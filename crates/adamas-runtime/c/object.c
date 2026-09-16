/* Заголовок, аллокация, счётчик ссылок, переиспользование блока.
 *
 * Договор описан в `adamas.h`; здесь только то, что видно из реализации.
 */

#include "adamas.h"

#include <stdio.h>
#include <stdlib.h>

/* Счётчики блоков: ряд у каждого потока, сумма по требованию.
 *
 * Правка трека I волны 2 Фазы 7, и форма её выбрана **замером**. Прежние
 * счётчики были беззнаковыми и `_Thread_local`, а на пути освобождения стояла
 * проверка «выдавал ли рантайм этот блок» - `blocks_live == 0`. С первым же
 * разделяемым значением она ломается: блок, выданный одним потоком и
 * освобождённый другим, вычитается не из того ряда, и проверка обрывает верную
 * программу. Свидетель «ноль живых», на котором стоит весь корпус, тоже
 * перестаёт значить что-либо.
 *
 * *Общий атомарный ряд отвергнут по цене, и цена мерена.* 20 млн пар
 * `alloc`+`drop`, `-O2`, медиана пяти прогонов: **0.209 с** без счётчиков
 * вовсе, **0.212 с** прежними потоко-локальными (то есть внутри разброса -
 * прежний комментарий про «`malloc` дороже их на порядки» замером подтверждён),
 * **0.298 с** с парой `__atomic_fetch_add`/`fetch_sub` на общий счётчик,
 * **0.234 с** с реестром. Общий ряд стоит **+41%** к пути аллокации за
 * диагностику, у которой не было ни одного свидетеля: обрыв «не выдавал» не
 * проверяется ни одним тестом дерева.
 *
 * Взят реестр (+11%): ряд по-прежнему у каждого потока свой, счёт в нём
 * **знаковый** - освободивший чужой блок уходит в минус, и это законно, - а
 * узлы рядов связаны в общий список. Сумма считается на требование
 * (`adamas_stat_live_everywhere`), то есть один раз в конце прогона, и там же
 * проверяется отрицательность: она и значит «освобождён блок, которого рантайм
 * не выдавал». Цена на горячем пути - ноль атомарных операций; остаток
 * одиннадцати процентов есть проверка «завёл ли этот поток свой ряд».
 *
 * Обнуление (`adamas_stat_reset`) остаётся локальным: тесты рантайма идут
 * потоками одного процесса, и общий ряд они обнуляли бы друг у друга
 * (измерено: 2 из 46 падают обрывом). */
typedef struct adamas_counters {
    struct adamas_counters *next;
    ptrdiff_t allocated;
    ptrdiff_t live;
} adamas_counters;

static adamas_counters *registry = NULL;
static _Thread_local adamas_counters *mine = NULL;

/* Заводит ряд этого потока и вносит его в реестр.
 *
 * Не освобождается намеренно: узел читает сумма, а она вправе быть позвана
 * после того, как поток договорил. Блоков это стоит по одному на поток, и
 * выданы они `calloc`'ом мимо собственного учёта - иначе учёт считал бы себя.
 *
 * `noinline` здесь **несущий**, а не косметический, и это измерено. Путь этот
 * холодный - по разу на поток, - но инлайнер видит его наравне с горячим и
 * считает `adamas_block_free` слишком большой; следом перестаёт инлайниться
 * `adamas_drop`, и сквозной конвейер (`llvm-link` с рантаймом) теряет весь
 * свой смысл: вызовов после `-O2` стало **25 против 22**, то есть больше, чем
 * без рантайма вовсе (`tests/llvm.rs`,
 * `the_runtime_in_bitcode_lets_the_optimiser_see_through_it`). */
__attribute__((noinline)) static adamas_counters *enlist(void) {
    adamas_counters *made = (adamas_counters *)calloc(1, sizeof(adamas_counters));
    adamas_counters *head;
    if (made == NULL) {
        adamas_fail("куча исчерпана");
    }
    head = __atomic_load_n(&registry, __ATOMIC_RELAXED);
    do {
        made->next = head;
    } while (!__atomic_compare_exchange_n(&registry, &head, made, 0, __ATOMIC_ACQ_REL,
                                          __ATOMIC_RELAXED));
    mine = made;
    return made;
}

/* Ряд этого потока; заводится на первой же аллокации. */
static adamas_counters *ours(void) {
    adamas_counters *at = mine;
    return at != NULL ? at : enlist();
}

_Noreturn void adamas_fail(const char *message) {
    fprintf(stderr, "adamas: %s\n", message);
    abort();
}

void *adamas_block_alloc(size_t size) {
    void *block = malloc(size);
    adamas_counters *counters;
    if (block == NULL) {
        adamas_fail("куча исчерпана");
    }
    counters = ours();
    counters->allocated += 1;
    counters->live += 1;
    return block;
}

void adamas_block_free(void *block) {
    if (block == NULL) {
        return;
    }
    /* Ряд уходит в минус у того, кто освободил чужой блок, - и это не ошибка, а
     * ровно та величина, которой он перестал быть: «выдано этим потоком» и
     * «живо у этого потока» сходятся, только пока блоки не ездят. Ловит
     * лишнее освобождение сумма, а не эта строка. */
    ours()->live -= 1;
    free(block);
}

adamas_header *adamas_header_of(void *block) {
    /* Заголовок - первый член у объекта, замыкания, кадра, сегмента и вектора.
     * Обращение идёт через `void *`, а не приведением одной структуры к другой:
     * так тип, через который читают байты, совпадает с типом самого члена. */
    return (adamas_header *)block;
}

size_t adamas_stat_allocated(void) {
    return (size_t)ours()->allocated;
}

size_t adamas_stat_live(void) {
    return (size_t)ours()->live;
}

size_t adamas_stat_live_everywhere(void) {
    ptrdiff_t total = 0;
    /* `acquire` парен `acq_rel` у вставки: узлы, положенные другими потоками,
     * обязаны быть видны целиком, а не одним указателем. */
    for (const adamas_counters *at = __atomic_load_n(&registry, __ATOMIC_ACQUIRE); at != NULL;
         at = at->next) {
        total += at->live;
    }
    if (total < 0) {
        /* Отрицательная сумма и значит «освобождён блок, которого рантайм не
         * выдавал». Прежде это ловилось на самом освобождении; проверка стоила
         * атомарной пары на каждый блок (+41% к пути аллокации, мерено) и не
         * имела ни одного свидетеля. */
        adamas_fail("освобождён блок, которого рантайм не выдавал");
    }
    return (size_t)total;
}

void adamas_stat_reset(void) {
    adamas_counters *counters = ours();
    counters->allocated = 0;
    counters->live = 0;
}

/* ------------------------------------------------------------------ */
/* Непосредственные значения                                           */
/* ------------------------------------------------------------------ */

int adamas_is_imm(adamas_value value) {
    return ((uintptr_t)value & 1u) != 0u;
}

adamas_value adamas_imm(intptr_t number) {
    return (adamas_value)((((uintptr_t)number) << 1) | 1u);
}

intptr_t adamas_imm_get(adamas_value value) {
    /* Сдвиг знакового вправо арифметический у gcc, clang и msvc; на цели, где
     * это не так, здесь понадобится деление. */
    return ((intptr_t)value) >> 1;
}

adamas_value adamas_con0(uint16_t tag) {
    return adamas_imm((intptr_t)tag);
}

adamas_value adamas_unit(void) {
    return adamas_con0(0);
}

/* ------------------------------------------------------------------ */
/* Объекты                                                             */
/* ------------------------------------------------------------------ */

adamas_value adamas_alloc(uint16_t tag, size_t fields) {
    adamas_value object =
        (adamas_value)adamas_block_alloc(sizeof(adamas_header) + fields * sizeof(adamas_value));
    adamas_header *header = adamas_header_of(object);
    header->rc = 0;
    header->tag = tag;
    header->flags = 0;
    return object;
}

void adamas_free(adamas_value value) {
    if (adamas_is_imm(value)) {
        return;
    }
    adamas_block_free(value);
}

uint16_t adamas_tag(adamas_value value) {
    /* Одна функция на оба представления - ради этого нульарный конструктор и
     * сделан непосредственным: разбор не спрашивает, объект перед ним или нет. */
    if (adamas_is_imm(value)) {
        return (uint16_t)adamas_imm_get(value);
    }
    return adamas_header_of(value)->tag;
}

/* ------------------------------------------------------------------ */
/* Счётчик: локальный режим и разделяемый                              */
/* ------------------------------------------------------------------ */

/* Разделяемый ли объект: `ADAMAS_FLAG_SHARED` в заголовке (§5.1).
 *
 * Флаг читается **неатомарно**, и это не недосмотр. Ставит его
 * `adamas_share` до того, как значение становится видно второму потоку, а
 * `pthread_create` (и всякая иная передача владения) даёт ребро
 * happens-before: гонки чтения с той записью не бывает по построению. Обратное
 * - промоушен уже разделённого значения - и есть та ошибка, ради которой
 * промоушен стоит на границе `spawn`, а не где придётся (§5.2). */
static int shared(const adamas_header *header) {
    return (header->flags & ADAMAS_FLAG_SHARED) != 0;
}

/* Промоушен транзитивно достижимого (§5.2).
 *
 * Форма выбрана симметрией с `adamas_drop`, и симметрия эта не косметическая:
 * обход детей рантайму **неоткуда взять** - числа полей в заголовке нет, сорт
 * слота (боксированный против плоского, §4.11) тем более, - а понижение и то и
 * другое знает и уже порождает ровно такой обход для дропа (`release.c`).
 * Поэтому здесь то же разделение труда: рантайм держит пометку, остановку и
 * рекурсию, вызывающий даёт `children`.
 *
 * Пометка ставится **до** обхода: иначе цикл в графе не заканчивался бы, а
 * общий подграф обходился бы по разу на каждый путь к нему. */
void adamas_share(adamas_value value, adamas_promote children) {
    adamas_header *header;
    if (adamas_is_imm(value)) {
        return;
    }
    header = adamas_header_of(value);
    if (shared(header)) {
        return;
    }
    header->flags |= ADAMAS_FLAG_SHARED;
    if (children != NULL) {
        children(value);
    }
}

int adamas_is_shared(adamas_value value) {
    if (adamas_is_imm(value)) {
        return 0;
    }
    return shared(adamas_header_of(value));
}

uint32_t adamas_rc(adamas_value value) {
    if (adamas_is_imm(value)) {
        return 0;
    }
    adamas_header *header = adamas_header_of(value);
    if (shared(header)) {
        return __atomic_load_n(&header->rc, __ATOMIC_ACQUIRE);
    }
    return header->rc;
}

adamas_value adamas_dup(adamas_value value) {
    if (adamas_is_imm(value)) {
        return value;
    }
    /* Переполнение 32-битного счётчика не обрабатывается: 2^32 лишних ссылок на
     * один объект - не тот режим, который эта стадия обслуживает. */
    adamas_header *header = adamas_header_of(value);
    if (shared(header)) {
        /* `relaxed` довольно: взятие ссылки ничего не упорядочивает - у того,
         * кто дупает, ссылка уже есть, значит объект уже виден ему целиком.
         * Та же нота, что у `Arc::clone` в Rust и у `shared_ptr` в libstdc++. */
        __atomic_fetch_add(&header->rc, 1u, __ATOMIC_RELAXED);
        return value;
    }
    header->rc += 1;
    return value;
}

int adamas_is_unique(adamas_value value) {
    if (adamas_is_imm(value)) {
        return 0;
    }
    adamas_header *header = adamas_header_of(value);
    if (shared(header)) {
        /* `acquire`: ответ «уникален» есть право переписать слоты на месте
         * (FBIP, §5.1), и переписывающий обязан увидеть всё, что писал в них
         * прежний владелец. */
        return __atomic_load_n(&header->rc, __ATOMIC_ACQUIRE) == 0;
    }
    return header->rc == 0;
}

/* Отдать ссылку: истина - эта была последней.
 *
 * Один обмен, и решение по **старому** значению. Читать счётчик и вычитать
 * следом нельзя: два потока, увидевшие `1`, оба вычли бы из единицы, и один
 * получил бы ноль, а второй - переполнение вниз. Счётчик считает **лишние**
 * ссылки, поэтому последним оказывается тот, кому обмен отдал ноль; уход
 * счётчика в `0xFFFFFFFF` при этом безвреден - блок сразу умирает, и читать
 * его больше некому.
 *
 * `acq_rel`: `release` - чтобы записи уходящего были видны тому, кто будет
 * освобождать, `acquire` - чтобы освобождающий увидел записи всех ушедших. */
static int released(adamas_header *header) {
    if (shared(header)) {
        return __atomic_fetch_sub(&header->rc, 1u, __ATOMIC_ACQ_REL) == 0;
    }
    if (header->rc == 0) {
        return 1;
    }
    header->rc -= 1;
    return 0;
}

void adamas_drop(adamas_value value, adamas_release release) {
    if (adamas_is_imm(value)) {
        return;
    }
    if (!released(adamas_header_of(value))) {
        return;
    }
    if (release != NULL) {
        release(value);
    }
    adamas_block_free(value);
}

adamas_value adamas_drop_reuse(adamas_value value, adamas_release release) {
    if (adamas_is_imm(value)) {
        return NULL;
    }
    if (!released(adamas_header_of(value))) {
        return NULL;
    }
    if (release != NULL) {
        release(value);
    }
    return value;
}

adamas_value adamas_reuse(adamas_value block, uint16_t tag, size_t fields) {
    if (block == NULL) {
        return adamas_alloc(tag, fields);
    }
    /* Размер не проверяется: reuse срабатывает только при совпадении формы
     * конструкторов (§5.1), и это условие держит вставка Perceus.
     *
     * Флаг разделяемости при этом **снимается** вместе с прочими, и это верно:
     * блок пришёл из `adamas_drop_reuse`, то есть отдал последнюю ссылку, -
     * второго владельца у него нет, и новый постоялец локален, пока его снова
     * не разделят. */
    (void)fields;
    adamas_header *header = adamas_header_of(block);
    header->rc = 0;
    header->tag = tag;
    header->flags = 0;
    return block;
}

adamas_value adamas_field(adamas_value value, size_t index) {
    return value->fields[index];
}

void adamas_set_field(adamas_value value, size_t index, adamas_value field) {
    value->fields[index] = field;
}

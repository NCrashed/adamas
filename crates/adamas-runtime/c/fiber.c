/* Питомник и файберы: несколько вычислений под одним питомником (§5.2).
 *
 * Модель **повторена за машиной** (`adamas-interp/src/fiber.rs`), а не
 * придумана заново: там она отревьюирована дважды - ревью 2026-09-07 и
 * закрытие §10 вопроса 144, - и второй записи модели не заводится. Совпадать
 * обязаны круг, порядок очереди и то, что отмена делает с сегментом;
 * представление своё, потому что стек здесь односвязная цепочка кадров, а не
 * `Vec` звеньев.
 *
 * Файбер есть **сегмент того же стека**. Уступка снимает его от кадра
 * питомника до вершины (`adamas_kont_cut`), пробуждение возвращает на место
 * (`adamas_kont_restore`); копий не делается ни одной. Резумпция файбера
 * аффинна по построению - он либо в очереди, либо бежит, - поэтому ресурс
 * внутри задачи законен, в отличие от области видимости `handleMulti` (§3.4).
 *
 * # Кто кого держит
 *
 * Круг живёт, пока на него есть ссылки: по одной у каждого кадра `NURSERY` и по
 * одной у каждого невыразимого имени файбера, плюс одна «круг открыт», которую
 * отпускает закрытие. Таблицы номеров нет вовсе, и без неё круг не переживает
 * своих кадров: у машины запись в `Vec` остаётся навсегда, потому что номер её
 * несёт кадр, - здесь кадр несёт сам указатель.
 *
 * # Почему следующий файбер запускается кадром, а не вызовом
 *
 * Ещё не начатый файбер надо применить к единице, и прямой `adamas_apply`
 * прямо отсюда вложил бы C-кадр на каждое переключение: уступка → старт →
 * уступка → старт. Вместо этого ставится кадр `PLAIN` с кодом старта, и его
 * зовёт трамплин - цикл `adamas_kont_run` остаётся плоским независимо от числа
 * порождённых.
 *
 * # Настоящие потоки
 *
 * Круг умеет идти на нескольких потоках, и включается это переменной окружения
 * `ADAMAS_THREADS` (пусто либо `1` - круг однопоточный, как был). Модель
 * переезд допускает **по построению**: цепочка кадров лежит в куче, а не на
 * C-стеке, и `adamas_kont_run` берёт ручку параметром, - в `adamas_fiber`
 * адресов C-стека нет вовсе.
 *
 * Работы это потребовало трёх:
 *
 * 1. *Замок вокруг круга.* Очередь, ждущие, готовые, счётчик номеров и счётчик
 *    ссылок правятся под `lock`. Однопоточный круг замка **не берёт**: ветвь
 *    по `hands` стоит перед ним, и вся многопоточная половина вынесена за
 *    `noinline` - тем же ходом, каким вопрос 175 вынес атомарные половины
 *    счётчика, и по той же причине (у LLVM `PartialInlinerPass` в `-O2`
 *    выключен, делить точку входа обязан источник).
 *
 * 2. *Свой `adamas_kont` на воркера.* Воркер заводит пустой стек и ставит на
 *    него файбер целиком - вместе с его кадром `NURSERY`. Отсюда же следует
 *    граница: **под кадром питомника у воркера пусто**, поэтому обрыв,
 *    уходящий наружу круга, из мигрировавшего файбера не выражается вовсе, и
 *    рантайм говорит об этом вслух, а не портит стек.
 *
 * 3. *Номер бегущего переехал в кадр.* Прежде `running`/`rooted` лежали в
 *    круге - одно поле на всех, - и с двумя воркерами это гонка по
 *    построению. Теперь их несёт сам кадр `NURSERY`, то есть они едут вместе с
 *    файбером; заодно это чинит вложенные круги, где поле круга затиралось.
 *
 * Ответ корневого файбера **мигрирует**: договорить он вправе на любом
 * воркере, а отдать его обязан тот стек, на котором стоял `withNursery`, -
 * `nursery->home`. Круг поэтому закрывает только хозяин; воркер, оставшийся
 * без работы, возвращается в свой цикл.
 *
 * # Что многопоточным кругом не покрыто, и названо, а не обойдено
 *
 * - *Обрыв наружу питомника из мигрировавшего файбера* - рантайм отказывает
 *   вслух (см. `adamas_nursery_abandoned`), свидетель в
 *   `adamas-codegen/tests/threads.rs`.
 * - *Отмена файбера, бегущего на чужом воркере*, молча не происходит: точки
 *   прерывания у бегущего нет, а §5.2 её и не называет - отмена приходит в
 *   suspend-точке (см. `adamas_nursery_cancel`).
 * - *Вложенные круги* под потоками свидетеля не имеют: внутренний нанимает
 *   своих воркеров поверх внешних, и числа потоков перемножаются. Программы,
 *   различающей это, в корпусе нет - обе вложенные кончаются следом либо
 *   обрывом, а то и другое под потоками не определено.
 * - *Порядок файберов* перестаёт быть определённым, и всякая программа со
 *   следом отвечает иначе. Договор трёх вычислителей поэтому проверяется на
 *   той корпусной, чей ответ от порядка не зависит.
 */

#include "adamas.h"

#include <pthread.h>
#include <stdlib.h>

/* Среда кадра `NURSERY`: круг, номер файбера, корневой ли он.
 *
 * Все три несчётные - заголовков у них нет вовсе. Номер и признак лежат здесь,
 * а не в круге, потому что кадр едет вместе с файбером (см. шапку). */
#define ADAMAS_NURSERY_SLOTS 3

/* Приостановленный файбер очереди. */
typedef struct adamas_fiber {
    struct adamas_fiber *next;
    /** Номер: им задача названа в значении `Task`. */
    uint32_t id;
    /** Кого ждёт. Значимо только в списке ждущих. */
    uint32_t awaited;
    /** Корневой ли: его значением питомник и отвечает. */
    int root;
    /** Ещё не начатый: тело запустит питомник. */
    int fresh;
    /** Fresh: приостановленное вычисление. */
    adamas_value body;
    /** Parked: сегмент от кадра питомника до вершины. */
    adamas_segment *segment;
    /**
     * Чем возобновление ему ответит.
     *
     * Хранится **при файбере**, а не берётся у пробуждающего: уступка отвечает
     * единицей, а ожидание - значением дождавшейся задачи, и различить их в
     * момент пробуждения нечем (ревью 2026-09-07 у машины).
     */
    adamas_value answer;
} adamas_fiber;

/* Ответ договорившего файбера. */
typedef struct adamas_done {
    struct adamas_done *next;
    uint32_t id;
    adamas_value value;
} adamas_done;

struct adamas_nursery {
    /** Готовые к исполнению, в порядке круга: голова и хвост. */
    adamas_fiber *ready;
    adamas_fiber *last;
    /**
     * Ждущие чужого ответа. Круг их не касается, пока ожидаемый не договорил:
     * пустая очередь при непустом этом списке и есть взаимная блокировка - её
     * видно по построению, а не по зависанию.
     */
    adamas_fiber *blocked;
    /** Ответы договоривших. */
    adamas_done *done;
    /** Вектор на месте `withNursery`: под ним идёт всякий файбер круга. */
    adamas_evidence *base;
    /** Дроп чужих значений: порождает его понижение по типу. */
    adamas_release release;
    /**
     * Промоушен чужих значений: тот же обход, что у дропа, но помечающий.
     *
     * Зовётся только многопоточным кругом (§5.2): пока круг однопоточен,
     * промоушен на границе `spawn` есть чистый налог - атомарный режим стоит
     * 4.2 раза на паре `dup`/`drop`. `NULL` законен: понижение вправе его не
     * дать, и тогда многопоточный круг отказывается стартовать вслух.
     */
    adamas_promote promote;
    /** Ответ корневого файбера, когда он договорил. */
    adamas_value result;
    /** Следующий свободный номер файбера. */
    uint32_t next;
    /** Ссылок сверх одной: кадры `NURSERY` и имена файберов. */
    uint32_t refs;
    /** Есть ли ответ корневого. */
    int answered;
    /** Отпущена ли ссылка «круг открыт». */
    int closed;

    /* --- многопоточный круг (§5.2); при `hands == 0` ничего из этого не
     * трогается вовсе --- */

    /** Замок вокруг всего перечисленного выше. */
    pthread_mutex_t lock;
    /** «Работа появилась» либо «круг договорил». */
    pthread_cond_t wake;
    /** Стек, на котором стоял `withNursery`: только он отдаёт ответ круга. */
    adamas_kont *home;
    /** Поток хозяина: обрыв круга законен только на нём. */
    pthread_t owner;
    /** Воркеры. */
    pthread_t *crew;
    /** Сколько их. `0` - круг однопоточный, и весь замок обходится стороной. */
    uint32_t hands;
    /** Файберов бежит прямо сейчас, считая хозяйского. */
    uint32_t busy;
    /** Воркерам расходиться: круг договорил либо брошен. */
    int shut;
    /** Собраны ли воркеры обратно. */
    int joined;
};

/* Невыразимое имя файбера: написать его автор не может, а `await`, отмена и
 * печать читают из него круг и номер. Стоит оно **аргументом объявленного
 * конструктора**, поэтому `drop (MkTask n)` разбирается как обычно. */
typedef struct adamas_fiber_name {
    adamas_header header;
    adamas_nursery *home;
    uint32_t id;
} adamas_fiber_name;

static adamas_value nursery_step(adamas_kont *kont, adamas_nursery *nursery);

/* ------------------------------------------------------------------ */
/* Замок круга                                                         */
/* ------------------------------------------------------------------ */

/* Половина, до которой однопоточный круг не доходит.
 *
 * Разделение сделано **в источнике**, а не отдано компилятору: правило трека B
 * волны 3 Фазы 7 - у gcc частичный инлайнинг делит точку входа сам, у LLVM
 * `PartialInlinerPass` в `-O2` выключен по умолчанию, и на колонном ядре это
 * стоило 72%. `cold` метит место вызова маловероятным, и быстрый путь -
 * однопоточный круг - остаётся прямым. */
#define ADAMAS_CROWDED __attribute__((noinline, cold))

ADAMAS_CROWDED static void nursery_lock(adamas_nursery *nursery) {
    if (pthread_mutex_lock(&nursery->lock) != 0) {
        adamas_fail("замок круга не взялся");
    }
}

ADAMAS_CROWDED static void nursery_unlock(adamas_nursery *nursery) {
    if (pthread_mutex_unlock(&nursery->lock) != 0) {
        adamas_fail("замок круга не отпустился");
    }
}

/* Замок берётся только многопоточным кругом; ветвь и есть весь быстрый путь. */
static void nursery_hold(adamas_nursery *nursery) {
    if (nursery->hands != 0) {
        nursery_lock(nursery);
    }
}

static void nursery_free(adamas_nursery *nursery) {
    if (nursery->hands != 0) {
        nursery_unlock(nursery);
    }
}

ADAMAS_CROWDED static void nursery_broadcast(adamas_nursery *nursery) {
    pthread_cond_broadcast(&nursery->wake);
}

/* Работа появилась: кто ждал - пусть возьмёт. Зовётся под замком. */
static void nursery_wakened(adamas_nursery *nursery) {
    if (nursery->hands != 0) {
        nursery_broadcast(nursery);
    }
}

/* ------------------------------------------------------------------ */
/* Владение кругом                                                     */
/* ------------------------------------------------------------------ */

/* Круг разобран: замок и переменная условия уничтожаются тут, а не раньше.
 * Воркеры к этому времени собраны - хозяин делает это до `nursery_close`. */
ADAMAS_CROWDED static void nursery_dismantle(adamas_nursery *nursery) {
    free(nursery->crew);
    nursery->crew = NULL;
    pthread_cond_destroy(&nursery->wake);
    pthread_mutex_destroy(&nursery->lock);
}

static void nursery_unref(adamas_nursery *nursery) {
    uint32_t hands = nursery->hands;
    nursery_hold(nursery);
    if (nursery->refs == 0) {
        nursery_free(nursery);
        if (hands != 0) {
            nursery_dismantle(nursery);
        }
        adamas_evidence_drop(nursery->base);
        adamas_block_free(nursery);
        return;
    }
    nursery->refs -= 1;
    nursery_free(nursery);
}

/* Круг договорил: содержимое больше не нужно, ссылка «открыт» отпускается.
 * Идемпотентно - раскрутка добирается сюда с каждого кадра `NURSERY`. */
static void nursery_close(adamas_nursery *nursery) {
    int already;
    nursery_hold(nursery);
    already = nursery->closed;
    nursery->closed = 1;
    nursery_free(nursery);
    if (already) {
        return;
    }
    nursery_unref(nursery);
}

/* Дроп среды кадра питомника: сам круг лежит в нулевом слоте несчётным. */
static void nursery_frame_release(adamas_frame *frame, adamas_kont *kont) {
    (void)kont;
    nursery_unref((adamas_nursery *)(void *)adamas_frame_env(frame)[0]);
}

static adamas_nursery *nursery_of(adamas_frame *frame) {
    if (adamas_frame_fields(frame) < ADAMAS_NURSERY_SLOTS) {
        adamas_fail("кадр питомника без круга в среде");
    }
    return (adamas_nursery *)(void *)adamas_frame_env(frame)[0];
}

/* Номер файбера, которому этот кадр принадлежит.
 *
 * Лежит он **в кадре**, а не в круге, и это не вкус: кадр едет вместе с
 * файбером, а поле круга было бы одно на всех воркеров - гонка по построению.
 * Вложенные круги тем же чинятся: у каждого кадра свой номер. */
static uint32_t fiber_id_of(adamas_frame *frame) {
    return (uint32_t)(uintptr_t)(void *)adamas_frame_env(frame)[1];
}

static int fiber_root_of(adamas_frame *frame) {
    return (int)(uintptr_t)(void *)adamas_frame_env(frame)[2];
}

/* ------------------------------------------------------------------ */
/* Очередь, ждущие, готовые                                            */
/* ------------------------------------------------------------------ */

static adamas_fiber *fiber_alloc(uint32_t id, int root) {
    adamas_fiber *fiber = (adamas_fiber *)adamas_block_alloc(sizeof(adamas_fiber));
    fiber->next = NULL;
    fiber->id = id;
    fiber->awaited = 0;
    fiber->root = root;
    fiber->fresh = 0;
    fiber->body = adamas_unit();
    fiber->segment = NULL;
    fiber->answer = adamas_unit();
    return fiber;
}

static void queue_push(adamas_nursery *nursery, adamas_fiber *fiber) {
    fiber->next = NULL;
    if (nursery->last == NULL) {
        nursery->ready = fiber;
    } else {
        nursery->last->next = fiber;
    }
    nursery->last = fiber;
}

static adamas_fiber *queue_pop(adamas_nursery *nursery) {
    adamas_fiber *fiber = nursery->ready;
    if (fiber == NULL) {
        return NULL;
    }
    nursery->ready = fiber->next;
    if (nursery->ready == NULL) {
        nursery->last = NULL;
    }
    fiber->next = NULL;
    return fiber;
}

/* Хвост очереди. Обход, а не второй указатель назад: зовётся это только
 * раскруткой брошенного круга, где очередь и без того вычерпывается целиком. */
static adamas_fiber *queue_pop_back(adamas_nursery *nursery) {
    adamas_fiber *fiber = nursery->ready;
    adamas_fiber *before = NULL;
    if (fiber == NULL) {
        return NULL;
    }
    while (fiber->next != NULL) {
        before = fiber;
        fiber = fiber->next;
    }
    if (before == NULL) {
        nursery->ready = NULL;
        nursery->last = NULL;
    } else {
        before->next = NULL;
        nursery->last = before;
    }
    return fiber;
}

/* Снимает файбер с круга по номеру: из очереди либо из ждущих. */
static adamas_fiber *fiber_take(adamas_nursery *nursery, uint32_t id) {
    adamas_fiber *before = NULL;
    adamas_fiber *fiber = nursery->ready;
    while (fiber != NULL) {
        if (fiber->id == id) {
            if (before == NULL) {
                nursery->ready = fiber->next;
            } else {
                before->next = fiber->next;
            }
            if (nursery->last == fiber) {
                nursery->last = before;
            }
            fiber->next = NULL;
            return fiber;
        }
        before = fiber;
        fiber = fiber->next;
    }
    before = NULL;
    fiber = nursery->blocked;
    while (fiber != NULL) {
        if (fiber->id == id) {
            if (before == NULL) {
                nursery->blocked = fiber->next;
            } else {
                before->next = fiber->next;
            }
            fiber->next = NULL;
            return fiber;
        }
        before = fiber;
        fiber = fiber->next;
    }
    return NULL;
}

static void fiber_free(adamas_nursery *nursery, adamas_fiber *fiber) {
    adamas_drop(fiber->body, nursery->release);
    adamas_drop(fiber->answer, nursery->release);
    adamas_block_free(fiber);
}

static void done_push(adamas_nursery *nursery, uint32_t id, adamas_value value) {
    adamas_done *entry = (adamas_done *)adamas_block_alloc(sizeof(adamas_done));
    entry->next = nursery->done;
    entry->id = id;
    entry->value = value;
    nursery->done = entry;
}

/* Ответ договорившего **лишней ссылкой**: запись остаётся на месте.
 *
 * Остаётся потому, что `await` его только читает - у машины там `find` с
 * `Rc::clone`, а не изъятие (`Machine::awaiting`). Забери запись, и второе
 * ожидание той же задачи ушло бы в круг ждать никого: с `data Task` кратность
 * значения ω, и написать два `await` подряд ничто не мешает. Освобождает
 * записи закрытие круга. */
static adamas_value done_read(adamas_nursery *nursery, uint32_t id, int *found) {
    adamas_done *entry = nursery->done;
    *found = 0;
    while (entry != NULL) {
        if (entry->id == id) {
            *found = 1;
            return adamas_dup(entry->value);
        }
        entry = entry->next;
    }
    return adamas_unit();
}

/* Ответ договорившего владением; запись снимается. `found` - нашлась ли она. */
static adamas_value done_take(adamas_nursery *nursery, uint32_t id, int *found) {
    adamas_done *before = NULL;
    adamas_done *entry = nursery->done;
    *found = 0;
    while (entry != NULL) {
        if (entry->id == id) {
            adamas_value value = entry->value;
            if (before == NULL) {
                nursery->done = entry->next;
            } else {
                before->next = entry->next;
            }
            adamas_block_free(entry);
            *found = 1;
            return value;
        }
        before = entry;
        entry = entry->next;
    }
    return adamas_unit();
}

static void done_clear(adamas_nursery *nursery) {
    while (nursery->done != NULL) {
        adamas_done *entry = nursery->done;
        nursery->done = entry->next;
        adamas_drop(entry->value, nursery->release);
        adamas_block_free(entry);
    }
}

/* ------------------------------------------------------------------ */
/* Невыразимое имя файбера                                             */
/* ------------------------------------------------------------------ */

static adamas_value fiber_name(adamas_nursery *nursery, uint32_t id) {
    adamas_fiber_name *name =
        (adamas_fiber_name *)adamas_block_alloc(sizeof(adamas_fiber_name));
    adamas_header *header = adamas_header_of(name);
    header->rc = 0;
    header->tag = ADAMAS_TAG_FIBER;
    header->flags = 0;
    name->home = nursery;
    name->id = id;
    nursery->refs += 1;
    return (adamas_value)(void *)name;
}

void adamas_fiber_name_release(adamas_value value) {
    nursery_unref(((adamas_fiber_name *)(void *)value)->home);
}

/* Имя файбера в поле `at` значения задачи. `NULL` - собрано не питомником. */
static adamas_fiber_name *named(adamas_value task, uint32_t at) {
    adamas_value field;
    if (adamas_is_imm(task)) {
        return NULL;
    }
    field = adamas_field(task, at);
    if (adamas_is_imm(field) || adamas_tag(field) != ADAMAS_TAG_FIBER) {
        return NULL;
    }
    return (adamas_fiber_name *)(void *)field;
}

/* ------------------------------------------------------------------ */
/* Поиск круга по вектору evidence                                     */
/* ------------------------------------------------------------------ */

int adamas_nursery_serves(const adamas_evidence *evidence, uint32_t label) {
    size_t index = adamas_evidence_count(evidence);
    while (index > 0) {
        uint32_t at;
        index -= 1;
        at = adamas_evidence_label_at(evidence, index);
        if (at == ADAMAS_LABEL_NURSERY) {
            /* Подавленная запись круга не считается вовсе: кадра её на этом
             * стеке нет. Поиск идёт наружу - к тому кругу, который жив. */
            if (!adamas_evidence_suppressed_at(evidence, index)) {
                return 1;
            }
            continue;
        }
        if (at == label) {
            /* Подавленная запись хендлера считается наравне с живой: у машины
             * `Kont::catching` отдаёт и `Handler`, и `Suppressing`. */
            return 0;
        }
    }
    return 0;
}

static adamas_frame *nursery_frame(const adamas_evidence *evidence) {
    size_t index = adamas_evidence_count(evidence);
    while (index > 0) {
        index -= 1;
        if (adamas_evidence_label_at(evidence, index) == ADAMAS_LABEL_NURSERY
            && !adamas_evidence_suppressed_at(evidence, index)) {
            return adamas_evidence_at(evidence, index);
        }
    }
    adamas_fail("операция питомника вне питомника (§5.2)");
}

/* ------------------------------------------------------------------ */
/* Запуск файбера                                                      */
/* ------------------------------------------------------------------ */

/* Код кадра старта: применяет тело к единице под вектором своего кадра. */
static adamas_value fiber_start(adamas_frame *frame, adamas_kont *kont, adamas_value incoming) {
    adamas_value *env = adamas_frame_env(frame);
    adamas_nursery *nursery = (adamas_nursery *)(void *)env[1];
    adamas_value body = env[0];
    adamas_value answer;
    adamas_drop(incoming, NULL);
    env[0] = adamas_unit();
    answer = adamas_apply(body, adamas_frame_evidence(frame), kont, adamas_unit());
    /* Тело потреблено: `adamas_apply` замыкание заимствует (`adamas.h`). */
    adamas_drop(body, nursery->release);
    return answer;
}

static void start_release(adamas_frame *frame, adamas_kont *kont) {
    adamas_value *env = adamas_frame_env(frame);
    (void)kont;
    adamas_drop(env[0], ((adamas_nursery *)(void *)env[1])->release);
}

/* Ставит кадр питомника и кадр старта над ним. Тело берётся владением. */
static adamas_value nursery_start(adamas_kont *kont, adamas_nursery *nursery, adamas_value body,
                                  uint32_t id, int root) {
    adamas_frame *frame =
        adamas_kont_push(kont, ADAMAS_MARK_NURSERY, 0, NULL, nursery_frame_release,
                         ADAMAS_NURSERY_SLOTS, 0, nursery->base);
    adamas_evidence *inner;
    adamas_frame *starter;
    adamas_value *env;
    adamas_frame_env(frame)[0] = (adamas_value)(void *)nursery;
    adamas_frame_env(frame)[1] = (adamas_value)(void *)(uintptr_t)id;
    adamas_frame_env(frame)[2] = (adamas_value)(void *)(uintptr_t)(unsigned)root;
    nursery_hold(nursery);
    nursery->refs += 1;
    nursery_free(nursery);
    /* Кадр свой у каждого файбера, и вектор его называет **этот** кадр:
     * возобновление ставит файбер обратно под свой круг, а не под чужой. */
    inner = adamas_evidence_extend(nursery->base, ADAMAS_LABEL_NURSERY, frame);
    /* Слот тела счётный, слот круга - нет: у круга заголовка не существует. */
    starter = adamas_kont_push(kont, ADAMAS_MARK_PLAIN, 0, fiber_start, start_release, 2, 1, inner);
    adamas_evidence_drop(inner);
    env = adamas_frame_env(starter);
    env[0] = body;
    env[1] = (adamas_value)(void *)nursery;
    return adamas_unit();
}

/* ------------------------------------------------------------------ */
/* Круг                                                                */
/* ------------------------------------------------------------------ */

/* Ставит снятый файбер на этот стек и отдаёт значение, которым он продолжится.
 *
 * Стек - **этот**, каким бы ни был тот, с которого файбер сняли: цепочка кадров
 * лежит в куче, и переезд её есть перекладывание одного указателя
 * (`adamas_kont_restore`). Ради этого свойства файбер и сделан сегментом кучи,
 * а не вторым C-стеком. */
static adamas_value fiber_install(adamas_kont *kont, adamas_nursery *nursery,
                                  adamas_fiber *fiber) {
    if (fiber->fresh) {
        adamas_value body = fiber->body;
        uint32_t id = fiber->id;
        int root = fiber->root;
        fiber->body = adamas_unit();
        fiber_free(nursery, fiber);
        return nursery_start(kont, nursery, body, id, root);
    }
    adamas_kont_restore(kont, fiber->segment);
    {
        adamas_value answer = fiber->answer;
        fiber->answer = adamas_unit();
        fiber->segment = NULL;
        fiber_free(nursery, fiber);
        return answer;
    }
}

/* Круг договорил: ответ корневого уходит вниз, готовые освобождаются. */
static adamas_value nursery_result(adamas_nursery *nursery) {
    adamas_value result;
    if (nursery->blocked != NULL) {
        /* Круг пуст, а ждущие есть - ждать им друг друга до конца времён.
         * Видно это по построению, а не по зависанию. */
        adamas_fail("взаимная блокировка файберов (§5.2)");
    }
    result = nursery->answered ? nursery->result : adamas_unit();
    nursery->answered = 0;
    nursery->result = adamas_unit();
    done_clear(nursery);
    nursery_close(nursery);
    return result;
}

/* Расходиться и собраться. Зовётся хозяином без замка. */
ADAMAS_CROWDED static void crew_join(adamas_nursery *nursery) {
    uint32_t at;
    nursery_lock(nursery);
    if (nursery->joined) {
        nursery_unlock(nursery);
        return;
    }
    nursery->joined = 1;
    nursery->shut = 1;
    pthread_cond_broadcast(&nursery->wake);
    nursery_unlock(nursery);
    for (at = 0; at < nursery->hands; at += 1) {
        pthread_join(nursery->crew[at], NULL);
    }
}

/* Шаг многопоточного круга. Замок берётся здесь и только здесь.
 *
 * Отдаёт файбер к постановке либо `NULL`. `over` - круг договорил, и это
 * значимо только хозяину: воркеру «работы нет» и «круг кончился» одинаковы, он
 * в обоих случаях возвращается в свой цикл. */
__attribute__((noinline)) static adamas_fiber *crowd_next(adamas_nursery *nursery, int mine,
                                                          int *over) {
    adamas_fiber *next;
    nursery_lock(nursery);
    nursery->busy -= 1;
    for (;;) {
        next = queue_pop(nursery);
        if (next != NULL) {
            nursery->busy += 1;
            break;
        }
        if (nursery->busy == 0 || nursery->shut) {
            /* Никто не бежит и очередь пуста: круг договорил (либо брошен).
             * Будит всех - хозяину пора отвечать, воркерам расходиться. */
            pthread_cond_broadcast(&nursery->wake);
            break;
        }
        if (!mine) {
            /* Воркеру ждать незачем: он вернётся в свой цикл и встанет там.
             * Хозяин же обязан достоять до ответа - под ним лежит стек
             * `withNursery`, и уйти ему некуда. */
            break;
        }
        pthread_cond_wait(&nursery->wake, &nursery->lock);
    }
    *over = next == NULL && nursery->busy == 0;
    nursery_unlock(nursery);
    return next;
}

/* Следующий файбер очереди либо ответ питомника, если её больше нет. */
static adamas_value nursery_step(adamas_kont *kont, adamas_nursery *nursery) {
    adamas_fiber *next;
    if (nursery->hands != 0) {
        int over = 0;
        int mine = kont == nursery->home;
        next = crowd_next(nursery, mine, &over);
        if (next != NULL) {
            return fiber_install(kont, nursery, next);
        }
        if (!mine) {
            /* Стек воркера пуст: значение уйдёт трамплину, тот вернётся в цикл
             * воркера, и файбер тот возьмёт уже оттуда. */
            return adamas_unit();
        }
        if (!over) {
            adamas_fail("хозяин круга остался без работы, а круг не договорил (§5.2)");
        }
        crew_join(nursery);
        return nursery_result(nursery);
    }
    next = queue_pop(nursery);
    if (next == NULL) {
        return nursery_result(nursery);
    }
    return fiber_install(kont, nursery, next);
}

/* Снимает бегущий файбер со стека и кладёт его сегмент при нём. */
static adamas_fiber *parked(adamas_frame *frame, adamas_segment *segment, adamas_value answer) {
    adamas_fiber *fiber = fiber_alloc(fiber_id_of(frame), fiber_root_of(frame));
    fiber->segment = segment;
    fiber->answer = answer;
    return fiber;
}

/* ------------------------------------------------------------------ */
/* Воркеры                                                             */
/* ------------------------------------------------------------------ */

/* Цикл воркера: взять файбер, докрутить его до уступки, взять следующий.
 *
 * Стек у воркера **свой** и начинается пустым. Файбер ставится на него целиком,
 * вместе со своим кадром `NURSERY`; когда он уступит, `nursery_step` оставит
 * стек пустым, трамплин вернётся сюда, и цикл пойдёт за следующим. */
static void *crew_hand(void *argument) {
    adamas_nursery *nursery = (adamas_nursery *)argument;
    adamas_kont kont;
    adamas_kont_init(&kont);
    for (;;) {
        adamas_fiber *fiber;
        nursery_lock(nursery);
        while (nursery->ready == NULL && !nursery->shut && nursery->busy != 0) {
            pthread_cond_wait(&nursery->wake, &nursery->lock);
        }
        fiber = nursery->ready == NULL ? NULL : queue_pop(nursery);
        if (fiber != NULL) {
            nursery->busy += 1;
        } else {
            /* Работы нет и не будет: либо круг договорил, либо его бросили. */
            pthread_cond_broadcast(&nursery->wake);
        }
        nursery_unlock(nursery);
        if (fiber == NULL) {
            return NULL;
        }
        /* Ответ трамплина - единица `nursery_step`: круг закрывает хозяин, и
         * значения круга сюда не приходит. Дроп стоит на случай, если придёт. */
        adamas_drop(adamas_kont_run(&kont, fiber_install(&kont, nursery, fiber)),
                    nursery->release);
    }
}

/* Сколько воркеров просит окружение. `0` - круг однопоточный, как был.
 *
 * Переменная, а не умолчание: круг под настоящими потоками **меняет
 * наблюдаемое** - порядок отметок задач больше не определён, - и включать это
 * молча значило бы сломать договор трёх вычислителей у всякой программы со
 * следом. */
static uint32_t crew_asked(void) {
    const char *asked = getenv("ADAMAS_THREADS");
    long many;
    char *end;
    if (asked == NULL || *asked == '\0') {
        return 0;
    }
    many = strtol(asked, &end, 10);
    if (*end != '\0' || many < 1) {
        adamas_fail("`ADAMAS_THREADS` - целое не меньше единицы");
    }
    if (many > 256) {
        many = 256;
    }
    /* Единица значит «круг как был»: хозяин крутит его сам, воркеров нет. */
    return (uint32_t)(many - 1);
}

/* Заводит воркеров. Зовётся хозяином сразу после постройки круга. */
ADAMAS_CROWDED static void crew_hire(adamas_nursery *nursery, uint32_t hands) {
    uint32_t at;
    if (nursery->promote == NULL) {
        /* Без обхода промоушена значение, уехавшее в чужой поток, считалось бы
         * неатомарно (§5.1). Молчать об этом нечем: гонка не видна ответом. */
        adamas_fail("многопоточный круг без обхода промоушена (§5.2)");
    }
    nursery->crew = (pthread_t *)calloc(hands, sizeof(pthread_t));
    if (nursery->crew == NULL) {
        adamas_fail("куча исчерпана");
    }
    /* `hands` ставится **до** запуска: воркер читает его у себя же. */
    nursery->hands = hands;
    for (at = 0; at < hands; at += 1) {
        if (pthread_create(&nursery->crew[at], NULL, crew_hand, nursery) != 0) {
            adamas_fail("поток круга не завёлся");
        }
    }
}

adamas_value adamas_nursery_begin(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_value body, adamas_release release,
                                  adamas_promote promote) {
    adamas_nursery *nursery = (adamas_nursery *)adamas_block_alloc(sizeof(adamas_nursery));
    uint32_t hands = crew_asked();
    adamas_value seed;
    nursery->ready = NULL;
    nursery->last = NULL;
    nursery->blocked = NULL;
    nursery->done = NULL;
    nursery->base = adamas_evidence_dup((adamas_evidence *)(uintptr_t)evidence);
    nursery->release = release;
    nursery->promote = promote;
    nursery->result = adamas_unit();
    nursery->next = 1;
    nursery->refs = 0;
    nursery->answered = 0;
    nursery->closed = 0;
    nursery->home = kont;
    nursery->owner = pthread_self();
    nursery->crew = NULL;
    nursery->hands = 0;
    nursery->busy = 1; /* корневой файбер ставится прямо сейчас */
    nursery->shut = 0;
    nursery->joined = 1; /* однопоточному кругу собирать некого */
    if (hands != 0) {
        if (pthread_mutex_init(&nursery->lock, NULL) != 0
            || pthread_cond_init(&nursery->wake, NULL) != 0) {
            adamas_fail("замок круга не собрался");
        }
        nursery->joined = 0;
        /* Вектор места `withNursery` называет **каждый** кадр питомника, а
         * кадры эти ставят и снимают разные воркеры: без пометки его счётчик
         * правился бы голым `+=` из нескольких потоков разом. Детей у вектора
         * нет, поэтому обход `NULL`. */
        if (nursery->base != NULL) {
            adamas_share((adamas_value)(void *)nursery->base, NULL);
        }
    }
    /* Корневой файбер ставится **до** найма: воркеры, увидев пустую очередь при
     * нулевом `busy`, разошлись бы, не начав. */
    seed = nursery_start(kont, nursery, body, 0, 1);
    if (hands != 0) {
        crew_hire(nursery, hands);
    }
    return seed;
}

adamas_value adamas_nursery_suspend(adamas_kont *kont, const adamas_evidence *evidence) {
    adamas_frame *frame = nursery_frame(evidence);
    adamas_nursery *nursery = nursery_of(frame);
    /* Сегмент включает сам кадр питомника - тем же приёмом, что у хендлера. */
    adamas_segment *segment = adamas_kont_cut(kont, frame);
    adamas_fiber *fiber = parked(frame, segment, adamas_unit());
    nursery_hold(nursery);
    queue_push(nursery, fiber);
    nursery_wakened(nursery);
    nursery_free(nursery);
    return nursery_step(kont, nursery);
}

adamas_value adamas_nursery_spawn(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_value body, uint32_t tag, uint32_t slots, uint32_t at) {
    adamas_frame *frame = nursery_frame(evidence);
    adamas_nursery *nursery = nursery_of(frame);
    adamas_fiber *fiber;
    adamas_value task;
    uint32_t id;
    uint32_t slot;
    (void)kont;
    /* **Место вызова промоушена** (§5.2, вопрос 174 закрыт без него).
     *
     * Тело уезжает в чужой поток целиком - вместе со всем, до чего из его
     * захвата доходит обход, - и с этой минуты его счётчик обязан быть
     * атомарным. Стоит это 4.2 раза на паре `dup`/`drop`, поэтому ставится оно
     * **по факту**, а не на всяком `spawn`: однопоточный круг ничего никуда не
     * передаёт, и платить за него было бы чистым налогом.
     *
     * Ветвь по `hands` и есть та проверка; в порождённом коде её нет вовсе. */
    if (nursery->hands != 0) {
        adamas_share(body, nursery->promote);
    }
    nursery_hold(nursery);
    id = nursery->next;
    nursery->next += 1;
    fiber = fiber_alloc(id, 0);
    fiber->fresh = 1;
    fiber->body = body;
    queue_push(nursery, fiber);
    nursery_wakened(nursery);
    if (tag == ADAMAS_NO_TASK) {
        nursery_free(nursery);
        return adamas_unit();
    }
    /* Имя файбера берёт ссылку на круг, и счётчик её - под тем же замком. */
    task = fiber_name(nursery, id);
    nursery_free(nursery);
    {
        adamas_value name = task;
        task = adamas_alloc((uint16_t)tag, slots);
        for (slot = 0; slot < slots; slot += 1) {
            adamas_set_field(task, slot, adamas_unit());
        }
        adamas_set_field(task, at, name);
    }
    return task;
}

/* Ожидание в многопоточном круге: чтение готовых и уход в ждущие - **одним**
 * держанием замка.
 *
 * Врозь их делать нельзя, и это не осторожность: между «ответа ещё нет» и
 * «встаю ждать» ожидаемый вправе договорить на чужом воркере, никого в списке
 * ждущих не найти, - и ждущий остался бы ждать навсегда. Поэтому сегмент
 * режется **до** замка, а если ответ всё-таки нашёлся, кладётся обратно:
 * разрез с возвратом есть перекладывание двух указателей. */
__attribute__((noinline)) static adamas_value await_crowded(adamas_kont *kont,
                                                            adamas_nursery *nursery,
                                                            adamas_frame *frame, uint32_t awaited) {
    adamas_segment *segment = adamas_kont_cut(kont, frame);
    adamas_fiber *waiting;
    adamas_value ready;
    int found;
    nursery_lock(nursery);
    ready = done_read(nursery, awaited, &found);
    if (found) {
        nursery_unlock(nursery);
        adamas_kont_restore(kont, segment);
        return ready;
    }
    waiting = parked(frame, segment, adamas_unit());
    waiting->awaited = awaited;
    waiting->next = nursery->blocked;
    nursery->blocked = waiting;
    nursery_unlock(nursery);
    return nursery_step(kont, nursery);
}

adamas_value adamas_nursery_await(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_value task, uint32_t at) {
    adamas_frame *frame = nursery_frame(evidence);
    adamas_nursery *nursery = nursery_of(frame);
    adamas_fiber_name *name = named(task, at);
    uint32_t awaited;
    adamas_segment *segment;
    adamas_fiber *waiting;
    int found;
    adamas_value ready;
    if (name == NULL) {
        adamas_fail("`await` над значением, которого питомник не собирал (§5.2)");
    }
    if (name->home != nursery) {
        /* Задача чужого круга: её очередь и список ждущих не здесь, и ждать её
         * отсюда нечем. Ответа её тоже нет - круг, закрывшись, освобождает
         * готовые, - поэтому и договорившая сюда не подходит. */
        adamas_fail("`await` над задачей чужого питомника (§5.2)");
    }
    awaited = name->id;
    /* Задача потреблена: `await : (1 t : Task) -> a` (§5.2). Разбора её
     * значения при этом нет, поэтому нет и отмены. */
    adamas_drop(task, nursery->release);
    if (nursery->hands != 0) {
        return await_crowded(kont, nursery, frame, awaited);
    }
    ready = done_read(nursery, awaited, &found);
    if (found) {
        return ready;
    }
    segment = adamas_kont_cut(kont, frame);
    waiting = parked(frame, segment, adamas_unit());
    waiting->awaited = awaited;
    waiting->next = nursery->blocked;
    nursery->blocked = waiting;
    return nursery_step(kont, nursery);
}

adamas_value adamas_nursery_finished(adamas_kont *kont, adamas_frame *frame, adamas_value value) {
    adamas_nursery *nursery = nursery_of(frame);
    uint32_t id = fiber_id_of(frame);
    adamas_fiber *waiting;
    adamas_fiber *keep = NULL;
    /* **Второе место вызова промоушена** (§5.2). Ответ договорившего забирают
     * ждавшие его - и `await` их вправе стоять на чужом воркере, - а корневой
     * ответ и вовсе едет к хозяину круга. Значение, которое сейчас уйдёт в
     * готовые, с этой минуты считается атомарно. */
    if (nursery->hands != 0) {
        adamas_share(value, nursery->promote);
    }
    nursery_hold(nursery);
    if (fiber_root_of(frame)) {
        nursery->result = adamas_dup(value);
        nursery->answered = 1;
    }
    /* Ждавшие его возвращаются в круг: чужой ответ готов - и он же становится
     * тем, чем возобновление им ответит. Единицу тут положить нельзя: `await`
     * объявлен отдающим `a` задачи (§5.2). */
    waiting = nursery->blocked;
    while (waiting != NULL) {
        adamas_fiber *fiber = waiting;
        waiting = waiting->next;
        if (fiber->awaited == id) {
            /* Ждущий несёт единицу - её кладёт `parked`, и заменяется она
             * только здесь. Проверка стоит вместо дропа не из осторожности:
             * дроп значения с именем файбера внутри позвал бы
             * `adamas_fiber_name_release`, тот - `nursery_unref`, а тот взял бы
             * замок вторым разом на этом же потоке. Названный отказ лучше
             * зависания. */
            if (!adamas_is_imm(fiber->answer)) {
                adamas_fail("ждущий файбер нёс не единицу (§5.2)");
            }
            fiber->answer = adamas_dup(value);
            queue_push(nursery, fiber);
        } else {
            fiber->next = keep;
            keep = fiber;
        }
    }
    nursery->blocked = keep;
    done_push(nursery, id, value);
    nursery_wakened(nursery);
    nursery_free(nursery);
    return nursery_step(kont, nursery);
}

adamas_segment *adamas_nursery_abandoned(adamas_frame *frame) {
    adamas_nursery *nursery = nursery_of(frame);
    adamas_fiber *fiber;
    if (nursery->hands != 0) {
        /* **Названная граница многопоточного круга.** Обрыв уходит наружу
         * питомника, а под кадром питомника у воркера пусто: раскручивать
         * оттуда нечего, и продолжать обрыв некуда. Говорится это вслух, а не
         * молча портит стек.
         *
         * У хозяина стек под кадром есть, и там обрыв законен; воркеров перед
         * раскруткой надо собрать - иначе они продолжат брать файберы из
         * круга, который уже вычерпывается. */
        if (!pthread_equal(nursery->owner, pthread_self())) {
            adamas_fail("обрыв круга из мигрировавшего файбера не выражается (§5.2)");
        }
        crew_join(nursery);
    }
    /* Ждущие чужого ответа брошены наравне с очередью: ответа им теперь не
     * будет ни от кого. Ещё не начатый отбрасывается молча - тело его не
     * начиналось, и закрывать в нём нечего. */
    while ((fiber = queue_pop_back(nursery)) != NULL) {
        adamas_segment *segment = fiber->segment;
        fiber->segment = NULL;
        fiber_free(nursery, fiber);
        if (segment != NULL) {
            return segment;
        }
    }
    while (nursery->blocked != NULL) {
        adamas_segment *segment;
        fiber = nursery->blocked;
        nursery->blocked = fiber->next;
        segment = fiber->segment;
        fiber->segment = NULL;
        fiber_free(nursery, fiber);
        if (segment != NULL) {
            return segment;
        }
    }
    done_clear(nursery);
    if (nursery->answered) {
        adamas_drop(nursery->result, nursery->release);
        nursery->result = adamas_unit();
        nursery->answered = 0;
    }
    nursery_close(nursery);
    return NULL;
}

adamas_value adamas_nursery_cancel(adamas_kont *kont, adamas_value task, uint32_t at) {
    adamas_fiber_name *name = named(task, at);
    adamas_nursery *nursery;
    adamas_fiber *fiber;
    adamas_segment *segment;
    adamas_value ready;
    int found;
    if (name == NULL) {
        return task;
    }
    nursery = name->home;
    /* Ответ договорившего никому не достанется: снимается с готовых - тем же
     * `retain`, каким снимает его машина.
     *
     * **Свидетель у этой строки появился** треком I волны 2 Фазы 7:
     * `adamas-codegen/tests/nursery.rs`,
     * `the_answer_of_a_cancelled_task_is_taken_off_the_ready_list`. Прежде его
     * не было, и мешало этому одно: различающая программа кончается взаимной
     * блокировкой, то есть обрывом, а наблюдать обрыв ни один прогон тогда не
     * умел - `agreed` и `llvm_agreed` роняют тест на ненулевом коде возврата.
     * Наблюдение добавлено (`harness::c_printed`), и сними эту строку - `await`
     * по копии отвечает `9 13` вместо обрыва. Копию даёт `data Task`:
     * кратность значения ω, и второе упоминание написать можно. */
    nursery_hold(nursery);
    ready = done_take(nursery, name->id, &found);
    fiber = fiber_take(nursery, name->id);
    nursery_free(nursery);
    /* Дроп **после** замка: внутри снятого ответа бывает имя файбера, а его
     * release берёт замок круга - на этом же потоке это было бы зависание. */
    adamas_drop(ready, nursery->release);
    if (fiber == NULL) {
        /* Файбер не найден: договорил либо бежит сам, и снимать со стека
         * нечего.
         *
         * **Многопоточный круг добавляет сюда третий случай, и он не покрыт:**
         * файбер бежит на **чужом** воркере. Отмена тогда молча не происходит -
         * задача досчитывает до конца, и питомник её дожидается. Однопоточному
         * кругу этот случай был пуст (бежать мог только сам отменяющий);
         * закрыть его нечем без точки прерывания у бегущего файбера, а её §5.2
         * не называет: отмена там приходит в suspend-точке, то есть к тому, кто
         * уже уступил. */
        return task;
    }
    segment = fiber->segment;
    fiber->segment = NULL;
    fiber_free(nursery, fiber);
    if (segment == NULL) {
        return task;
    }
    /* Сегмент отдаётся **без нижней метки**: свой кадр питомника уступивший
     * несёт с собой, а раскрутке он означал бы «питомник брошен» и вычерпал
     * бы круг целиком (ревью 2026-09-08 у машины). */
    adamas_segment_disown_base(segment);
    adamas_segment_unwind_holding(kont, segment, task);
    return adamas_unit();
}

/* Вектор evidence: скрытый первый аргумент понижённой функции (§3.4).
 *
 * Вектор неизменяем, а вход в хендлер даёт новый - копией родителя плюс запись.
 * Копия стоит O(n) на вход в хендлер, и это цена evidence-перевода: взамен
 * операция находит свой хендлер по статической позиции, а не обходом стека.
 *
 * Записи хендлерами не владеют. Кадр хендлера живёт в цепочке кадров или в
 * вырезанном сегменте, и владеет им она; вектор его лишь называет.
 *
 * Запись бывает **подавленной**: хендлер уже ответил, и второго ответа деть
 * некуда. Это не «записи нет» и не «искать дальше наружу» - разница названа у
 * `adamas_evidence_lookup` и стоила ревью 2026-09-05.
 *
 * Маска - тоже правка вектора, и другой быть не может: `#mask.L` стоит вокруг
 * **чужого** вычисления, а операции лежат внутри него, поэтому места, куда
 * вписать число пропусков, у маски нет вовсе. Вектор же приходит маскируемому
 * вычислению целиком - его и правит `adamas_evidence_mask`.
 */

#include "adamas.h"

#include <string.h>

typedef struct adamas_ev_entry {
    uint32_t label;
    uint32_t flags;
    adamas_frame *handler;
} adamas_ev_entry;

struct adamas_evidence {
    adamas_header header;
    size_t count;
    adamas_ev_entry entries[];
};

_Static_assert(sizeof(adamas_ev_entry) == 16, "запись вектора - два слова");
_Static_assert(offsetof(struct adamas_evidence, entries) == 16, "записи идут с 16-го байта");

static adamas_evidence *evidence_alloc(size_t count) {
    adamas_evidence *evidence = (adamas_evidence *)adamas_block_alloc(
        sizeof(adamas_evidence) + count * sizeof(adamas_ev_entry));
    adamas_header *header = adamas_header_of(evidence);
    header->rc = 0;
    header->tag = ADAMAS_TAG_EVIDENCE;
    header->flags = 0;
    evidence->count = count;
    return evidence;
}

/* Разделяемость **наследуется** потомком вектора (§5.2).
 *
 * Найдено санитайзером, а не выведено: пометить один `nursery->base` мало.
 * Вектор файбера строится из базы копией записей (`adamas_evidence_extend` в
 * `nursery_start`), и живёт он ровно столько, сколько живут кадры этого
 * файбера, - а кадры уезжают на чужой воркер вместе с ним. Счётчик такого
 * вектора правят `frame_alloc` и `frame_free` на разных потоках, и без
 * наследования он правится голым `+=`. Стенд `adamas-codegen/tests/threads.rs`
 * ловил это как «живо 1» раз в несколько сотен прогонов, а под шестью копиями
 * разом - как `malloc_consolidate(): unaligned fastbin chunk`.
 *
 * Наследование, а не пометка при постройке файбера: вектор плодится и дальше -
 * всякий `handle` внутри задачи даёт новый, - и метить надо всю нисходящую
 * цепочку, а не её корень. Корень метит `adamas_nursery_begin`.
 *
 * Цена вне многопоточного круга - ноль: у базы флага нет, и ветвь ниже никогда
 * не срабатывает. */
static void inherit_shared(adamas_evidence *child, const adamas_evidence *parent) {
    if (parent == NULL) {
        return;
    }
    adamas_header_of(child)->flags |=
        ((const adamas_header *)(const void *)parent)->flags & ADAMAS_FLAG_SHARED;
}

adamas_evidence *adamas_evidence_empty(void) {
    return evidence_alloc(0);
}

adamas_evidence *adamas_evidence_extend(const adamas_evidence *parent, uint32_t label,
                                        adamas_frame *handler) {
    size_t count = parent == NULL ? 0 : parent->count;
    adamas_evidence *extended = evidence_alloc(count + 1);
    if (count > 0) {
        memcpy(extended->entries, parent->entries, count * sizeof(adamas_ev_entry));
    }
    extended->entries[count].label = label;
    extended->entries[count].flags = 0;
    extended->entries[count].handler = handler;
    inherit_shared(extended, parent);
    return extended;
}

adamas_evidence *adamas_evidence_mask(const adamas_evidence *parent, uint32_t label) {
    size_t count = parent == NULL ? 0 : parent->count;
    size_t found = count; /* `count` значит «записи такой метки нет» */
    for (size_t index = count; index > 0; index -= 1) {
        /* Изнутри наружу, и подавленная запись подходит наравне с живой: у
         * машины маску гасят и `Handler`, и `Suppressing` (`Kont::catching`). */
        if (parent->entries[index - 1].label == label) {
            found = index - 1;
            break;
        }
    }
    if (found == count) {
        /* Снимать нечего, и это не ошибка: операция внутри упрётся в
         * `MISSING` - ровно то же, чем кончает машина, у которой кадр маски
         * стоит, а хендлера под ним нет. */
        return adamas_evidence_copy(parent);
    }
    adamas_evidence *masked = evidence_alloc(count - 1);
    memcpy(masked->entries, parent->entries, found * sizeof(adamas_ev_entry));
    memcpy(masked->entries + found, parent->entries + found + 1,
           (count - found - 1) * sizeof(adamas_ev_entry));
    inherit_shared(masked, parent);
    return masked;
}

adamas_evidence *adamas_evidence_copy(const adamas_evidence *evidence) {
    size_t count = evidence == NULL ? 0 : evidence->count;
    adamas_evidence *copy = evidence_alloc(count);
    if (count > 0) {
        memcpy(copy->entries, evidence->entries, count * sizeof(adamas_ev_entry));
    }
    inherit_shared(copy, evidence);
    return copy;
}

void adamas_evidence_suppress(adamas_evidence *evidence, const adamas_frame *handler) {
    if (evidence == NULL) {
        return;
    }
    /* По самому кадру, а не по метке: двух одноимённых хендлеров в цепочке
     * ничто не запрещает, и подавлять надо тот, чей ответ уже дан. Записи
     * этого кадра может не быть - тогда подавлять нечего: вектор деструктора
     * снят внутри всех хендлеров под ним, и отсутствие означает, что кадр не
     * хендлер вовсе. */
    for (size_t index = 0; index < evidence->count; index += 1) {
        if (evidence->entries[index].handler == handler) {
            evidence->entries[index].flags |= ADAMAS_EV_SUPPRESSED;
            return;
        }
    }
}

void adamas_evidence_rebind(adamas_evidence *evidence, const adamas_frame *from,
                            adamas_frame *to) {
    if (evidence == NULL) {
        return;
    }
    for (size_t index = 0; index < evidence->count; index += 1) {
        if (evidence->entries[index].handler == from) {
            evidence->entries[index].handler = to;
        }
    }
}

int adamas_evidence_names(const adamas_evidence *evidence, const adamas_frame *handler) {
    if (evidence == NULL) {
        return 0;
    }
    for (size_t index = 0; index < evidence->count; index += 1) {
        if (evidence->entries[index].handler == handler) {
            return 1;
        }
    }
    return 0;
}

size_t adamas_evidence_count(const adamas_evidence *evidence) {
    return evidence == NULL ? 0 : evidence->count;
}

adamas_frame *adamas_evidence_at(const adamas_evidence *evidence, size_t index) {
    if (evidence == NULL || index >= evidence->count) {
        adamas_fail("запись вектора evidence за его пределами");
    }
    return evidence->entries[index].handler;
}

int adamas_evidence_suppressed_at(const adamas_evidence *evidence, size_t index) {
    if (evidence == NULL || index >= evidence->count) {
        adamas_fail("запись вектора evidence за его пределами");
    }
    return (evidence->entries[index].flags & ADAMAS_EV_SUPPRESSED) != 0;
}

uint32_t adamas_evidence_label_at(const adamas_evidence *evidence, size_t index) {
    if (evidence == NULL || index >= evidence->count) {
        adamas_fail("запись вектора evidence за его пределами");
    }
    return evidence->entries[index].label;
}

int adamas_evidence_lookup(const adamas_evidence *evidence, uint32_t label,
                           adamas_frame **handler) {
    if (handler != NULL) {
        *handler = NULL;
    }
    if (evidence == NULL) {
        return ADAMAS_LOOKUP_MISSING;
    }
    /* Изнутри наружу: последняя запись есть ближайший хендлер. Пропусков поиск
     * не считает - маски снимают записи до него (`adamas_evidence_mask`). */
    size_t index = evidence->count;
    while (index > 0) {
        index -= 1;
        if (evidence->entries[index].label != label) {
            continue;
        }
        if (handler != NULL) {
            *handler = evidence->entries[index].handler;
        }
        if ((evidence->entries[index].flags & ADAMAS_EV_SUPPRESSED) != 0) {
            return ADAMAS_LOOKUP_SUPPRESSED;
        }
        return ADAMAS_LOOKUP_HANDLER;
    }
    return ADAMAS_LOOKUP_MISSING;
}

/* Счётчик вектора **гибриден** ровно так же, как счётчик объекта (§5.1).
 *
 * Прежде он правился здесь голым `+=`, и однопоточному кругу этого хватало. С
 * настоящими потоками (§5.2) не хватает: вектор места `withNursery` называет
 * **каждый** кадр питомника, а кадры эти ставят и снимают разные воркеры -
 * счётчик его правится ими вперемежку. Помечает вектор разделяемым
 * `adamas_nursery_begin`; с этой минуты ветвь ниже уводит его в атомарный
 * режим.
 *
 * Ветвь написана **здесь**, а не сведена к `adamas_dup`/`adamas_drop`, и это
 * не дублирование ради вкуса: вектор дупается и дропается на каждый кадр
 * (`frame_alloc`, `frame_free`), а `adamas_dup` живёт в другой единице
 * трансляции - сведение добавило бы вызов на каждый кадр там, где стоял
 * инкремент. Ноты те же и по тем же доводам, что у `object.c`: `relaxed` на
 * взятии, `acq_rel` на отдаче.
 *
 * Разделяемые половины вынесены за `noinline, cold` - правило вопроса 175 и
 * трека B волны 3: атомарная операция, оставленная в теле, переворачивает
 * решение инлайнера.
 *
 * *Цена измерена, и она в пределах разброса окна.* Нагрузками из таблицы
 * разрыва её мерить не на чем - ни одна из пяти кадра не ставит вовсе
 * (`adamas_kont_push` в их порождённом C ноль вхождений), то есть вектора не
 * трогает. Мерено на самой кадроёмкой из доступных - хендлерном стенде
 * `benches/native.rs`: шесть парных замеров дали 0.9862, 0.9926, 1.0014,
 * 1.0055, 1.0247, 1.0472 против счётчика без ветви, то есть **медиана 1.003 при
 * размахе 0.061**. Воспроизводится
 * `docs/measurements/threads/evidence-counter.sh`.
 *
 * Первая редакция сводила эти две точки к `adamas_dup`/`adamas_drop` и была
 * отвергнута не замером, а чтением: те живут в другой единице трансляции, и
 * сведение добавило бы вызов на каждый кадр.
 *
 * Детей у вектора нет: записи называют кадры, но ими не владеют (см. шапку), -
 * поэтому последняя ссылка просто отдаёт блок. */
__attribute__((noinline, cold)) static void evidence_dup_shared(adamas_header *header) {
    __atomic_fetch_add(&header->rc, 1u, __ATOMIC_RELAXED);
}

__attribute__((noinline, cold)) static int evidence_released_shared(adamas_header *header) {
    return __atomic_fetch_sub(&header->rc, 1u, __ATOMIC_ACQ_REL) == 0;
}

adamas_evidence *adamas_evidence_dup(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return NULL;
    }
    adamas_header *header = adamas_header_of(evidence);
    if ((header->flags & ADAMAS_FLAG_SHARED) != 0) {
        evidence_dup_shared(header);
        return evidence;
    }
    header->rc += 1;
    return evidence;
}

void adamas_evidence_drop(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return;
    }
    adamas_header *header = adamas_header_of(evidence);
    if ((header->flags & ADAMAS_FLAG_SHARED) != 0) {
        if (evidence_released_shared(header)) {
            adamas_block_free(evidence);
        }
        return;
    }
    if (header->rc == 0) {
        adamas_block_free(evidence);
        return;
    }
    header->rc -= 1;
}

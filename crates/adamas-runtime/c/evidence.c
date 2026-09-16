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
    return masked;
}

adamas_evidence *adamas_evidence_copy(const adamas_evidence *evidence) {
    size_t count = evidence == NULL ? 0 : evidence->count;
    adamas_evidence *copy = evidence_alloc(count);
    if (count > 0) {
        memcpy(copy->entries, evidence->entries, count * sizeof(adamas_ev_entry));
    }
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

/* Счётчик вектора идёт через общий, гибридный (§5.1), а не правится здесь.
 *
 * Прежде он правился здесь голым `+=`, и однопоточному кругу этого хватало. С
 * настоящими потоками (§5.2) не хватает: вектор места `withNursery` называет
 * **каждый** кадр питомника, а кадры эти ставят и снимают разные воркеры -
 * счётчик его правится ими вперемежку. Помечает его разделяемым
 * `adamas_nursery_begin`, и с этой минуты та же ветвь по флагу, что у объектов,
 * уводит его в атомарный режим.
 *
 * Детей у вектора нет: записи называют кадры, но ими не владеют (см. шапку), -
 * поэтому `release` здесь `NULL`, и `adamas_drop` на последней ссылке просто
 * отдаёт блок. */
adamas_evidence *adamas_evidence_dup(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return NULL;
    }
    adamas_dup((adamas_value)(void *)evidence);
    return evidence;
}

void adamas_evidence_drop(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return;
    }
    adamas_drop((adamas_value)(void *)evidence, NULL);
}

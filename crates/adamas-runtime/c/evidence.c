/* Вектор evidence: скрытый первый аргумент понижённой функции (§3.4).
 *
 * Вектор неизменяем, а вход в хендлер даёт новый - копией родителя плюс запись.
 * Копия стоит O(n) на вход в хендлер, и это цена evidence-перевода: взамен
 * операция находит свой хендлер по статической позиции, а не обходом стека.
 *
 * Записи хендлерами не владеют. Кадр хендлера живёт в цепочке кадров или в
 * вырезанном сегменте, и владеет им она; вектор его лишь называет.
 */

#include "adamas.h"

#include <string.h>

typedef struct adamas_ev_entry {
    uint32_t label;
    uint32_t padding;
    adamas_frame *handler;
} adamas_ev_entry;

struct adamas_evidence {
    adamas_header header;
    size_t count;
    adamas_ev_entry entries[];
};

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
    extended->entries[count].padding = 0;
    extended->entries[count].handler = handler;
    return extended;
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

uint32_t adamas_evidence_label_at(const adamas_evidence *evidence, size_t index) {
    if (evidence == NULL || index >= evidence->count) {
        adamas_fail("запись вектора evidence за его пределами");
    }
    return evidence->entries[index].label;
}

adamas_frame *adamas_evidence_find(const adamas_evidence *evidence, uint32_t label, size_t skip) {
    if (evidence == NULL) {
        return NULL;
    }
    /* Изнутри наружу: последняя запись есть ближайший хендлер. Маски считаются
     * по дороге - каждая пропускает один подходящий (§3.4, §10 вопрос 72). */
    size_t index = evidence->count;
    while (index > 0) {
        index -= 1;
        if (evidence->entries[index].label != label) {
            continue;
        }
        if (skip > 0) {
            skip -= 1;
            continue;
        }
        return evidence->entries[index].handler;
    }
    return NULL;
}

adamas_evidence *adamas_evidence_dup(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return NULL;
    }
    adamas_header_of(evidence)->rc += 1;
    return evidence;
}

void adamas_evidence_drop(adamas_evidence *evidence) {
    if (evidence == NULL) {
        return;
    }
    adamas_header *header = adamas_header_of(evidence);
    if (header->rc == 0) {
        adamas_block_free(evidence);
        return;
    }
    header->rc -= 1;
}

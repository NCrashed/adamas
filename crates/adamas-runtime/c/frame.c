/* Кадры второй формы понижения, стек продолжения и его сегменты.
 *
 * Модель повторяет машину интерпретатора (`adamas-interp/src/frame.rs`)
 * **семантикой**, а не представлением: там стек лежит звеньями в `Vec`, здесь -
 * односвязной цепочкой объектов кучи. Совпадать обязаны метки, порядок работы
 * и порядок раскрутки; представление решено отдельно (§13, 2026-09-08).
 *
 * Кадр всегда уникален. Цепочка одна, разделения нет, мультишот копирует -
 * поэтому счётчик в заголовке кадра неизменно нуль. Заголовок у него общий
 * ради единообразия аллокации и учёта.
 */

#include "adamas.h"

struct adamas_frame {
    adamas_header header; /* tag - метка кадра, `adamas_mark` */
    adamas_frame *below;
    adamas_frame_code code;
    adamas_frame_release release;
    adamas_evidence *evidence;
    uint32_t label;
    uint32_t fields;
    adamas_value env[];
};

struct adamas_segment {
    adamas_header header;
    adamas_frame *top;
    adamas_frame *base;
    size_t depth;
};

static adamas_frame *frame_alloc(uint16_t mark, uint32_t label, adamas_frame_code code,
                                 adamas_frame_release release, size_t fields,
                                 adamas_evidence *evidence) {
    adamas_frame *frame = (adamas_frame *)adamas_block_alloc(sizeof(adamas_frame) +
                                                             fields * sizeof(adamas_value));
    adamas_header *header = adamas_header_of(frame);
    header->rc = 0;
    header->tag = mark;
    header->flags = 0;
    frame->below = NULL;
    frame->code = code;
    frame->release = release;
    frame->evidence = adamas_evidence_dup(evidence);
    frame->label = label;
    frame->fields = (uint32_t)fields;
    return frame;
}

/* Вектор деструктора при раскрутке: копия с подавленными записями хендлеров,
 * которые уже ответили.
 *
 * Мертвы они все до одного: основание сегмента - хендлер, чья ветка ответ дала,
 * а хендлеры **между** ним и этим scope'ом брошены вместе с сегментом. Ходит
 * по ним рантайм и только рантайм: цепочку обходит он, и никто больше не знает,
 * какие записи мертвы. Ровно тот же ряд ставит машина кадрами `Suppressing`
 * (`adamas-interp/src/effect.rs`, `Machine::unwinding`); представление другое,
 * потому что поиск здесь ведёт вектор, а не обход стека.
 *
 * Запись **помечается**, а не снимается, и разница названа ревью 2026-09-05:
 * снятая уводила бы операцию деструктора к одноимённому хендлеру снаружи -
 * статика и динамика расходились бы молча.
 *
 * Цена - копия вектора на деструктор. Путь холодный (раскрутка), и другого
 * места у пометки нет: вектор общий с живым кодом, править его на месте нельзя.
 */
static adamas_evidence *closing_evidence(adamas_frame *frame) {
    adamas_evidence *evidence = adamas_evidence_copy(frame->evidence);
    for (adamas_frame *below = frame->below; below != NULL; below = below->below) {
        if (adamas_frame_mark(below) == ADAMAS_MARK_HANDLER) {
            adamas_evidence_suppress(evidence, below);
        }
    }
    return evidence;
}

/* Деструктор scope: §3.3 требует его и при нормальном выходе, и при обрыве.
 * Отвечает он `()`, поэтому ответ дропается непосредственным.
 *
 * `unwinding` различает два случая. При нормальном выходе хендлеры под scope'ом
 * живы, и операция деструктора обязана их достать. При раскрутке они мертвы, и
 * вектор деструктора говорит об этом каждому, кто спросит.
 *
 * Флаг явный, хотя нормальный путь и так отцепляет кадр до вызова, и
 * `closing_evidence` нашла бы под ним пустоту. Опираться на это значило бы
 * держать различие двух путей на порядке двух строк в третьем месте.
 */
static void frame_close(adamas_frame *frame, int unwinding) {
    adamas_value closer = frame->env[0];
    adamas_evidence *evidence = unwinding ? closing_evidence(frame) : frame->evidence;
    adamas_value answer = adamas_apply(closer, evidence, adamas_unit());
    adamas_drop(answer, NULL);
    if (unwinding) {
        adamas_evidence_drop(evidence);
    }
}

static void frame_free(adamas_frame *frame) {
    if (frame->release != NULL) {
        frame->release(frame);
    }
    adamas_evidence_drop(frame->evidence);
    adamas_block_free(frame);
}

static adamas_segment *segment_alloc(adamas_frame *top, adamas_frame *base, size_t depth) {
    adamas_segment *segment = (adamas_segment *)adamas_block_alloc(sizeof(adamas_segment));
    adamas_header *header = adamas_header_of(segment);
    header->rc = 0;
    header->tag = ADAMAS_TAG_SEGMENT;
    header->flags = 0;
    segment->top = top;
    segment->base = base;
    segment->depth = depth;
    return segment;
}

/* ------------------------------------------------------------------ */
/* Стек                                                                */
/* ------------------------------------------------------------------ */

void adamas_kont_init(adamas_kont *kont) {
    kont->top = NULL;
    kont->depth = 0;
}

adamas_frame *adamas_kont_push(adamas_kont *kont, uint16_t mark, uint32_t label,
                               adamas_frame_code code, adamas_frame_release release, size_t fields,
                               adamas_evidence *evidence) {
    adamas_frame *frame = frame_alloc(mark, label, code, release, fields, evidence);
    frame->below = kont->top;
    kont->top = frame;
    kont->depth += 1;
    return frame;
}

adamas_value *adamas_frame_env(adamas_frame *frame) {
    return frame->env;
}

size_t adamas_frame_fields(const adamas_frame *frame) {
    return frame->fields;
}

uint16_t adamas_frame_mark(const adamas_frame *frame) {
    return ((const adamas_header *)(const void *)frame)->tag;
}

uint32_t adamas_frame_label(const adamas_frame *frame) {
    return frame->label;
}

adamas_evidence *adamas_frame_evidence(adamas_frame *frame) {
    return frame->evidence;
}

adamas_value adamas_kont_run(adamas_kont *kont, adamas_value value) {
    while (kont->top != NULL) {
        adamas_frame *frame = kont->top;
        kont->top = frame->below;
        kont->depth -= 1;
        frame->below = NULL;
        if (adamas_frame_mark(frame) == ADAMAS_MARK_CLOSING) {
            /* Scope закончился нормально: деструктор срабатывает, а значение
             * идёт мимо него дальше - оно и есть ответ scope'а. Подавления
             * тут нет: хендлеры под scope'ом живы и ответа ещё не давали. */
            frame_close(frame, 0);
        } else if (frame->code != NULL) {
            /* Код вправе положить новые кадры: они и станут вершиной, а ответ
             * пойдёт им. */
            value = frame->code(frame, value);
        }
        frame_free(frame);
    }
    return value;
}

/* ------------------------------------------------------------------ */
/* Сегменты                                                            */
/* ------------------------------------------------------------------ */

adamas_segment *adamas_kont_cut(adamas_kont *kont, adamas_frame *handler) {
    if (handler == NULL) {
        adamas_fail("резать нечего: кадр хендлера не назван");
    }
    /* Обход идёт по будущему сегменту, а не по всему стеку, и нужен он только
     * ради длины: копирование и раскрутка стоят столько же. Кадр хендлера
     * приходит из вектора evidence, поэтому поиска здесь нет (§3.4). */
    size_t depth = 1;
    adamas_frame *frame = kont->top;
    while (frame != NULL && frame != handler) {
        frame = frame->below;
        depth += 1;
    }
    if (frame == NULL) {
        adamas_fail("кадр хендлера не принадлежит этому стеку");
    }
    adamas_segment *segment = segment_alloc(kont->top, handler, depth);
    kont->top = handler->below;
    kont->depth -= depth;
    handler->below = NULL;
    return segment;
}

void adamas_kont_restore(adamas_kont *kont, adamas_segment *segment) {
    segment->base->below = kont->top;
    kont->top = segment->top;
    kont->depth += segment->depth;
    /* Ручка потреблена: сегмент снова часть стека, и второго владельца у него
     * нет. Мультишот восстанавливает копию, а не этот же сегмент. */
    adamas_block_free(segment);
}

size_t adamas_segment_depth(const adamas_segment *segment) {
    return segment->depth;
}

adamas_frame *adamas_segment_base(adamas_segment *segment) {
    return segment->base;
}

adamas_segment *adamas_segment_copy(const adamas_segment *segment) {
    adamas_frame *source = segment->top;
    adamas_frame *previous = NULL;
    adamas_frame *first = NULL;
    while (source != NULL) {
        adamas_frame *copy = frame_alloc(adamas_frame_mark(source), source->label, source->code,
                                         source->release, source->fields, source->evidence);
        for (uint32_t index = 0; index < source->fields; index += 1) {
            copy->env[index] = adamas_dup(source->env[index]);
        }
        if (previous == NULL) {
            first = copy;
        } else {
            previous->below = copy;
        }
        previous = copy;
        source = source->below;
    }
    return segment_alloc(first, previous, segment->depth);
}

void adamas_segment_unwind(adamas_segment *segment) {
    /* От вершины к основанию - изнутри наружу, то есть LIFO (§3.4). Тот же
     * порядок, каким идёт `Machine::unwinding` в интерпретаторе. */
    adamas_frame *frame = segment->top;
    while (frame != NULL) {
        adamas_frame *below = frame->below;
        if (adamas_frame_mark(frame) == ADAMAS_MARK_CLOSING) {
            /* Хендлеры под этим scope'ом свои ответы уже дали: подавлены. */
            frame_close(frame, 1);
        }
        frame_free(frame);
        frame = below;
    }
    adamas_block_free(segment);
}

adamas_value adamas_segment_value(adamas_segment *segment) {
    return (adamas_value)(void *)segment;
}

adamas_segment *adamas_segment_of(adamas_value value) {
    if (adamas_is_imm(value) || adamas_tag(value) != ADAMAS_TAG_SEGMENT) {
        adamas_fail("значение не резумпция");
    }
    return (adamas_segment *)(void *)value;
}

void adamas_resumption_drop(adamas_value value) {
    adamas_segment *segment = adamas_segment_of(value);
    adamas_header *header = adamas_header_of(segment);
    if (header->rc == 0) {
        /* §3.4: дроп разматывает приостановленный сегмент, выполняя деструкторы
         * кадров внутри него. Резумпция аффинна, поэтому путь этот обычный, а
         * не крайний. */
        adamas_segment_unwind(segment);
        return;
    }
    header->rc -= 1;
}

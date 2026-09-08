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

/* Смещения закреплены: числа эти уезжают от перестановки полей молча, а Фаза 7
 * ставит по ним `align` и `dereferenceable` (шапка `adamas.h`, «Выравнивание»). */
_Static_assert(offsetof(struct adamas_frame, env) == 48, "среда кадра идёт с 48-го байта");
_Static_assert(sizeof(struct adamas_segment) == 32, "сегмент - четыре слова");

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
 * а хендлеры **между** ним и этим scope'ом брошены вместе с сегментом. `rest` -
 * остаток раскручиваемой цепочки под scope'ом; ходит по нему рантайм и только
 * рантайм. Ровно тот же ряд ставит машина кадрами `Suppressing`
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
static adamas_evidence *closing_evidence(adamas_frame *frame, adamas_frame *rest) {
    adamas_evidence *evidence = adamas_evidence_copy(frame->evidence);
    for (adamas_frame *below = rest; below != NULL; below = below->below) {
        if (adamas_frame_mark(below) == ADAMAS_MARK_HANDLER) {
            adamas_evidence_suppress(evidence, below);
        }
    }
    return evidence;
}

static void frame_free(adamas_frame *frame, adamas_kont *kont) {
    if (frame->release != NULL) {
        frame->release(frame, kont);
    }
    adamas_evidence_drop(frame->evidence);
    adamas_block_free(frame);
}

/* Среда кадра `UNWINDING`: слот 0 - значение, которым раскрутка кончится,
 * слот 1 - остаток цепочки сегментом. `label` - захвачен ли слот 0: кадр
 * ставится раньше, чем проточное значение существует, и первое пришедшее
 * становится held - тем же, чем у машины служит аргумент `buried`. */
static void unwind_push(adamas_kont *kont, adamas_segment *chain, adamas_value held,
                        uint32_t captured);

/* Дроп среды кадра раскрутки - на случай, когда кадр гибнет, не шагая:
 * внутри оборванного куска. Остаток его цепочки кладётся раскруткой же. */
static void unwinding_release(adamas_frame *frame, adamas_kont *kont) {
    adamas_drop(frame->env[0], NULL);
    adamas_value chain = frame->env[1];
    if (!adamas_is_imm(chain) && adamas_tag(chain) == ADAMAS_TAG_SEGMENT) {
        adamas_resumption_drop(kont, chain);
    }
}

/* Дроп среды кадра `CLOSED`: ответ scope, не дождавшийся своего деструктора. */
static void closed_release(adamas_frame *frame, adamas_kont *kont) {
    (void)kont;
    adamas_drop(frame->env[0], NULL);
}

/* Один шаг раскрутки: снять одно звено остатка. Кадр потребляется, остаток
 * перекладывается кадром заново - вершина между шагами открыта тому, что
 * положили деструктор и release звеньев (вложенные раскрутки бегут первыми,
 * LIFO). Порядок тот же, каким идёт `Machine::unwinding` (§10 вопрос 144). */
static adamas_value unwind_step(adamas_kont *kont, adamas_frame *frame, adamas_value incoming) {
    adamas_value held;
    if (frame->label == 0) {
        /* Первое пришедшее - то, что текло по стеку в момент смерти сегмента:
         * оно и есть ответ раскрутки, машина получает его аргументом. */
        held = incoming;
    } else {
        /* Ответ деструктора либо вложенной раскрутки: `()` по §3.3, дропается. */
        adamas_drop(incoming, NULL);
        held = frame->env[0];
    }
    adamas_segment *chain = adamas_segment_of(frame->env[1]);
    frame->env[0] = adamas_unit();
    frame->env[1] = adamas_unit();
    frame_free(frame, kont);

    adamas_frame *next = chain->top;
    if (next == NULL) {
        adamas_block_free(chain);
        return held;
    }
    chain->top = next->below;
    chain->depth -= 1;
    next->below = NULL;

    uint16_t mark = adamas_frame_mark(next);
    if (mark == ADAMAS_MARK_UNWINDING) {
        /* Вложенная раскрутка, чей контекст умер вместе с этим звеном: остаток
         * внешней ложится ниже, вложенная продолжается первой. Её held придёт
         * внешнему кадру и будет отброшен - как у машины, где held вложенного
         * `Frame::Unwinding` гибнет при взятии. */
        unwind_push(kont, chain, held, 1);
        next->below = kont->top;
        kont->top = next;
        kont->depth += 1;
        return adamas_unit();
    }
    if (mark == ADAMAS_MARK_CLOSING) {
        /* Хендлеры в остатке цепочки свои ответы уже дали: подавлены. Остаток
         * ложится кадром **до** деструктора: операция к живому хендлеру
         * снаружи режет один стек, и раскрутка уезжает в сегмент резумпции
         * вместе с ним - возобновление продолжит обе. */
        adamas_evidence *evidence = closing_evidence(next, chain->top);
        unwind_push(kont, chain, held, 1);
        adamas_value closer = next->env[0];
        adamas_value answer = adamas_apply(closer, evidence, kont, adamas_unit());
        adamas_evidence_drop(evidence);
        frame_free(next, kont);
        return answer;
    }
    /* Прочее звено: работа брошена, среда дропается. Остаток кладётся до
     * дропа: release резумпции в среде ставит вложенную раскрутку выше, и
     * она бежит первой. */
    unwind_push(kont, chain, held, 1);
    frame_free(next, kont);
    return adamas_unit();
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

static void unwind_push(adamas_kont *kont, adamas_segment *chain, adamas_value held,
                        uint32_t captured) {
    adamas_frame *frame =
        adamas_kont_push(kont, ADAMAS_MARK_UNWINDING, captured, NULL, unwinding_release, 2, NULL);
    frame->env[0] = held;
    frame->env[1] = adamas_segment_value(chain);
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
        uint16_t mark = adamas_frame_mark(frame);
        if (mark == ADAMAS_MARK_CLOSING) {
            /* Scope закончился нормально: ответ тела пережидает кадром
             * `CLOSED`, а деструктор бежит **на этом же стеке** - его операция
             * достаёт живые хендлеры внизу (§10 вопрос 144). Подавления тут
             * нет: хендлеры под scope'ом живы и ответа ещё не давали. */
            adamas_frame *closed = adamas_kont_push(kont, ADAMAS_MARK_CLOSED, 0, NULL,
                                                    closed_release, 1, NULL);
            closed->env[0] = value;
            adamas_value closer = frame->env[0];
            value = adamas_apply(closer, frame->evidence, kont, adamas_unit());
            frame_free(frame, kont);
            continue;
        }
        if (mark == ADAMAS_MARK_CLOSED) {
            /* Деструктор договорил: его `()` дропается, ответ scope идёт
             * дальше - оно и есть значение тела. */
            adamas_drop(value, NULL);
            value = frame->env[0];
            frame->env[0] = adamas_unit();
            frame_free(frame, kont);
            continue;
        }
        if (mark == ADAMAS_MARK_UNWINDING) {
            value = unwind_step(kont, frame, value);
            continue;
        }
        if (frame->code != NULL) {
            /* Код вправе положить новые кадры: они и станут вершиной, а ответ
             * пойдёт им. */
            value = frame->code(frame, value);
        }
        frame_free(frame, kont);
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
        /* Ресурсы под мультишотом запрещены статически (§10 вопрос 15), и кадр
         * раскрутки в копируемый сегмент не попадает. Владение остатком
         * цепочки при копии делить нечем, поэтому отказ здесь, а не молчание. */
        if (adamas_frame_mark(source) == ADAMAS_MARK_UNWINDING) {
            adamas_fail("сегмент раскрутки не копируется: ресурс под мультишотом");
        }
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

void adamas_segment_unwind(adamas_kont *kont, adamas_segment *segment) {
    unwind_push(kont, segment, adamas_unit(), 0);
}

adamas_value adamas_kont_abort(adamas_kont *kont) {
    /* Обрыв и раскрутка - одно и то же действие над разными цепочками: там
     * вырезанный сегмент, здесь кадры оборванного кода. Граница - ближайший
     * кадр `UNWINDING`: ниже стоит раскрутка, которая этот код и запустила, и
     * она продолжится сама. Вне раскрутки границы нет, и снимается весь стек -
     * прежнее правило как частный случай. */
    adamas_frame *cursor = kont->top;
    adamas_frame *last = NULL;
    size_t depth = 0;
    while (cursor != NULL && adamas_frame_mark(cursor) != ADAMAS_MARK_UNWINDING) {
        last = cursor;
        depth += 1;
        cursor = cursor->below;
    }
    if (depth == 0) {
        return adamas_unit();
    }
    adamas_segment *chain = segment_alloc(kont->top, last, depth);
    kont->top = cursor;
    kont->depth -= depth;
    last->below = NULL;
    unwind_push(kont, chain, adamas_unit(), 0);
    return adamas_unit();
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

void adamas_resumption_drop(adamas_kont *kont, adamas_value value) {
    adamas_segment *segment = adamas_segment_of(value);
    adamas_header *header = adamas_header_of(segment);
    if (header->rc == 0) {
        /* §3.4: дроп разматывает приостановленный сегмент, выполняя деструкторы
         * кадров внутри него. Резумпция аффинна, поэтому путь этот обычный, а
         * не крайний. Размотка кладётся кадром - точка приостановки (шапка
         * `adamas.h`): деструкторы выполнит `adamas_kont_run`. */
        adamas_segment_unwind(kont, segment);
        return;
    }
    header->rc -= 1;
}

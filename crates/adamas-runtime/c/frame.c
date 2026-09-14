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
    /* Ветки хендлера; у прочих кадров `NULL`. Отдельным полем, а не
     * объединением с `code`: код спрашивает `adamas_kont_run` у всякого кадра. */
    adamas_handler_code branches;
    adamas_frame_release release;
    adamas_evidence *evidence;
    uint32_t label;
    /* Слотов всего и сколько первых из них счётные. Двумя половинами слова, а
     * не двумя словами: среда обязана остаться на 56-м байте, а плоский слот
     * дупать нельзя - заголовка у него нет (§4.11). */
    uint16_t fields;
    uint16_t counted;
    adamas_value env[];
};

struct adamas_segment {
    adamas_header header;
    adamas_frame *top;
    adamas_frame *base;
};

/* Смещения закреплены: числа эти уезжают от перестановки полей молча, а Фаза 7
 * ставит по ним `align` и `dereferenceable` (шапка `adamas.h`, «Выравнивание»). */
_Static_assert(offsetof(struct adamas_frame, env) == 56, "среда кадра идёт с 56-го байта");
_Static_assert(sizeof(struct adamas_segment) == 24, "сегмент - три слова");

static adamas_frame *frame_alloc(uint16_t mark, uint32_t label, adamas_frame_code code,
                                 adamas_handler_code branches, adamas_frame_release release,
                                 size_t fields, size_t counted, adamas_evidence *evidence) {
    if (fields > UINT16_MAX || counted > fields) {
        adamas_fail("среда кадра: слотов больше, чем кадр умеет носить");
    }
    adamas_frame *frame = (adamas_frame *)adamas_block_alloc(sizeof(adamas_frame) +
                                                             fields * sizeof(adamas_value));
    adamas_header *header = adamas_header_of(frame);
    header->rc = 0;
    header->tag = mark;
    header->flags = 0;
    frame->below = NULL;
    frame->code = code;
    frame->branches = branches;
    frame->release = release;
    frame->evidence = adamas_evidence_dup(evidence);
    frame->label = label;
    frame->fields = (uint16_t)fields;
    frame->counted = (uint16_t)counted;
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
        uint16_t mark = adamas_frame_mark(below);
        /* Кадр питомника подавляется наравне с хендлером, и по тому же счёту:
         * деструктор бежит на стеке того, кто раскручивает, а брошенного кадра
         * там нет - резать по нему уступку было бы разрезом чужого стека.
         * Поиск питомника подавленную запись пропускает и идёт наружу
         * (`adamas_nursery_serves`), то есть находит круг, который жив. */
        if (mark == ADAMAS_MARK_HANDLER || mark == ADAMAS_MARK_NURSERY) {
            adamas_evidence_suppress(evidence, below);
        }
    }
    return evidence;
}

/* Длина цепочки. Считается обходом и **не хранится**: единственные её читатели
 * - диагностика и свидетели, а разрез с возобновлением обязаны быть за
 * постоянное время (см. `adamas_kont_cut`). */
static size_t chain_depth(const adamas_frame *top) {
    size_t depth = 0;
    for (const adamas_frame *frame = top; frame != NULL; frame = frame->below) {
        depth += 1;
    }
    return depth;
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
        return adamas_unit();
    }
    if (mark == ADAMAS_MARK_NURSERY) {
        /* Питомник внутри сегмента: его файберы брошены вместе с ним, а
         * сегменты их лежат в круге и в эту цепочку не входят - поэтому
         * `CLOSING` внутри уступившей задачи не отрабатывал бы никогда (у
         * машины это ревью 2026-09-07: `[1]` вместо `[1, 7]`).
         *
         * Берётся по одному, и кадр возвращается в остаток: снятый из круга
         * обратно не кладётся, поэтому обход конечен. Раскрутка брошенного
         * бежит **первой** - её кадр ложится выше остатка. */
        adamas_segment *parked = adamas_nursery_abandoned(next);
        if (parked != NULL) {
            next->below = chain->top;
            chain->top = next;
            unwind_push(kont, chain, held, 1);
            unwind_push(kont, parked, adamas_unit(), 1);
            return adamas_unit();
        }
        unwind_push(kont, chain, held, 1);
        frame_free(next, kont);
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

static adamas_segment *segment_alloc(adamas_frame *top, adamas_frame *base) {
    adamas_segment *segment = (adamas_segment *)adamas_block_alloc(sizeof(adamas_segment));
    adamas_header *header = adamas_header_of(segment);
    header->rc = 0;
    header->tag = ADAMAS_TAG_SEGMENT;
    header->flags = 0;
    segment->top = top;
    segment->base = base;
    return segment;
}

static void unwind_push(adamas_kont *kont, adamas_segment *chain, adamas_value held,
                        uint32_t captured) {
    adamas_frame *frame = adamas_kont_push(kont, ADAMAS_MARK_UNWINDING, captured, NULL,
                                           unwinding_release, 2, 2, NULL);
    frame->env[0] = held;
    frame->env[1] = adamas_segment_value(chain);
}

/* ------------------------------------------------------------------ */
/* Стек                                                                */
/* ------------------------------------------------------------------ */

void adamas_kont_init(adamas_kont *kont) {
    kont->top = NULL;
}

adamas_frame *adamas_kont_push(adamas_kont *kont, uint16_t mark, uint32_t label,
                               adamas_frame_code code, adamas_frame_release release, size_t fields,
                               size_t counted, const adamas_evidence *evidence) {
    /* Вектор здесь только берётся ссылкой, и `const` у входа - про место
     * вызова: у порождённого C он `const adamas_evidence *`, а приводить его
     * там значило бы писать приведение на каждой точке приостановки. */
    adamas_frame *frame = frame_alloc(mark, label, code, NULL, release, fields, counted,
                                      (adamas_evidence *)(uintptr_t)evidence);
    frame->below = kont->top;
    kont->top = frame;
    return frame;
}

adamas_frame *adamas_kont_handler(adamas_kont *kont, uint32_t label, adamas_handler_code branches,
                                  adamas_frame_release release, size_t fields,
                                  const adamas_evidence *evidence) {
    /* Вектор здесь только берётся ссылкой, и `const` у входа - про место
     * вызова: у порождённого C он `const adamas_evidence *`, а приводить его
     * там значило бы писать приведение в каждом хендлере. */
    /* Слоты хендлера все до одного указательные: среда веток есть захват, а
     * плоское понижение захватывать отказывается (`Lowerer::capturing`). */
    adamas_frame *frame = frame_alloc(ADAMAS_MARK_HANDLER, label, NULL, branches, release, fields,
                                      fields, (adamas_evidence *)(uintptr_t)evidence);
    frame->below = kont->top;
    kont->top = frame;
    return frame;
}

adamas_value adamas_frame_perform(adamas_frame *handler, adamas_kont *kont, uint32_t operation,
                                  adamas_value *arguments, size_t count) {
    if (handler == NULL || handler->branches == NULL) {
        adamas_fail("операция пришла к кадру без веток");
    }
    return handler->branches(handler, kont, operation, arguments, count);
}

adamas_value *adamas_frame_env(adamas_frame *frame) {
    return frame->env;
}

size_t adamas_frame_fields(const adamas_frame *frame) {
    return frame->fields;
}

size_t adamas_frame_counted(const adamas_frame *frame) {
    return frame->counted;
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

adamas_frame *adamas_kont_closing(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_frame_release release, adamas_value closer) {
    adamas_frame *frame = frame_alloc(ADAMAS_MARK_CLOSING, 0, NULL, NULL, release, 1, 1,
                                      (adamas_evidence *)(uintptr_t)evidence);
    frame->env[0] = closer;
    frame->below = kont->top;
    kont->top = frame;
    return frame;
}

adamas_value adamas_kont_run(adamas_kont *kont, adamas_value value) {
    return adamas_kont_run_to(kont, NULL, value);
}

adamas_value adamas_kont_run_to(adamas_kont *kont, adamas_frame *floor, adamas_value value) {
    while (kont->top != floor) {
        if (kont->top == NULL) {
            /* Пол не встретился: кадр, до которого крутили, сняли не мы. */
            adamas_fail("пол раскрутки не принадлежит этому стеку");
        }
        adamas_frame *frame = kont->top;
        kont->top = frame->below;
        frame->below = NULL;
        uint16_t mark = adamas_frame_mark(frame);
        if (mark == ADAMAS_MARK_CLOSING) {
            /* Scope закончился нормально: ответ тела пережидает кадром
             * `CLOSED`, а деструктор бежит **на этом же стеке** - его операция
             * достаёт живые хендлеры внизу (§10 вопрос 144). Подавления тут
             * нет: хендлеры под scope'ом живы и ответа ещё не давали. */
            adamas_frame *closed = adamas_kont_push(kont, ADAMAS_MARK_CLOSED, 0, NULL,
                                                    closed_release, 1, 1, NULL);
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
        if (mark == ADAMAS_MARK_NURSERY) {
            /* Файбер договорил: ответ его запоминается кругом, дальше идёт
             * следующий из очереди. Пустая очередь означает, что дожидаться
             * больше некого, и значение круга уходит вниз - тому, кто звал
             * `withNursery` (§5.2). */
            value = adamas_nursery_finished(kont, frame, value);
            frame_free(frame, kont);
            continue;
        }
        if (mark == ADAMAS_MARK_HANDLER) {
            /* Нормальный выход из хендлера: вычисление под ним договорило, и
             * его значение принимает ветка `return`. У дроблёного тела другого
             * пути нет вовсе - кадр хендлера стоит ниже кадров вычисления, и
             * значение доходит до него тем же трамплином, что и до прочих. */
            if (frame->branches != NULL) {
                value = frame->branches(frame, kont, ADAMAS_HANDLER_RETURN, &value, 1);
            }
            frame_free(frame, kont);
            continue;
        }
        if (frame->code != NULL) {
            /* Код вправе положить новые кадры: они и станут вершиной, а ответ
             * пойдёт им. */
            value = frame->code(frame, kont, value);
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
    /* Разрез идёт за постоянное время, и это **несущее** свойство, а не
     * экономия. Сегмент общей ветки растёт с глубиной рекурсии под хендлером;
     * обход по нему на каждой операции давал бы квадрат, ровно тот, из-за
     * которого у машины стек лежит звеньями (§10 вопрос 94). Прежняя редакция
     * обходила сегмент ради его длины с доводом «копирование и раскрутка стоят
     * столько же»; довод верен для мультишота и абортивной ветки и неверен для
     * одношота общего вида, где возобновление есть перекладывание указателей.
     * Мерено: 17/53/164/921 мс на 3200/6400/12800/25600 операций до правки.
     *
     * Кадр хендлера приходит из вектора evidence, поэтому поиска здесь нет
     * (§3.4), а проверки принадлежности стеку - тоже: она и была тем обходом. */
    adamas_segment *segment = segment_alloc(kont->top, handler);
    kont->top = handler->below;
    handler->below = NULL;
    return segment;
}

void adamas_kont_restore(adamas_kont *kont, adamas_segment *segment) {
    segment->base->below = kont->top;
    kont->top = segment->top;
    /* Ручка потреблена: сегмент снова часть стека, и второго владельца у него
     * нет. Мультишот восстанавливает копию, а не этот же сегмент. */
    adamas_block_free(segment);
}

void adamas_kont_resume(adamas_kont *kont, adamas_value value) {
    adamas_segment *segment = adamas_segment_of(value);
    if (segment->top == NULL) {
        /* Аффинность резумпции держат типы (§3.3): второе возобновление сюда
         * попасть может только дефектом понижения, и молчать о нём нечем. */
        adamas_fail("резумпция возобновлена дважды");
    }
    adamas_header *header = adamas_header_of(segment);
    if ((header->flags & ADAMAS_FLAG_MULTI) != 0 && header->rc != 0) {
        /* Мультишот: на ручку есть ещё ссылки, значит второе возобновление
         * впереди - ставится **копия**, и она же есть цена §3.4, O(глубины) на
         * resume. Единственная ссылка копии не требует: возобновить сегмент
         * второй раз некому, и он отдаётся сам - тот же договор об
         * уникальности, что у reuse (§5.1). N возобновлений - N-1 копий. */
        adamas_kont_restore(kont, adamas_segment_copy(segment));
        return;
    }
    segment->base->below = kont->top;
    kont->top = segment->top;
    /* Ручка **тратится**, а не освобождается: ссылок на неё бывает больше
     * одной - замыкание `\s -> resume v s` держит её наравне с вызывающим, - и
     * блок отдаст последняя. Пустая ручка раскручивать нечего. */
    segment->top = NULL;
    segment->base = NULL;
}

size_t adamas_segment_depth(const adamas_segment *segment) {
    return chain_depth(segment->top);
}

size_t adamas_kont_depth(const adamas_kont *kont) {
    return chain_depth(kont->top);
}

adamas_frame *adamas_segment_base(adamas_segment *segment) {
    return segment->base;
}

/* Переписывает записи, называющие `from`, на `to` во всех копиях выше него.
 *
 * Вектор у копии свой (см. `adamas_segment_copy`), поэтому правка идёт по
 * месту. Одного и того же вектора это касается один раз: второй проход не
 * находит `from` уже ни в одной записи. */
static void rebind_above(adamas_frame *top, const adamas_frame *until, const adamas_frame *from,
                         adamas_frame *to) {
    for (adamas_frame *frame = top; frame != until; frame = frame->below) {
        adamas_evidence_rebind(frame->evidence, from, to);
    }
}

adamas_segment *adamas_segment_copy(const adamas_segment *segment) {
    adamas_frame *source = segment->top;
    adamas_frame *previous = NULL;
    adamas_frame *first = NULL;
    /* Общий вектор копируется один раз на всю цепочку звеньев, которые его
     * делят: под одним хендлером у всех кадров он один и тот же указатель -
     * вторая форма передаёт его по вызовам без изменений. Это и держит цену
     * копии линейной по глубине, а не по глубине на длину вектора. */
    adamas_evidence *shared_source = NULL;
    adamas_evidence *shared_copy = NULL;
    while (source != NULL) {
        /* Ресурсы под мультишотом запрещены статически (§10 вопрос 15), и кадр
         * раскрутки в копируемый сегмент не попадает. Владение остатком
         * цепочки при копии делить нечем, поэтому отказ здесь, а не молчание. */
        if (adamas_frame_mark(source) == ADAMAS_MARK_UNWINDING) {
            adamas_fail("сегмент раскрутки не копируется: ресурс под мультишотом");
        }
        adamas_evidence *evidence;
        if (source->evidence != NULL && source->evidence == shared_source) {
            evidence = adamas_evidence_dup(shared_copy);
        } else {
            /* Свой, а не общий с оригиналом: записи о скопированных хендлерах
             * придётся переписать, и правка общего задела бы оригинал. */
            evidence = adamas_evidence_copy(source->evidence);
            shared_source = source->evidence;
            shared_copy = evidence;
        }
        adamas_frame *copy =
            frame_alloc(adamas_frame_mark(source), source->label, source->code, source->branches,
                        source->release, source->fields, source->counted, NULL);
        /* Вектор ставится своей ссылкой: `frame_alloc` дупнул бы чужой. */
        copy->evidence = evidence;
        for (uint16_t index = 0; index < source->counted; index += 1) {
            adamas_value slot = adamas_dup(source->env[index]);
            /* Одношотная резумпция внутри мультишотного участка достаётся
             * каждому проходу: потратив её первым, второй получил бы пустой
             * сегмент. Ровно этот дефект машина закрыла признаком `multishot`
             * (`eval/multi-over-oneshot`). */
            if (!adamas_is_imm(slot) && adamas_tag(slot) == ADAMAS_TAG_SEGMENT) {
                adamas_header_of(slot)->flags |= ADAMAS_FLAG_MULTI;
            }
            copy->env[index] = slot;
        }
        for (uint16_t index = source->counted; index < source->fields; index += 1) {
            /* Плоский слот - биты (§4.11): дупать в нём нечего. */
            copy->env[index] = source->env[index];
        }
        if (previous == NULL) {
            first = copy;
        } else {
            previous->below = copy;
        }
        if (adamas_frame_mark(source) == ADAMAS_MARK_HANDLER) {
            /* Запись вектора называет кадр, а у копии он свой. Переписываются
             * только копии **выше** хендлера: ниже его записи нет по построению
             * - вектор с ней родился на входе в хендлер. */
            rebind_above(first, copy, source, copy);
        }
        previous = copy;
        source = source->below;
    }
    return segment_alloc(first, previous);
}

adamas_value adamas_segment_multi(adamas_value resumption) {
    adamas_header_of(adamas_segment_of(resumption))->flags |= ADAMAS_FLAG_MULTI;
    return resumption;
}

void adamas_segment_unwind(adamas_kont *kont, adamas_segment *segment) {
    unwind_push(kont, segment, adamas_unit(), 0);
}

void adamas_segment_unwind_holding(adamas_kont *kont, adamas_segment *segment, adamas_value held) {
    unwind_push(kont, segment, held, 1);
}

adamas_value adamas_kont_abort(adamas_kont *kont) {
    /* Обрыв и раскрутка - одно и то же действие над разными цепочками: там
     * вырезанный сегмент, здесь кадры оборванного кода. Граница - ближайший
     * кадр `UNWINDING`: ниже стоит раскрутка, которая этот код и запустила, и
     * она продолжится сама. Вне раскрутки границы нет, и снимается весь стек -
     * прежнее правило как частный случай. */
    adamas_frame *cursor = kont->top;
    adamas_frame *last = NULL;
    while (cursor != NULL && adamas_frame_mark(cursor) != ADAMAS_MARK_UNWINDING) {
        last = cursor;
        cursor = cursor->below;
    }
    if (last == NULL) {
        return adamas_unit();
    }
    adamas_segment *chain = segment_alloc(kont->top, last);
    kont->top = cursor;
    last->below = NULL;
    unwind_push(kont, chain, adamas_unit(), 0);
    return adamas_unit();
}

void adamas_segment_disown_base(adamas_segment *segment) {
    if (segment->base == NULL) {
        return;
    }
    /* Метка снимается, кадр остаётся: вектор деструктора внутри сегмента его
     * называет, и снятый оставил бы висячий указатель. Работы у кадра нет
     * вовсе - раскрутка пройдёт его как обычное звено и освободит в свой
     * черёд, отпустив вместе с ним и ссылку на круг. */
    adamas_header_of(segment->base)->tag = ADAMAS_MARK_PLAIN;
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
    if (header->rc != 0) {
        header->rc -= 1;
        return;
    }
    if (segment->top == NULL) {
        /* Потраченная: звенья уже стоят на стеке, раскручивать нечего. */
        adamas_block_free(segment);
        return;
    }
    /* §3.4: дроп разматывает приостановленный сегмент, выполняя деструкторы
     * кадров внутри него. Резумпция аффинна, поэтому путь этот обычный, а не
     * крайний. Размотка кладётся кадром - точка приостановки (шапка
     * `adamas.h`): деструкторы выполнит `adamas_kont_run`. */
    adamas_segment_unwind(kont, segment);
}

void adamas_segment_abandon(adamas_value value) {
    adamas_segment *segment = adamas_segment_of(value);
    if (segment->top == NULL) {
        return;
    }
    /* Корень свой: `adamas_release` о стеке не знает по своей сигнатуре.
     * Деструкторы поэтому бегут здесь же, а не откладываются кадром, - точки
     * приостановки у этого пути нет вовсе. */
    adamas_kont local;
    adamas_kont_init(&local);
    adamas_segment *chain = segment_alloc(segment->top, segment->base);
    segment->top = NULL;
    segment->base = NULL;
    unwind_push(&local, chain, adamas_unit(), 0);
    adamas_drop(adamas_kont_run(&local, adamas_unit()), NULL);
}

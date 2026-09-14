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
 */

#include "adamas.h"

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
    /** Ответ корневого файбера, когда он договорил. */
    adamas_value result;
    /** Кто бежит сейчас. */
    uint32_t running;
    /** Следующий свободный номер файбера. */
    uint32_t next;
    /** Ссылок сверх одной: кадры `NURSERY` и имена файберов. */
    uint32_t refs;
    /** Корневой ли бежит. */
    int rooted;
    /** Есть ли ответ корневого. */
    int answered;
    /** Отпущена ли ссылка «круг открыт». */
    int closed;
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
/* Владение кругом                                                     */
/* ------------------------------------------------------------------ */

static void nursery_unref(adamas_nursery *nursery) {
    if (nursery->refs == 0) {
        adamas_evidence_drop(nursery->base);
        adamas_block_free(nursery);
        return;
    }
    nursery->refs -= 1;
}

/* Круг договорил: содержимое больше не нужно, ссылка «открыт» отпускается.
 * Идемпотентно - раскрутка добирается сюда с каждого кадра `NURSERY`. */
static void nursery_close(adamas_nursery *nursery) {
    if (nursery->closed) {
        return;
    }
    nursery->closed = 1;
    nursery_unref(nursery);
}

/* Дроп среды кадра питомника: сам круг лежит в нулевом слоте несчётным. */
static void nursery_frame_release(adamas_frame *frame, adamas_kont *kont) {
    (void)kont;
    nursery_unref((adamas_nursery *)(void *)adamas_frame_env(frame)[0]);
}

static adamas_nursery *nursery_of(adamas_frame *frame) {
    if (adamas_frame_fields(frame) < 1) {
        adamas_fail("кадр питомника без круга в среде");
    }
    return (adamas_nursery *)(void *)adamas_frame_env(frame)[0];
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

/* Ответ договорившего владением; `found` - нашёлся ли он вообще. */
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
static adamas_value nursery_start(adamas_kont *kont, adamas_nursery *nursery, adamas_value body) {
    adamas_frame *frame =
        adamas_kont_push(kont, ADAMAS_MARK_NURSERY, 0, NULL, nursery_frame_release, 1, 0,
                         nursery->base);
    adamas_evidence *inner;
    adamas_frame *starter;
    adamas_value *env;
    adamas_frame_env(frame)[0] = (adamas_value)(void *)nursery;
    nursery->refs += 1;
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

/* Следующий файбер очереди либо ответ питомника, если её больше нет. */
static adamas_value nursery_step(adamas_kont *kont, adamas_nursery *nursery) {
    adamas_fiber *next = queue_pop(nursery);
    if (next == NULL) {
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
    nursery->running = next->id;
    nursery->rooted = next->root;
    if (next->fresh) {
        adamas_value body = next->body;
        next->body = adamas_unit();
        fiber_free(nursery, next);
        return nursery_start(kont, nursery, body);
    }
    adamas_kont_restore(kont, next->segment);
    {
        adamas_value answer = next->answer;
        next->answer = adamas_unit();
        next->segment = NULL;
        fiber_free(nursery, next);
        return answer;
    }
}

/* Снимает бегущий файбер со стека и кладёт его сегмент при нём. */
static adamas_fiber *parked(adamas_nursery *nursery, adamas_segment *segment,
                            adamas_value answer) {
    adamas_fiber *fiber = fiber_alloc(nursery->running, nursery->rooted);
    fiber->segment = segment;
    fiber->answer = answer;
    return fiber;
}

adamas_value adamas_nursery_begin(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_value body, adamas_release release) {
    adamas_nursery *nursery = (adamas_nursery *)adamas_block_alloc(sizeof(adamas_nursery));
    nursery->ready = NULL;
    nursery->last = NULL;
    nursery->blocked = NULL;
    nursery->done = NULL;
    nursery->base = adamas_evidence_dup((adamas_evidence *)(uintptr_t)evidence);
    nursery->release = release;
    nursery->result = adamas_unit();
    nursery->running = 0;
    nursery->next = 1;
    nursery->refs = 0;
    nursery->rooted = 1;
    nursery->answered = 0;
    nursery->closed = 0;
    return nursery_start(kont, nursery, body);
}

adamas_value adamas_nursery_suspend(adamas_kont *kont, const adamas_evidence *evidence) {
    adamas_frame *frame = nursery_frame(evidence);
    adamas_nursery *nursery = nursery_of(frame);
    /* Сегмент включает сам кадр питомника - тем же приёмом, что у хендлера. */
    adamas_segment *segment = adamas_kont_cut(kont, frame);
    queue_push(nursery, parked(nursery, segment, adamas_unit()));
    return nursery_step(kont, nursery);
}

adamas_value adamas_nursery_spawn(adamas_kont *kont, const adamas_evidence *evidence,
                                  adamas_value body, uint32_t tag, uint32_t slots, uint32_t at) {
    adamas_frame *frame = nursery_frame(evidence);
    adamas_nursery *nursery = nursery_of(frame);
    adamas_fiber *fiber = fiber_alloc(nursery->next, 0);
    adamas_value task;
    uint32_t slot;
    (void)kont;
    nursery->next += 1;
    fiber->fresh = 1;
    fiber->body = body;
    queue_push(nursery, fiber);
    if (tag == ADAMAS_NO_TASK) {
        return adamas_unit();
    }
    task = adamas_alloc((uint16_t)tag, slots);
    for (slot = 0; slot < slots; slot += 1) {
        adamas_set_field(task, slot, adamas_unit());
    }
    adamas_set_field(task, at, fiber_name(nursery, fiber->id));
    return task;
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
    ready = done_take(nursery, awaited, &found);
    if (found) {
        return ready;
    }
    segment = adamas_kont_cut(kont, frame);
    waiting = parked(nursery, segment, adamas_unit());
    waiting->awaited = awaited;
    waiting->next = nursery->blocked;
    nursery->blocked = waiting;
    return nursery_step(kont, nursery);
}

adamas_value adamas_nursery_finished(adamas_kont *kont, adamas_frame *frame, adamas_value value) {
    adamas_nursery *nursery = nursery_of(frame);
    uint32_t id = nursery->running;
    adamas_fiber *waiting = nursery->blocked;
    adamas_fiber *keep = NULL;
    if (nursery->rooted) {
        nursery->result = adamas_dup(value);
        nursery->answered = 1;
    }
    /* Ждавшие его возвращаются в круг: чужой ответ готов - и он же становится
     * тем, чем возобновление им ответит. Единицу тут положить нельзя: `await`
     * объявлен отдающим `a` задачи (§5.2). */
    while (waiting != NULL) {
        adamas_fiber *fiber = waiting;
        waiting = waiting->next;
        if (fiber->awaited == id) {
            adamas_drop(fiber->answer, nursery->release);
            fiber->answer = adamas_dup(value);
            queue_push(nursery, fiber);
        } else {
            fiber->next = keep;
            keep = fiber;
        }
    }
    nursery->blocked = keep;
    done_push(nursery, id, value);
    return nursery_step(kont, nursery);
}

adamas_segment *adamas_nursery_abandoned(adamas_frame *frame) {
    adamas_nursery *nursery = nursery_of(frame);
    adamas_fiber *fiber;
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
    int found;
    if (name == NULL) {
        return task;
    }
    nursery = name->home;
    /* Ответ договорившего никому не достанется: снимается с готовых. */
    adamas_drop(done_take(nursery, name->id, &found), nursery->release);
    fiber = fiber_take(nursery, name->id);
    if (fiber == NULL) {
        /* Файбер не найден: договорил либо бежит сам, и снимать со стека
         * нечего. */
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

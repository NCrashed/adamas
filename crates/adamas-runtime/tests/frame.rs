//! Кадры, сегмент продолжения, мультишот и раскрутка.
//!
//! Проверяется семантика, которую понижение обязано повторить за машиной
//! интерпретатора (`adamas-interp/src/frame.rs`): порядок работы сверху вниз,
//! копирование звеньев под мультишот, деструкторы раскрутки в порядке LIFO.

#![allow(unsafe_code)]

use std::cell::RefCell;
use std::ptr;

use adamas_runtime::ffi::{
    Evidence, Frame, HANDLER_RETURN, Kont, LOOKUP_HANDLER, LOOKUP_MISSING, LOOKUP_SUPPRESSED,
    MARK_CLOSING, MARK_HANDLER, MARK_PLAIN, Value, adamas_alloc, adamas_closure,
    adamas_closure_get, adamas_closure_release, adamas_closure_set, adamas_drop, adamas_dup,
    adamas_evidence_at, adamas_evidence_drop, adamas_evidence_empty, adamas_evidence_extend,
    adamas_evidence_lookup, adamas_evidence_mask, adamas_field, adamas_frame_env,
    adamas_frame_evidence, adamas_frame_fields, adamas_frame_label, adamas_frame_mark,
    adamas_frame_perform, adamas_imm, adamas_imm_get, adamas_kont_abort, adamas_kont_cut,
    adamas_kont_depth, adamas_kont_handler, adamas_kont_init, adamas_kont_push,
    adamas_kont_restore, adamas_kont_resume, adamas_kont_run, adamas_rc, adamas_resumption_drop,
    adamas_segment_abandon, adamas_segment_base, adamas_segment_copy, adamas_segment_depth,
    adamas_segment_unwind, adamas_segment_value, adamas_set_field, adamas_stat_live,
    adamas_stat_reset, adamas_unit,
};

thread_local! {
    /// Отметки сработавших деструкторов в порядке срабатывания.
    static TRACE: RefCell<Vec<isize>> = const { RefCell::new(Vec::new()) };
    /// Вердикты поиска хендлера изнутри деструктора.
    static VERDICTS: RefCell<Vec<i32>> = const { RefCell::new(Vec::new()) };
    /// Глубины сегментов, вырезанных изнутри деструктора (§10 вопрос 144).
    static SEIZED: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

/// Пустой стек.
fn kont() -> Kont {
    let mut kont = Kont {
        top: ptr::null_mut(),
    };
    unsafe { adamas_kont_init(&raw mut kont) };
    kont
}

/// Число, лежащее в объекте: копирование сегмента обязано его `dup`-нуть.
unsafe fn boxed(number: isize) -> Value {
    unsafe {
        let value = adamas_alloc(0, 1);
        adamas_set_field(value, 0, adamas_imm(number));
        value
    }
}

/// Прибавляет к пришедшему число из среды.
unsafe extern "C" fn adding(frame: *mut Frame, _kont: *mut Kont, incoming: Value) -> Value {
    unsafe {
        let held = *adamas_frame_env(frame);
        adamas_imm(adamas_imm_get(incoming) + adamas_imm_get(adamas_field(held, 0)))
    }
}

/// Умножает пришедшее на число из среды.
unsafe extern "C" fn scaling(frame: *mut Frame, _kont: *mut Kont, incoming: Value) -> Value {
    unsafe {
        let held = *adamas_frame_env(frame);
        adamas_imm(adamas_imm_get(incoming) * adamas_imm_get(adamas_field(held, 0)))
    }
}

/// Дроп среды кадра: один слот с объектом.
unsafe extern "C" fn release_held(frame: *mut Frame, _kont: *mut Kont) {
    unsafe {
        adamas_drop(*adamas_frame_env(frame), None);
    }
}

/// Дроп среды кадра: один слот с замыканием.
unsafe extern "C" fn release_closer(frame: *mut Frame, _kont: *mut Kont) {
    unsafe {
        adamas_drop(*adamas_frame_env(frame), Some(adamas_closure_release));
    }
}

/// Дроп среды кадра: один слот с резумпцией. Ручка стека - место, куда её
/// дроп кладёт размотку кадром.
unsafe extern "C" fn release_resumption(frame: *mut Frame, kont: *mut Kont) {
    unsafe {
        adamas_resumption_drop(kont, *adamas_frame_env(frame));
    }
}

/// Деструктор, отмечающийся в следе.
unsafe extern "C" fn note(
    closure: Value,
    _evidence: *const Evidence,
    _kont: *mut Kont,
    argument: Value,
) -> Value {
    unsafe {
        let mark = adamas_imm_get(adamas_closure_get(closure, 0));
        TRACE.with_borrow_mut(|trace| trace.push(mark));
        adamas_drop(argument, None);
        adamas_unit()
    }
}

/// Замыкание-деструктор с отметкой.
unsafe fn closer(mark: isize) -> Value {
    unsafe {
        let closure = adamas_closure(Some(note), None, 1, 1);
        adamas_closure_set(closure, 0, adamas_imm(mark));
        closure
    }
}

/// Отложенная работа: при обрыве она **не** выполняется, в отличие от scope'а.
unsafe extern "C" fn noting(frame: *mut Frame, _kont: *mut Kont, incoming: Value) -> Value {
    unsafe {
        let mark = adamas_imm_get(*adamas_frame_env(frame));
        TRACE.with_borrow_mut(|trace| trace.push(mark));
        incoming
    }
}

/// Деструктор второй формы, производящий операцию, - то, что напишет понижение.
///
/// Откладывает работу (метка 77), открывает свой scope (метка 8), спрашивает
/// метки 7 и 9 и записывает вердикты. На `SUPPRESSED` зовёт `adamas_kont_abort`
/// со своим стеком и возвращает его ответ немедленно: своё завершение он не
/// отмечает, вместо отметки идёт отрицательная. На `HANDLER` договаривает как
/// обычно, и стек его доигрывается до конца.
///
/// Отложенная работа и scope различают обрыв и доигрывание: §3.3 обещает
/// деструкторы у оборванного, но не обещает доделать то, ради чего он бежал.
unsafe extern "C" fn probing(
    closure: Value,
    evidence: *const Evidence,
    kont: *mut Kont,
    argument: Value,
) -> Value {
    unsafe {
        let mark = adamas_imm_get(adamas_closure_get(closure, 0));
        adamas_drop(argument, None);
        let deferred = adamas_kont_push(
            kont,
            MARK_PLAIN,
            0,
            Some(noting),
            None,
            1,
            1,
            evidence.cast_mut(),
        );
        *adamas_frame_env(deferred) = adamas_imm(77);
        push_closing(kont, 8, evidence.cast_mut());

        let seven = adamas_evidence_lookup(evidence, 7, ptr::null_mut());
        let nine = adamas_evidence_lookup(evidence, 9, ptr::null_mut());
        // Внешний одноимённый - за маской, то есть под вектором без ближайшей
        // записи метки 7.
        let past = adamas_evidence_mask(evidence, 7);
        let outer = adamas_evidence_lookup(past, 7, ptr::null_mut());
        adamas_evidence_drop(past);
        VERDICTS.with_borrow_mut(|verdicts| verdicts.extend([seven, nine, outer]));

        if seven == LOOKUP_SUPPRESSED {
            let answer = adamas_kont_abort(kont);
            TRACE.with_borrow_mut(|trace| trace.push(-mark));
            return answer;
        }
        TRACE.with_borrow_mut(|trace| trace.push(mark));
        adamas_unit()
    }
}

/// Кадр с числом в среде.
unsafe fn push_holding(
    kont: *mut Kont,
    mark: u16,
    code: unsafe extern "C" fn(*mut Frame, *mut Kont, Value) -> Value,
    number: isize,
    evidence: *mut Evidence,
) -> *mut Frame {
    unsafe {
        let frame = adamas_kont_push(
            kont,
            mark,
            0,
            Some(code),
            Some(release_held),
            1,
            1,
            evidence,
        );
        *adamas_frame_env(frame) = boxed(number);
        frame
    }
}

/// Кадр scope'а с деструктором.
unsafe fn push_closing(kont: *mut Kont, mark: isize, evidence: *mut Evidence) -> *mut Frame {
    unsafe {
        let frame = adamas_kont_push(
            kont,
            MARK_CLOSING,
            0,
            None,
            Some(release_closer),
            1,
            1,
            evidence,
        );
        *adamas_frame_env(frame) = closer(mark);
        frame
    }
}

/// Кадр scope'а, чей деструктор производит операцию.
unsafe fn push_probing(kont: *mut Kont, mark: isize, evidence: *mut Evidence) -> *mut Frame {
    unsafe {
        let frame = adamas_kont_push(
            kont,
            MARK_CLOSING,
            0,
            None,
            Some(release_closer),
            1,
            1,
            evidence,
        );
        let closure = adamas_closure(Some(probing), None, 1, 1);
        adamas_closure_set(closure, 0, adamas_imm(mark));
        *adamas_frame_env(frame) = closure;
        frame
    }
}

#[test]
fn cut_takes_everything_up_to_the_handler() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        let bottom = adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, 0, evidence);
        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 3, None, None, 0, 0, evidence);
        adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, 0, evidence);
        adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, 0, evidence);
        assert_eq!(adamas_kont_depth(&raw const kont), 4);

        let segment = adamas_kont_cut(&raw mut kont, handler);
        // Сегмент включает сам кадр хендлера: возобновление ставит его обратно,
        // и это и значит «глубокий».
        assert_eq!(adamas_segment_depth(segment), 3);
        assert_eq!(adamas_segment_base(segment), handler);
        assert_eq!(adamas_frame_mark(handler), MARK_HANDLER);
        assert_eq!(adamas_frame_label(handler), 3);
        assert_eq!(adamas_frame_fields(handler), 0);
        // Под разрезом стек цел.
        assert_eq!(adamas_kont_depth(&raw const kont), 1);
        assert_eq!(kont.top, bottom);

        adamas_segment_unwind(&raw mut kont, segment);
        adamas_kont_run(&raw mut kont, adamas_unit());
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn work_goes_from_the_top_of_the_stack_down() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        // Снизу вверх: прибавить 10, умножить на 2, прибавить 1. Метки все
        // обычные: у кадра хендлера работы нет вовсе - его дело быть найденным,
        // а значение вычисления уходит ветке `return`, а не коду кадра.
        push_holding(&raw mut kont, MARK_PLAIN, adding, 10, evidence);
        push_holding(&raw mut kont, MARK_PLAIN, scaling, 2, evidence);
        push_holding(&raw mut kont, MARK_PLAIN, adding, 1, evidence);

        // Вершина первая: (1 + 1) * 2 + 10. Обратный порядок дал бы 23.
        let answer = adamas_kont_run(&raw mut kont, adamas_imm(1));
        assert_eq!(adamas_imm_get(answer), 14);
        assert_eq!(adamas_kont_depth(&raw const kont), 0);
        assert!(kont.top.is_null());

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn a_copied_segment_resumes_twice_and_independently() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        // Основание сегмента - обычный кадр: резать `adamas_kont_cut` умеет по
        // любому, а работа у кадра хендлера не своя, а веток.
        let handler = push_holding(&raw mut kont, MARK_PLAIN, adding, 10, evidence);
        let scale = push_holding(&raw mut kont, MARK_PLAIN, scaling, 2, evidence);
        let ten = *adamas_frame_env(handler);
        let two = *adamas_frame_env(scale);
        let segment = adamas_kont_cut(&raw mut kont, handler);
        assert_eq!(adamas_segment_depth(segment), 2);

        let first = adamas_segment_copy(segment);
        let second = adamas_segment_copy(segment);
        // Звенья свои, поля общие: мультишот копирует, `dup`-ая (§3.4).
        assert_eq!(adamas_rc(ten), 2);
        assert_eq!(adamas_rc(two), 2);

        adamas_kont_restore(&raw mut kont, first);
        assert_eq!(adamas_kont_depth(&raw const kont), 2);
        assert_eq!(
            adamas_imm_get(adamas_kont_run(&raw mut kont, adamas_imm(1))),
            12
        );
        assert_eq!(adamas_rc(ten), 1);

        adamas_kont_restore(&raw mut kont, second);
        assert_eq!(
            adamas_imm_get(adamas_kont_run(&raw mut kont, adamas_imm(5))),
            20
        );
        assert_eq!(adamas_rc(ten), 0);

        // Оригинал цел и после двух возобновлений.
        assert_eq!(adamas_segment_depth(segment), 2);
        adamas_segment_unwind(&raw mut kont, segment);
        adamas_kont_run(&raw mut kont, adamas_unit());
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Копия переписывает вектор: запись называет **её** кадр хендлера.
///
/// Иначе операция под возобновлённой копией резала бы стек по кадру оригинала,
/// которого на стеке нет вовсе, - и снесла бы стек молча. Свидетель читает
/// вектор скопированного звена и требует от него кадр копии.
#[test]
fn a_copy_names_its_own_handler_in_the_vector() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        // Вектор вычисления под хендлером: запись называет его кадр.
        let under = adamas_evidence_extend(empty, 7, handler);
        let chunk = push_holding(&raw mut kont, MARK_PLAIN, adding, 10, under);
        assert_eq!(adamas_frame_evidence(chunk), under);

        let segment = adamas_kont_cut(&raw mut kont, handler);
        let copy = adamas_segment_copy(segment);
        let base = adamas_segment_base(copy);
        assert_ne!(base, handler, "основание копии - кадр оригинала");

        adamas_kont_restore(&raw mut kont, copy);
        let top = kont.top;
        let mut found: *mut Frame = ptr::null_mut();
        let verdict = adamas_evidence_lookup(adamas_frame_evidence(top), 7, &raw mut found);
        assert_eq!(verdict, LOOKUP_HANDLER);
        assert_eq!(found, base, "вектор копии называет кадр оригинала");
        // И вектор у копии свой: правка общего задела бы оригинал.
        assert_ne!(adamas_frame_evidence(top), under);
        assert_eq!(adamas_evidence_at(under, 0), handler);

        adamas_kont_run(&raw mut kont, adamas_imm(1));
        adamas_segment_unwind(&raw mut kont, segment);
        adamas_kont_run(&raw mut kont, adamas_unit());
        adamas_evidence_drop(under);
        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Плоский слот копия не дупает: счётчика у него нет вовсе (§4.11).
///
/// Кадр носит число **счётных** слотов рядом с числом слотов, счётные идут
/// первыми. Дупни копия всё подряд - и биты `40` поехали бы указателем: младший
/// бит нулевой, заголовка по этому адресу нет.
#[test]
fn a_copy_duplicates_only_the_counted_slots() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        let base = adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, 0, evidence);
        // Два слота, счётный один: второй - биты плоского значения.
        let frame = adamas_kont_push(
            &raw mut kont,
            MARK_PLAIN,
            0,
            None,
            Some(release_held),
            2,
            1,
            evidence,
        );
        let held = boxed(3);
        // Биты плоского `Int64`, как их кладёт порождённый C: 40 - чётное, то
        // есть непосредственным значением не притворяется и `adamas_dup` по нему
        // полез бы в заголовок по адресу 40.
        let bits: Value = std::ptr::without_provenance_mut(40);
        *adamas_frame_env(frame) = held;
        *adamas_frame_env(frame).add(1) = bits;
        assert_eq!(adamas_frame_fields(frame), 2);

        let segment = adamas_kont_cut(&raw mut kont, base);
        let copy = adamas_segment_copy(segment);
        // Счётный слот получил ссылку, плоский - те же биты и ни одной.
        assert_eq!(adamas_rc(held), 1);

        adamas_kont_restore(&raw mut kont, copy);
        assert_eq!(*adamas_frame_env(kont.top), held);
        assert_eq!((*adamas_frame_env(kont.top).add(1)).addr(), 40);

        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(adamas_rc(held), 0);
        adamas_segment_unwind(&raw mut kont, segment);
        adamas_kont_run(&raw mut kont, adamas_unit());
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Одношотная ручка в слоте копируемого звена достаётся **каждому** ходу.
///
/// Копия дупает слот, и с этого мгновения у сегмента два независимых владельца:
/// потрать его первый - второму досталась бы пустая ручка. Поэтому копия
/// помечает такие ручки мультишотными. Тот же дефект машина закрыла признаком
/// `multishot` (`eval/multi-over-oneshot`), и там он давал `[2, 2]` вместо
/// `[2, 4]` - второй проход не исполнялся вовсе.
///
/// Ответы ходов различны по построению: `1` и `5` на входе дают `12` и `20`.
#[test]
fn a_copy_makes_the_resumptions_in_its_slots_multishot() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        // Внутренний сегмент: в основании прибавить 10, сверху умножить на 2.
        let bottom = push_holding(&raw mut kont, MARK_PLAIN, adding, 10, evidence);
        push_holding(&raw mut kont, MARK_PLAIN, scaling, 2, evidence);
        let inner = adamas_segment_value(adamas_kont_cut(&raw mut kont, bottom));

        // Внешнее звено держит её слотом - так её носит дроблёное тело.
        let outer_base = adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, 0, evidence);
        let holder = adamas_kont_push(
            &raw mut kont,
            MARK_PLAIN,
            0,
            None,
            Some(release_resumption),
            1,
            1,
            evidence,
        );
        *adamas_frame_env(holder) = inner;
        let outer = adamas_kont_cut(&raw mut kont, outer_base);

        let copy = adamas_segment_copy(outer);
        assert_eq!(adamas_rc(inner), 1, "копия не взяла ссылки на ручку");

        // Первый ход: владельцев двое, возобновление ставит копию сегмента.
        adamas_kont_resume(&raw mut kont, inner);
        assert_eq!(
            adamas_imm_get(adamas_kont_run(&raw mut kont, adamas_imm(1))),
            12
        );

        // Оригинал внешнего сегмента умирает, и с ним одна из двух ссылок.
        adamas_segment_unwind(&raw mut kont, outer);
        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(adamas_rc(inner), 0);

        // Второй ход: ссылка последняя, копии не нужно - сегмент отдаётся сам.
        adamas_kont_resume(&raw mut kont, inner);
        assert_eq!(
            adamas_imm_get(adamas_kont_run(&raw mut kont, adamas_imm(5))),
            20
        );

        adamas_segment_unwind(&raw mut kont, copy);
        adamas_kont_run(&raw mut kont, adamas_unit());
        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn unwinding_runs_the_destructors_lifo() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, 0, evidence);
        push_closing(&raw mut kont, 1, evidence);
        push_closing(&raw mut kont, 2, evidence);
        push_closing(&raw mut kont, 3, evidence);

        let segment = adamas_kont_cut(&raw mut kont, handler);
        adamas_segment_unwind(&raw mut kont, segment);
        // Точка приостановки: деструкторы выполняет `adamas_kont_run`.
        adamas_kont_run(&raw mut kont, adamas_unit());
        // Изнутри наружу: последний вошедший scope закрывается первым (§3.4).
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![3, 2, 1]);

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn a_normal_exit_runs_the_destructor_and_keeps_the_value() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        push_closing(&raw mut kont, 1, evidence);
        push_closing(&raw mut kont, 2, evidence);

        // §3.3 требует деструктора при любом выходе, а ответ scope'а идёт мимо
        // него: деструктор отвечает `()`, и ответом это не становится.
        let answer = adamas_kont_run(&raw mut kont, adamas_imm(5));
        assert_eq!(adamas_imm_get(answer), 5);
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![2, 1]);

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn the_last_reference_to_a_resumption_unwinds_it() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, 0, evidence);
        push_closing(&raw mut kont, 1, evidence);
        let resumption = adamas_segment_value(adamas_kont_cut(&raw mut kont, handler));

        adamas_dup(resumption);
        adamas_resumption_drop(&raw mut kont, resumption);
        // Ссылка была лишняя - сегмент жив, деструктор молчит.
        assert!(TRACE.with_borrow(Vec::is_empty));

        adamas_resumption_drop(&raw mut kont, resumption);
        adamas_kont_run(&raw mut kont, adamas_unit());
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![1]);

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn an_abandoned_resumption_inside_a_segment_unwinds_too() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let evidence = adamas_evidence_empty();

        // Ветка хендлера, не позвавшая резумпцию: её сегмент мертвеет вместе с
        // тем, в котором лежит (интерпретатор ловит это ветвью `Frame::Branch`).
        let inner_handler =
            adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, 0, evidence);
        push_closing(&raw mut kont, 9, evidence);
        let inner = adamas_segment_value(adamas_kont_cut(&raw mut kont, inner_handler));

        let outer_handler =
            adamas_kont_push(&raw mut kont, MARK_HANDLER, 2, None, None, 0, 0, evidence);
        let holder = adamas_kont_push(
            &raw mut kont,
            MARK_PLAIN,
            0,
            None,
            Some(release_resumption),
            1,
            1,
            evidence,
        );
        *adamas_frame_env(holder) = inner;
        push_closing(&raw mut kont, 1, evidence);

        let outer = adamas_kont_cut(&raw mut kont, outer_handler);
        adamas_segment_unwind(&raw mut kont, outer);
        adamas_kont_run(&raw mut kont, adamas_unit());
        // Сперва свой деструктор, затем брошенная резумпция под ним: release
        // резумпции кладёт её размотку кадром выше остатка, и она бежит первой.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![1, 9]);

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Стек под оба теста подавления: снаружи живой хендлер метки 7, внутри
/// сегмента - хендлер той же метки и хендлер метки 9, над ними два scope'а.
///
/// Возвращает стек, кадр внешнего хендлера, кадр основания и четыре вектора,
/// которые вызывающий обязан дропнуть.
unsafe fn suppression_stack() -> (Kont, *mut Frame, *mut Frame, [*mut Evidence; 4]) {
    unsafe {
        let mut kont = kont();
        let empty = adamas_evidence_empty();
        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        let with_outer = adamas_evidence_extend(empty, 7, outer);
        let base = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, with_outer);
        let with_base = adamas_evidence_extend(with_outer, 7, base);
        let nine = adamas_kont_push(&raw mut kont, MARK_HANDLER, 9, None, None, 0, 0, with_base);
        let with_nine = adamas_evidence_extend(with_base, 9, nine);

        push_closing(&raw mut kont, 1, with_nine);
        push_probing(&raw mut kont, 2, with_nine);
        (kont, outer, base, [empty, with_outer, with_base, with_nine])
    }
}

#[test]
fn unwinding_suppresses_the_handlers_that_already_answered() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        VERDICTS.with_borrow_mut(Vec::clear);
        let (mut kont, outer, base, vectors) = suppression_stack();

        let doomed = adamas_kont_cut(&raw mut kont, base);
        // До прогона внешний хендлер на стеке один: раскрутка ещё кадром.
        assert_eq!(adamas_kont_depth(&raw const kont), 1);
        assert_eq!(kont.top, outer);
        adamas_segment_unwind(&raw mut kont, doomed);
        adamas_kont_run(&raw mut kont, adamas_unit());

        // Операция деструктора не достаётся ни своему хендлеру - тот ответ уже
        // дал, - ни хендлеру метки 9 под ним: оба брошены вместе с сегментом.
        // Внешний одноимённый при этом жив и достижим за маской: подавление
        // **помечает** запись, а не снимает её (ревью 2026-09-05).
        assert_eq!(
            VERDICTS.with_borrow(Clone::clone),
            vec![LOOKUP_SUPPRESSED, LOOKUP_SUPPRESSED, LOOKUP_HANDLER]
        );
        // Обрыв закрыл scope, открытый самим деструктором (8), - §3.3 требует
        // деструкторов и у оборванного, - но отложенную работу (77) не сделал:
        // обрыв не есть доигрывание. Отметка обрыва (-2) стоит раньше восьмёрки:
        // обрыв - точка приостановки, его раскрутку выполняет `adamas_kont_run`
        // после немедленного возврата, а у машины кода после обрыва нет вовсе -
        // это мёртвое продолжение. Раскрутка пошла дальше, и следующий scope
        // закрылся как обычно.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![-2, 8, 1]);

        for evidence in vectors {
            adamas_evidence_drop(evidence);
        }
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Деструктор, чья операция достаёт живой хендлер метки 7 **снаружи**
/// раскручиваемого сегмента (§10 вопрос 144): режет один стек до его кадра и
/// тут же возобновляет - эмуляция tail-resume ветки. Разрез забирает остаток
/// раскрутки кадром `UNWINDING`, и возобновление продолжает обе.
unsafe extern "C" fn reaching(
    closure: Value,
    evidence: *const Evidence,
    kont: *mut Kont,
    argument: Value,
) -> Value {
    unsafe {
        let mark = adamas_imm_get(adamas_closure_get(closure, 0));
        adamas_drop(argument, None);
        let mut handler: *mut Frame = ptr::null_mut();
        let verdict = adamas_evidence_lookup(evidence, 7, &raw mut handler);
        VERDICTS.with_borrow_mut(|verdicts| verdicts.push(verdict));
        if verdict == LOOKUP_HANDLER {
            let segment = adamas_kont_cut(kont, handler);
            SEIZED.with_borrow_mut(|seized| seized.push(adamas_segment_depth(segment)));
            adamas_kont_restore(kont, segment);
            TRACE.with_borrow_mut(|trace| trace.push(mark));
        }
        adamas_unit()
    }
}

/// Кадр scope'а, чей деструктор режет стек до живого внешнего хендлера.
unsafe fn push_reaching(kont: *mut Kont, mark: isize, evidence: *mut Evidence) -> *mut Frame {
    unsafe {
        let frame = adamas_kont_push(
            kont,
            MARK_CLOSING,
            0,
            None,
            Some(release_closer),
            1,
            1,
            evidence,
        );
        let closure = adamas_closure(Some(reaching), None, 1, 1);
        adamas_closure_set(closure, 0, adamas_imm(mark));
        *adamas_frame_env(frame) = closure;
        frame
    }
}

#[test]
fn a_destructors_operation_reaches_a_live_outer_handler() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        VERDICTS.with_borrow_mut(Vec::clear);
        SEIZED.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        // Живой хендлер метки 7 - снаружи будущего сегмента.
        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        let with_outer = adamas_evidence_extend(empty, 7, outer);
        // Основание сегмента - хендлер метки 9; над ним scope с деструктором.
        let base = adamas_kont_push(&raw mut kont, MARK_HANDLER, 9, None, None, 0, 0, with_outer);
        push_reaching(&raw mut kont, 5, with_outer);

        let doomed = adamas_kont_cut(&raw mut kont, base);
        adamas_segment_unwind(&raw mut kont, doomed);
        adamas_kont_run(&raw mut kont, adamas_unit());

        // Хендлер жив и не в сегменте: вердикт обычный, а не подавленный.
        assert_eq!(VERDICTS.with_borrow(Clone::clone), vec![LOOKUP_HANDLER]);
        // Разрез прошёл по одному стеку и забрал остаток раскрутки кадром:
        // хендлер плюс кадр `UNWINDING`. До правки §10 вопроса 144 здесь было
        // «кадр хендлера не принадлежит этому стеку»: деструктор бежал на
        // своём пустом стеке.
        assert_eq!(SEIZED.with_borrow(Clone::clone), vec![2]);
        // Деструктор договорил после возобновления.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![5]);

        adamas_evidence_drop(empty);
        adamas_evidence_drop(with_outer);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Резумпция, взятая деструктором и брошенная: остаток раскрутки лежит в её
/// сегменте кадром и доигрывается дропом - возобновления не случается, но
/// звенья ниже scope'а всё равно освобождаются.
unsafe extern "C" fn seizing(
    closure: Value,
    evidence: *const Evidence,
    kont: *mut Kont,
    argument: Value,
) -> Value {
    unsafe {
        let _ = adamas_imm_get(adamas_closure_get(closure, 0));
        adamas_drop(argument, None);
        let mut handler: *mut Frame = ptr::null_mut();
        let verdict = adamas_evidence_lookup(evidence, 7, &raw mut handler);
        VERDICTS.with_borrow_mut(|verdicts| verdicts.push(verdict));
        if verdict == LOOKUP_HANDLER {
            let segment = adamas_kont_cut(kont, handler);
            adamas_resumption_drop(kont, adamas_segment_value(segment));
        }
        // Контракт обрыва: после дропа своего продолжения - вернуться
        // немедленно, у машины этого кода нет вовсе.
        adamas_unit()
    }
}

#[test]
fn dropping_the_seized_resumption_finishes_the_unwinding() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        VERDICTS.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let outer = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        let with_outer = adamas_evidence_extend(empty, 7, outer);
        let base = adamas_kont_push(&raw mut kont, MARK_HANDLER, 9, None, None, 0, 0, with_outer);
        // Под сегментом - ещё один scope: его деструктор обязан сработать и
        // тогда, когда резумпцию выбросили, - через вложенный кадр раскрутки.
        push_closing(&raw mut kont, 3, with_outer);
        let frame = adamas_kont_push(
            &raw mut kont,
            MARK_CLOSING,
            0,
            None,
            Some(release_closer),
            1,
            1,
            with_outer,
        );
        let closure = adamas_closure(Some(seizing), None, 1, 1);
        adamas_closure_set(closure, 0, adamas_imm(4));
        *adamas_frame_env(frame) = closure;

        let doomed = adamas_kont_cut(&raw mut kont, base);
        adamas_segment_unwind(&raw mut kont, doomed);
        adamas_kont_run(&raw mut kont, adamas_unit());

        assert_eq!(VERDICTS.with_borrow(Clone::clone), vec![LOOKUP_HANDLER]);
        // Дроп резумпции доиграл остаток: scope с меткой 3 закрылся, хотя
        // возобновления не было. Хендлер снаружи при этом умер вместе со
        // всем, что деструктор у него отрезал, - и утечки нет.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![3]);

        adamas_evidence_drop(empty);
        adamas_evidence_drop(with_outer);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Ветки хендлера: номер операции выбирает ветку, `return` идёт своим номером.
///
/// Среда - один слот с числом; ветка операции прибавляет к нему аргумент, ветка
/// `return` умножает. Различие ответов и есть свидетель выбора: сойдись номера,
/// и одно число вышло бы вместо двух.
unsafe extern "C" fn branching(
    handler: *mut Frame,
    _kont: *mut Kont,
    operation: u32,
    arguments: *mut Value,
    count: usize,
) -> Value {
    unsafe {
        assert_eq!(count, 1, "ветке передан не один аргумент");
        let held = adamas_imm_get(adamas_field(*adamas_frame_env(handler), 0));
        let incoming = adamas_imm_get(*arguments);
        if operation == HANDLER_RETURN {
            return adamas_imm(held * incoming);
        }
        adamas_imm(held + incoming)
    }
}

/// Тот же хендлер без среды: ветки читают только вектор кадра.
unsafe extern "C" fn silent(
    _handler: *mut Frame,
    _kont: *mut Kont,
    _operation: u32,
    arguments: *mut Value,
    _count: usize,
) -> Value {
    unsafe { *arguments }
}

#[test]
fn an_operation_reaches_the_branches_of_its_handler() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let handler = adamas_kont_handler(
            &raw mut kont,
            7,
            Some(branching),
            Some(release_held),
            1,
            empty,
        );
        *adamas_frame_env(handler) = boxed(10);
        let with_handler = adamas_evidence_extend(empty, 7, handler);

        // Операция находит кадр вектором и зовёт его ветку на месте - сегмента
        // при хвостовой резумпции не снимается.
        let mut found: *mut Frame = ptr::null_mut();
        let verdict = adamas_evidence_lookup(with_handler, 7, &raw mut found);
        assert_eq!(verdict, LOOKUP_HANDLER);
        assert_eq!(found, handler);
        let mut arguments = [adamas_imm(5)];
        let answer = adamas_frame_perform(found, &raw mut kont, 0, arguments.as_mut_ptr(), 1);
        assert_eq!(adamas_imm_get(answer), 15, "ветка операции не сработала");
        assert_eq!(adamas_kont_depth(&raw const kont), 1);
        assert_eq!(kont.top, handler);

        // Нормальный выход: значение вычисления доходит до кадра трамплином,
        // кадр снимается, `return` получает это значение.
        let answer = adamas_kont_run(&raw mut kont, adamas_imm(3));
        assert_eq!(adamas_imm_get(answer), 30, "ветка `return` не сработала");
        assert_eq!(adamas_kont_depth(&raw const kont), 0);
        assert!(kont.top.is_null());

        adamas_evidence_drop(with_handler);
        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Окружающая ветки - вектор **на месте `handle`**, а не тот, под которым
/// работала операция: ветка стоит снаружи своего хендлера (§3.4).
#[test]
fn a_branch_sees_the_vector_of_its_handle_site() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let handler = adamas_kont_handler(&raw mut kont, 7, Some(silent), None, 0, empty);
        let with_handler = adamas_evidence_extend(empty, 7, handler);

        // Под хендлером своя метка находится, а у ветки её нет: кадр помнит
        // родительский вектор, и второго источника у него не бывает.
        assert_eq!(
            adamas_evidence_lookup(with_handler, 7, ptr::null_mut()),
            LOOKUP_HANDLER
        );
        assert_eq!(
            adamas_evidence_lookup(adamas_frame_evidence(handler), 7, ptr::null_mut()),
            LOOKUP_MISSING
        );

        adamas_drop(adamas_kont_run(&raw mut kont, adamas_unit()), None);
        adamas_evidence_drop(with_handler);
        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

#[test]
fn a_normal_exit_suppresses_nothing() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        VERDICTS.with_borrow_mut(Vec::clear);
        let (mut kont, _outer, _base, vectors) = suppression_stack();

        // Ближайший проходящий сосед предыдущего теста: тот же стек, но выход
        // нормальный. Хендлеры под scope'ом ответа ещё не давали, и операция
        // деструктора обязана их достать.
        adamas_kont_run(&raw mut kont, adamas_unit());

        assert_eq!(
            VERDICTS.with_borrow(Clone::clone),
            vec![LOOKUP_HANDLER, LOOKUP_HANDLER, LOOKUP_HANDLER]
        );
        // Деструктор договорил (2); обрыва не было, поэтому стек его доигран до
        // конца - и scope закрылся (8), и отложенное сделано (77).
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![2, 8, 77, 1]);

        for evidence in vectors {
            adamas_evidence_drop(evidence);
        }
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Резумпция-значение: возобновление **тратит** ручку, а не отдаёт её блок.
///
/// Свидетель нужен потому, что ссылок на ручку бывает больше одной: замыкание
/// `\s -> resume v s` параметризованного хендлера держит её наравне с
/// вызывающим (§3.4, §10 вопрос 129). Освободи блок при возобновлении - и
/// вторая ссылка читала бы освобождённое.
#[test]
fn a_resumption_is_a_value_with_its_own_count() {
    unsafe {
        adamas_stat_reset();
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        push_holding(&raw mut kont, MARK_PLAIN, adding, 3, empty);
        let resumption = adamas_segment_value(adamas_kont_cut(&raw mut kont, handler));
        assert_eq!(adamas_kont_depth(&raw const kont), 0);

        // Вторая ссылка: та, что уехала бы в замыкание.
        adamas_dup(resumption);
        adamas_kont_resume(&raw mut kont, resumption);
        assert_eq!(
            adamas_kont_depth(&raw const kont),
            2,
            "звенья не вернулись на стек"
        );
        // Потраченную дропают дважды, и блок отдаёт последняя.
        adamas_resumption_drop(&raw mut kont, resumption);
        adamas_resumption_drop(&raw mut kont, resumption);

        let answer = adamas_kont_run(&raw mut kont, adamas_imm(4));
        assert_eq!(adamas_imm_get(answer), 7, "возобновление не досчитало");

        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

/// Брошенная резумпция без ручки стека: деструкторы бегут на своём корне.
///
/// Путь этот принадлежит слоту замыкания и полю объекта - там, где дроп идёт
/// через `adamas_release`, у которого ручки нет по сигнатуре. Ближайший
/// проходящий сосед - `adamas_resumption_drop` с ручкой: там раскрутка
/// откладывается кадром, здесь бежит немедленно.
#[test]
fn an_abandoned_resumption_unwinds_on_its_own_root() {
    unsafe {
        adamas_stat_reset();
        TRACE.with_borrow_mut(Vec::clear);
        let mut kont = kont();
        let empty = adamas_evidence_empty();

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 7, None, None, 0, 0, empty);
        push_closing(&raw mut kont, 5, empty);
        let resumption = adamas_segment_value(adamas_kont_cut(&raw mut kont, handler));

        adamas_segment_abandon(resumption);
        // Немедленно, без трамплина: у этого пути точки приостановки нет вовсе.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![5]);
        assert!(kont.top.is_null(), "раскрутка ушла на чужой стек");
        // Блок ручки отдаёт дроп: `adamas_release` его не освобождает.
        adamas_resumption_drop(&raw mut kont, resumption);

        adamas_evidence_drop(empty);
        assert_eq!(adamas_stat_live(), 0);
    }
}

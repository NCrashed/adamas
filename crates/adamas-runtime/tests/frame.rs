//! Кадры, сегмент продолжения, мультишот и раскрутка.
//!
//! Проверяется семантика, которую понижение обязано повторить за машиной
//! интерпретатора (`adamas-interp/src/frame.rs`): порядок работы сверху вниз,
//! копирование звеньев под мультишот, деструкторы раскрутки в порядке LIFO.

#![allow(unsafe_code)]

use std::cell::RefCell;
use std::ptr;

use adamas_runtime::ffi::{
    Evidence, Frame, Kont, MARK_CLOSING, MARK_HANDLER, MARK_PLAIN, Value, adamas_alloc,
    adamas_closure, adamas_closure_get, adamas_closure_release, adamas_closure_set, adamas_drop,
    adamas_dup, adamas_evidence_drop, adamas_evidence_empty, adamas_field, adamas_frame_env,
    adamas_frame_fields, adamas_frame_label, adamas_frame_mark, adamas_imm, adamas_imm_get,
    adamas_kont_cut, adamas_kont_init, adamas_kont_push, adamas_kont_restore, adamas_kont_run,
    adamas_rc, adamas_resumption_drop, adamas_segment_base, adamas_segment_copy,
    adamas_segment_depth, adamas_segment_unwind, adamas_segment_value, adamas_set_field,
    adamas_stat_live, adamas_stat_reset, adamas_unit,
};

thread_local! {
    /// Отметки сработавших деструкторов в порядке срабатывания.
    static TRACE: RefCell<Vec<isize>> = const { RefCell::new(Vec::new()) };
}

/// Пустой стек.
fn kont() -> Kont {
    let mut kont = Kont {
        top: ptr::null_mut(),
        depth: 0,
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
unsafe extern "C" fn adding(frame: *mut Frame, incoming: Value) -> Value {
    unsafe {
        let held = *adamas_frame_env(frame);
        adamas_imm(adamas_imm_get(incoming) + adamas_imm_get(adamas_field(held, 0)))
    }
}

/// Умножает пришедшее на число из среды.
unsafe extern "C" fn scaling(frame: *mut Frame, incoming: Value) -> Value {
    unsafe {
        let held = *adamas_frame_env(frame);
        adamas_imm(adamas_imm_get(incoming) * adamas_imm_get(adamas_field(held, 0)))
    }
}

/// Дроп среды кадра: один слот с объектом.
unsafe extern "C" fn release_held(frame: *mut Frame) {
    unsafe {
        adamas_drop(*adamas_frame_env(frame), None);
    }
}

/// Дроп среды кадра: один слот с замыканием.
unsafe extern "C" fn release_closer(frame: *mut Frame) {
    unsafe {
        adamas_drop(*adamas_frame_env(frame), Some(adamas_closure_release));
    }
}

/// Дроп среды кадра: один слот с резумпцией.
unsafe extern "C" fn release_resumption(frame: *mut Frame) {
    unsafe {
        adamas_resumption_drop(*adamas_frame_env(frame));
    }
}

/// Деструктор, отмечающийся в следе.
unsafe extern "C" fn note(closure: Value, _evidence: *const Evidence, argument: Value) -> Value {
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

/// Кадр с числом в среде.
unsafe fn push_holding(
    kont: *mut Kont,
    mark: u16,
    code: unsafe extern "C" fn(*mut Frame, Value) -> Value,
    number: isize,
    evidence: *mut Evidence,
) -> *mut Frame {
    unsafe {
        let frame = adamas_kont_push(kont, mark, 0, Some(code), Some(release_held), 1, evidence);
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
            evidence,
        );
        *adamas_frame_env(frame) = closer(mark);
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

        let bottom = adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, evidence);
        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 3, None, None, 0, evidence);
        adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, evidence);
        adamas_kont_push(&raw mut kont, MARK_PLAIN, 0, None, None, 0, evidence);
        assert_eq!(kont.depth, 4);

        let segment = adamas_kont_cut(&raw mut kont, handler);
        // Сегмент включает сам кадр хендлера: возобновление ставит его обратно,
        // и это и значит «глубокий».
        assert_eq!(adamas_segment_depth(segment), 3);
        assert_eq!(adamas_segment_base(segment), handler);
        assert_eq!(adamas_frame_mark(handler), MARK_HANDLER);
        assert_eq!(adamas_frame_label(handler), 3);
        assert_eq!(adamas_frame_fields(handler), 0);
        // Под разрезом стек цел.
        assert_eq!(kont.depth, 1);
        assert_eq!(kont.top, bottom);

        adamas_segment_unwind(segment);
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

        // Снизу вверх: прибавить 10, умножить на 2, прибавить 1.
        push_holding(&raw mut kont, MARK_HANDLER, adding, 10, evidence);
        push_holding(&raw mut kont, MARK_PLAIN, scaling, 2, evidence);
        push_holding(&raw mut kont, MARK_PLAIN, adding, 1, evidence);

        // Вершина первая: (1 + 1) * 2 + 10. Обратный порядок дал бы 23.
        let answer = adamas_kont_run(&raw mut kont, adamas_imm(1));
        assert_eq!(adamas_imm_get(answer), 14);
        assert_eq!(kont.depth, 0);
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

        let handler = push_holding(&raw mut kont, MARK_HANDLER, adding, 10, evidence);
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
        assert_eq!(kont.depth, 2);
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
        adamas_segment_unwind(segment);
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

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, evidence);
        push_closing(&raw mut kont, 1, evidence);
        push_closing(&raw mut kont, 2, evidence);
        push_closing(&raw mut kont, 3, evidence);

        let segment = adamas_kont_cut(&raw mut kont, handler);
        adamas_segment_unwind(segment);
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

        let handler = adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, evidence);
        push_closing(&raw mut kont, 1, evidence);
        let resumption = adamas_segment_value(adamas_kont_cut(&raw mut kont, handler));

        adamas_dup(resumption);
        adamas_resumption_drop(resumption);
        // Ссылка была лишняя - сегмент жив, деструктор молчит.
        assert!(TRACE.with_borrow(Vec::is_empty));

        adamas_resumption_drop(resumption);
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
            adamas_kont_push(&raw mut kont, MARK_HANDLER, 1, None, None, 0, evidence);
        push_closing(&raw mut kont, 9, evidence);
        let inner = adamas_segment_value(adamas_kont_cut(&raw mut kont, inner_handler));

        let outer_handler =
            adamas_kont_push(&raw mut kont, MARK_HANDLER, 2, None, None, 0, evidence);
        let holder = adamas_kont_push(
            &raw mut kont,
            MARK_PLAIN,
            0,
            None,
            Some(release_resumption),
            1,
            evidence,
        );
        *adamas_frame_env(holder) = inner;
        push_closing(&raw mut kont, 1, evidence);

        let outer = adamas_kont_cut(&raw mut kont, outer_handler);
        adamas_segment_unwind(outer);
        // Сперва свой деструктор, затем брошенная резумпция под ним.
        assert_eq!(TRACE.with_borrow(Clone::clone), vec![1, 9]);

        adamas_evidence_drop(evidence);
        assert_eq!(adamas_stat_live(), 0);
    }
}

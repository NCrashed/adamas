//! Поле-эффектная функция, брошенное без `unwind` (§3.4, §10 вопрос 252).
//!
//! Брошенная молча резумпция разматывается лишь в ближайшей точке
//! приостановки, и порядок эффектов её деструкторов у исполнителей не
//! определён. Тип не говорит, резумпция ли в поле,
//! поэтому это оговорка, а не отказ. Свидетель парный: та же обёртка с
//! `unwind` и с чистым полем молчит.

use adamas_core::source::SourceFile;
use adamas_elab::program::{Memory, analyze};

/// Обёртка резумпции: поле типа `field`, деструктор `body`.
fn said(field: &str, body: &str) -> Vec<String> {
    let entry = format!(
        "effect Log where
  note : UInt64 -> Unit

resource Resumption (r : Type) where
  Suspended : (1 k : {field}) -> Resumption r
  abandon : (1 s : Resumption r) -> {{Log}} Unit
  {body}
"
    );
    let program = analyze(SourceFile::new("вход", entry), &Memory::new());
    if let Some(located) = program.error() {
        panic!("отвергнуто: {}", program.rendered(located));
    }
    program
        .diagnostics
        .iter()
        .map(|it| it.diagnostic.message())
        .collect()
}

#[test]
fn an_effectful_field_dropped_without_unwind_is_warned_about() {
    assert_eq!(
        said("Unit -> {Log} r", "abandon (Suspended _k) = MkUnit"),
        [
            "поле конструктора `Suspended` - эффектная функция - брошено без `unwind`: если \
             это резумпция, её сегмент размотается лишь в ближайшей точке приостановки, и \
             порядок эффектов её деструкторов не определён; напишите `unwind`"
        ]
    );
}

#[test]
fn an_unwound_field_is_silent() {
    let found = said("Unit -> {Log} r", "abandon (Suspended k) = unwind k");
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn a_pure_field_is_silent() {
    // Чистой резумпции эффекту уйти некуда: размотка на своём корне честна.
    let found = said("Unit -> r", "abandon (Suspended _k) = MkUnit");
    assert!(found.is_empty(), "{found:#?}");
}

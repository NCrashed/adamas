//! Хвостовая резумптивность (§3.4) и два её читателя - §5.1 и §5.3.
//!
//! Свидетели идут от исходника, а не от собранного терма: позиция `resume`
//! есть свойство **написанного**, и тест на форму ядра ломался бы от смены
//! элаборации, ничего при этом не защищая.

use std::collections::BTreeMap;

use adamas_core::resume::{Blocked, Verdict, crossing, labels};
use adamas_core::row::{Label, Row};
use adamas_core::sig::Signature;
use adamas_core::term::{Name, Term};
use adamas_elab::{ElabError, elaborate};
use adamas_parser::parse;

/// Общая шапка: типы, без которых не написать ни одного хендлера.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit
";

/// Текст до сигнатуры. Отказ здесь - провал теста, а не проверяемый исход.
fn program(text: &str) -> Signature {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Ok((signature, _)) => signature,
        Err(error) => panic!("не элаборировалось: {error}"),
    }
}

/// Отказ элаборации; всё остальное - провал теста.
fn refused(text: &str) -> ElabError {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Err(error) => error,
        Ok(_) => panic!("ожидался отказ элаборации"),
    }
}

/// Вердикт метки по всем её площадкам в программе.
fn verdict(known: &BTreeMap<Name, Verdict>, label: &str) -> Verdict {
    match known.get(label) {
        Some(found) => *found,
        None => panic!("у метки `{label}` в программе нет ни одной площадки"),
    }
}

/// Замкнутая row из одной метки без аргументов.
fn only(label: &str) -> Row<Term> {
    Row::new([Label {
        name: label.into(),
        arguments: Vec::new(),
    }])
}

/// Перечень позиций `resume`, а не одна наблюдённая.
///
/// Каждая метка здесь - отдельная форма ветки, и вердикт у неё свой. Список
/// повторяет тот, что записан в шапке [`adamas_core::resume`]: разойдись они,
/// правило оказалось бы закрыто на том случае, на котором его нашли.
#[test]
fn the_positions_of_resume_are_enumerated() {
    let signature = program(&format!(
        "{BASE}
-- Кратность здесь `1`, а не умолчание: ω-параметр масштабировал бы аргумент
-- до ω, и аффинная резумпция в него не прошла бы вовсе.
bump : (1 n : Nat) -> Nat
bump n = n

-- `resume e` целиком телом.
effect Straight where
  straight : Unit

runStraight : ({{Straight}} Nat) -> Nat
runStraight act = handle act with
  return v -> v
  straight -> resume MkUnit

-- Резумпция не названа ни разу.
effect Stopped where
  stopped : Unit

runStopped : ({{Stopped}} Nat) -> Nat
runStopped act = handle act with
  return v -> v
  stopped -> Zero

-- Под разбором: у него по ответу на ветвь, и хвоста тут нет.
effect Chosen where
  chosen : Bool

runChosen : ({{Chosen}} Nat) -> Nat
runChosen act = handle act with
  return v -> v
  chosen -> case Zero of
    Zero -> resume True
    Succ k -> resume False

-- Аргументом чужого применения.
effect Wrapped where
  wrapped : Unit

runWrapped : ({{Wrapped}} Nat) -> Nat
runWrapped act = handle act with
  return v -> v
  wrapped -> bump (resume MkUnit)

-- Полем записи через проекцию: к резумпции ведут только узлы записи, и обход
-- обязан заглядывать в них. Обход понижения в них не заходит - см. заметки.
effect Boxed where
  boxed : Unit

runBoxed : ({{Boxed}} Nat) -> {{ got : Nat }}
runBoxed act = handle act with
  return v -> {{ got = v }}
  boxed -> {{ got = (resume MkUnit).got }}

-- Мультишот: вердикт не считается вовсе, ω-резумпция ничего не обещает.
effect Tossed where
  tossed : Bool

runTossed : ({{Tossed}} Nat) -> Nat
runTossed act = handleMulti act with
  return v -> v
  tossed -> resume True

-- Параметризованный: лямбда по состоянию дописана последним связыванием, и
-- `resume` стоит под ней - в хвосте он не окажется никогда.
effect Counted where
  fetch : Nat

runCounted : ({{Counted}} Nat) -> Nat
runCounted act = handle act with
  state Zero
  return v -> v
  fetch -> resume state state
"
    ));
    let known = labels(&signature);
    for (label, wanted) in [
        ("Straight", Verdict::Tail),
        ("Stopped", Verdict::Abortive),
        ("Chosen", Verdict::General),
        ("Wrapped", Verdict::General),
        ("Boxed", Verdict::General),
        ("Tossed", Verdict::General),
        ("Counted", Verdict::General),
    ] {
        assert_eq!(verdict(&known, label), wanted, "метка `{label}`");
    }
}

/// Абортивный случай разводит двух читателей по разным сторонам.
///
/// Одна программа, два ответа: §5.1 принимает `@noalloc` - продолжение
/// отброшено, захватывать нечего, - а правило чужого кадра тот же хендлер
/// отвергает, потому что спрашивает не про аллокацию, а про возврат
/// управления. Симметричная правка от одного читателя к другому и была бы
/// ошибкой, которую §5.3 называет прямо.
#[test]
fn the_two_readers_part_on_the_abortive_case() {
    let signature = program(&format!(
        "{BASE}
effect Fail where
  fail : Nat

effect Ask where
  ask : Nat

-- Абортивная: ветка резумпцию не зовёт.
@noalloc
runFail : ({{Fail}} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail -> Zero

-- Хвостовая: зовёт её в хвосте и один раз.
@noalloc
runAsk : ({{Ask}} Nat) -> Nat
runAsk act = handle act with
  return v -> v
  ask -> resume Zero
"
    ));
    let known = labels(&signature);
    assert_eq!(verdict(&known, "Fail"), Verdict::Abortive);
    assert_eq!(verdict(&known, "Ask"), Verdict::Tail);

    // §5.1: обе площадки под `@noalloc` законны - программа принята, и вердикт
    // ядра у обеих пуст.
    for name in ["runFail", "runAsk"] {
        assert!(
            signature
                .lookup(name)
                .is_some_and(|it| it.allocates.is_none()),
            "`{name}`: ни хвостовая, ни абортивная ветка кучи не трогают"
        );
    }

    // §5.3: хвостовая проходит через чужой кадр, абортивная - нет.
    assert_eq!(crossing(&known, &only("Ask")), None);
    assert_eq!(
        crossing(&known, &only("Fail")),
        Some(Blocked::Handler {
            label: "Fail".into(),
            verdict: Verdict::Abortive,
        }),
        "абортивный стоит на стороне общего случая: управление не вернётся"
    );
}

/// Отказ §5.1 называет метку и ветку, а не «где-то в хендлере».
#[test]
fn the_general_branch_is_blamed_by_name() {
    let text = format!(
        "{BASE}
bump : (1 n : Nat) -> Nat
bump n = n

effect Yield where
  yield : Nat -> Unit

@noalloc
collected : ({{Yield}} Nat) -> Nat
collected act = handle act with
  return v -> v
  yield x -> bump (resume MkUnit)
"
    );
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::Allocates { .. }),
        "получено {error:?}"
    );
    let said = error.to_string();
    assert!(
        said.contains("`Yield`") && said.contains("`yield`") && said.contains("вне хвостовой"),
        "отказ обязан назвать метку и ветку: {said}"
    );
}

/// `handleMulti` платит сама форма, и отказ не сваливает вину на ветку.
#[test]
fn a_multishot_site_pays_by_its_form() {
    let text = format!(
        "{BASE}
effect Tossed where
  tossed : Bool

@noalloc
runTossed : ({{Tossed}} Nat) -> Nat
runTossed act = handleMulti act with
  return v -> v
  tossed -> resume True
"
    );
    let said = refused(&text).to_string();
    assert!(
        said.contains("handleMulti") && said.contains("`Tossed`"),
        "отказ обязан назвать форму, а не ветку: {said}"
    );
    assert!(
        !said.contains("`tossed`"),
        "ветка тут ни при чём - вердикт у мультишота не считается: {said}"
    );
}

/// Правило чужого кадра: три способа не пройти, и каждый называет причину.
#[test]
fn the_foreign_frame_rule_names_what_blocks_it() {
    let signature = program(&format!(
        "{BASE}
bump : (1 n : Nat) -> Nat
bump n = n

effect Ask where
  ask : Nat

effect Fail where
  fail : Nat

effect Yield where
  yield : Nat -> Unit

-- Метка без единой площадки: погасить её в программе нечем.
effect Loose where
  loose : Nat

runAsk : ({{Ask}} Nat) -> Nat
runAsk act = handle act with
  return v -> v
  ask -> resume Zero

runFail : ({{Fail}} Nat) -> Nat
runFail act = handle act with
  return v -> v
  fail -> Zero

runYield : ({{Yield}} Nat) -> Nat
runYield act = handle act with
  return v -> v
  yield x -> bump (resume MkUnit)

leaked : ({{Loose}} Nat) -> {{Loose}} Nat
leaked act = act MkUnit
"
    ));
    let known = labels(&signature);

    // Пустая row проходит: гасить нечего, и возвращаться неоткуда.
    assert_eq!(crossing(&known, &Row::empty()), None);
    assert_eq!(crossing(&known, &only("Ask")), None);

    let blocked = |label: &str| match crossing(&known, &only(label)) {
        Some(found) => found,
        None => panic!("`{label}` обязан быть отвергнут в позиции колбэка"),
    };
    assert_eq!(
        blocked("Fail"),
        Blocked::Handler {
            label: "Fail".into(),
            verdict: Verdict::Abortive,
        }
    );
    assert_eq!(
        blocked("Yield"),
        Blocked::Handler {
            label: "Yield".into(),
            verdict: Verdict::General,
        }
    );
    assert_eq!(blocked("Loose"), Blocked::Unhandled("Loose".into()));
    for label in ["Fail", "Yield", "Loose"] {
        let said = blocked(label).to_string();
        assert!(
            said.contains(&format!("`{label}`")) && said.contains("§5.3"),
            "отказ обязан назвать конкретный эффект: {said}"
        );
    }

    // Открытый хвост: что придёт сверх написанного, в точке регистрации
    // неизвестно. Метка при этом называется раньше хвоста - она точнее.
    let open = Row::closing(
        [Label {
            name: "Ask".into(),
            arguments: Vec::new(),
        }],
        Some(adamas_core::row::Tail::Var(adamas_core::row::RowVar(0))),
    );
    assert!(matches!(
        crossing(&known, &open),
        Some(Blocked::Open(adamas_core::row::Tail::Var(_)))
    ));
    let mixed = Row::closing(
        [Label {
            name: "Fail".into(),
            arguments: Vec::new(),
        }],
        Some(adamas_core::row::Tail::Var(adamas_core::row::RowVar(0))),
    );
    assert!(matches!(
        crossing(&known, &mixed),
        Some(Blocked::Handler { .. })
    ));
}

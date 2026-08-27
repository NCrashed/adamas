//! Программы Adamas от текста до проверки типов - milestone Фазы 2.
//!
//! Проверяется не форма собранного терма, а два факта: программа доходит до
//! сигнатуры и то, что в ней оказалось, **вычисляет то, что написано**.
//! Форма - деталь элаборации, и тест на неё ломался бы от смены стратегии,
//! ничего при этом не защищая.

use std::rc::Rc;

use adamas_core::check::check_closed;
use adamas_core::level::Level;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::{ElabError, Missing, elaborate};
use adamas_parser::parse;

/// Текст до сигнатуры. Отказ здесь - провал теста, а не проверяемый исход.
fn program(text: &str) -> Signature {
    let module = match parse(text) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Ok(signature) => signature,
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

/// Ссылка на определение с одним параметром уровня, взятым нулём.
///
/// Написанный `Type` даёт дырку, она обобщается в параметр, и семейство
/// оказывается полиморфным по уровню. Тесту нужен замкнутый терм, поэтому
/// уровень задаётся явно.
fn at(name: &str) -> Term {
    Term::Const(name.into(), Rc::from([Level::Zero]))
}

/// `Nat` и `Bool` - минимальная база, на которой пишется всё остальное.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat
";

#[test]
fn a_family_and_its_constructors_reach_the_signature() {
    let signature = program(BASE);
    assert_eq!(
        signature
            .constructors("Nat")
            .expect("Nat индуктивен")
            .iter()
            .map(std::convert::AsRef::as_ref)
            .collect::<Vec<&str>>(),
        ["Zero", "Succ"],
        "порядок объявления задаёт порядок ветвей разбора"
    );
}

#[test]
fn a_definition_by_clauses_computes_what_it_says() {
    // `plus` собирается в дерево разбора и **вычисляет**: проверка
    // `anything (plus 2 3)` против `P 5` проходит только через δ и ι.
    let text = format!(
        "{BASE}
P : Nat -> Type
anything : (0 n : Nat) -> P n

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)
"
    );
    let signature = program(&text);

    assert!(
        signature
            .lookup("plus")
            .is_some_and(|definition| definition.total),
        "структурная рекурсия распознана"
    );

    let number = |value: u32| {
        (0..value).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        })
    };
    // `P` написана через `Type`, поэтому полиморфна по уровню; уровень здесь
    // задаётся явно - тесту нужен замкнутый терм, а не ещё одна дырка.
    for (left, right, sum) in [(0, 0, 0), (2, 3, 5), (4, 1, 5)] {
        let witness = at("anything").apply([number(sum)]);
        let family = at("P").apply([Term::constant("plus").apply([number(left), number(right)])]);
        let outcome = check_closed(&signature, &witness, &family);
        assert!(outcome.is_ok(), "{left}+{right} = {sum}: {outcome:?}");
    }
}

#[test]
fn nested_patterns_and_a_wildcard_elaborate() {
    let text = format!(
        "{BASE}
Q : Bool -> Type
q : (0 b : Bool) -> Q b

even : Nat -> Bool
even Zero = True
even (Succ Zero) = False
even (Succ (Succ k)) = even k

constant : Nat -> Bool
constant _ = True
"
    );
    let signature = program(&text);

    // Что дерево разбора **вычисляет**, видно только через конвертируемость:
    // `normalize` определений не разворачивает, δ живёт в проверке типов.
    for (input, expected) in [(0, "True"), (1, "False"), (2, "True"), (3, "False")] {
        let number = (0..input).fold(Term::constant("Zero"), |term, _| {
            Term::constant("Succ").apply([term])
        });
        let witness = at("q").apply([Term::constant(expected)]);
        let stated = at("Q").apply([Term::constant("even").apply([number])]);
        let outcome = check_closed(&signature, &witness, &stated);
        assert!(outcome.is_ok(), "even {input} = {expected}: {outcome:?}");
    }
    assert!(signature.lookup("constant").is_some());
}

#[test]
fn an_indexed_family_elaborates() {
    // Индексы монотипны, поэтому фрагменту доступны: параметров у семейства
    // нет, а `Nat` в индексе объявлен выше.
    let text = format!(
        "{BASE}
data Even : Nat -> Type where
  EvenZero : Even Zero
  EvenTwo : (0 n : Nat) -> Even n -> Even (Succ (Succ n))
"
    );
    let signature = program(&text);
    assert_eq!(
        signature
            .constructors("Even")
            .expect("Even индуктивен")
            .len(),
        2
    );
}

#[test]
fn a_signature_without_clauses_is_a_postulate() {
    // §4.1 пишет так примитивы: `openFile : String -> …` без тела.
    let text = format!("{BASE}\nopaque : Nat -> Bool\n");
    let signature = program(&text);
    let postulate = signature.lookup("opaque").expect("постулат объявлен");
    assert!(postulate.body.is_none(), "тела у постулата нет");
}

#[test]
fn a_dependent_function_type_elaborates() {
    let text = format!(
        "{BASE}
P : Nat -> Type
witness : (0 n : Nat) -> P n
use : (0 n : Nat) -> P n
use n = witness n
"
    );
    let signature = program(&text);
    assert!(signature.lookup("use").is_some());
}

#[test]
fn a_let_with_an_annotation_elaborates() {
    let text = format!(
        "{BASE}
two : Nat
two =
  let one : Nat = Succ Zero
  Succ one
"
    );
    let signature = program(&text);
    let body = signature
        .lookup("two")
        .and_then(|definition| definition.body.clone())
        .expect("тело есть");
    assert_eq!(
        adamas_core::eval::normalize(&body).to_string(),
        "Succ (Succ Zero)",
        "`let` вычисляется"
    );
}

// ------------------------------------------------------------------ отказы

#[test]
fn an_uppercase_name_in_a_pattern_must_be_a_constructor() {
    // Ровно та опечатка, ради которой правило регистра и выбрано: `Zeroo` не
    // становится переменной, ловящей всё, а называется на месте.
    let text = format!(
        "{BASE}
f : Nat -> Bool
f Zeroo = True
f _ = False
"
    );
    let error = refused(&text);
    let ElabError::NotAConstructor { name, .. } = &error else {
        panic!("ожидалось `NotAConstructor`, получено {error:?}");
    };
    assert_eq!(&**name, "Zeroo");
}

#[test]
fn a_lowercase_name_in_a_pattern_binds() {
    // Контроль к предыдущему: строчное имя связывает, даже если совпадает с
    // конструктором по смыслу.
    let text = format!(
        "{BASE}
f : Nat -> Nat
f zero = zero
"
    );
    let signature = program(&text);
    assert!(signature.lookup("f").is_some());
}

#[test]
fn clauses_without_a_signature_are_refused() {
    let text = format!("{BASE}\nf Zero = True\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::MissingSignature { .. }),
        "получено {error:?}"
    );
}

#[test]
fn what_the_core_cannot_carry_yet_names_itself() {
    // Каждая форма отвечает тем, чего ей недостаёт, а не «неизвестное имя»:
    // программа написана правильно, не хватает ядра.
    let missing = [
        ("f : Nat -> Nat\nf x = 1\n", Missing::Literal),
        ("f : Nat -> Nat\nf x = _\n", Missing::TermHole),
        ("f : {a : Type} -> Nat\n", Missing::ImplicitBinder),
        ("f : Nat\nf =\n  let x = Zero\n  x\n", Missing::UntypedLet),
        (
            "f : Nat -> Nat\nf x = if x then x else x\n",
            Missing::Conditional,
        ),
        ("f : Nat\nf = (Zero, Zero)\n", Missing::Tuple),
        ("resource File where\n  drop h = h\n", Missing::Resource),
    ];
    for (text, expected) in missing {
        let text = format!("{BASE}{text}");
        let error = refused(&text);
        let ElabError::Missing { what, .. } = error else {
            panic!("для {text:?} ожидалось `Missing`, получено {error:?}");
        };
        assert_eq!(what, expected, "для {text:?}");
    }
}

#[test]
fn a_free_type_variable_is_refused_for_now() {
    // Полиморфизм упирается в ядро, а не в элаборацию: подъём `a` в
    // implicit-параметр требует видимости у `Pi` и метапеременных на термах.
    let error = refused("f : a -> a\n");
    let ElabError::Missing {
        what: Missing::Implicits,
        ..
    } = error
    else {
        panic!("ожидались имплиситы, получено {error:?}");
    };
    // В теле то же имя - опечатка, а не свободная переменная: поднимать в
    // implicit-параметр там нечего.
    let error = refused(&format!("{BASE}f : Nat -> Nat\nf n = a\n"));
    assert!(
        matches!(error, ElabError::UnknownName { .. }),
        "получено {error:?}"
    );
}

#[test]
fn an_ill_typed_program_is_refused_by_the_core() {
    // Элаборация не в TCB: терм она собирает, а отвергает его `check`.
    let text = format!("{BASE}\nf : Nat -> Bool\nf n = n\n");
    let error = refused(&text);
    assert!(
        matches!(error, ElabError::Core { .. }),
        "получено {error:?}"
    );
}

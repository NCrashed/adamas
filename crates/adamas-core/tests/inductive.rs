//! Индуктивные типы: объявление, конструкторы, строгая позитивность, укладка
//! в универсум (§3.2, §9 Фаза 1).
//!
//! До этого среза `Type 0` был населён только `Pi`-типами, а замкнутых термов
//! в нём не существовало вовсе: постулировать житель можно, но постулат ничего
//! не вычисляет. Data-декларация - первый способ добавить в теорию новые
//! замкнутые значения, и она же - первый способ её сломать, если не проверять
//! позитивность и универсумы.
//!
//! Элиминации здесь ещё нет: конструкторы строят, разбирать пока нечем.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, TypeError, check_closed, infer_closed};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::{Group, Member, Signature};
use adamas_core::term::{Binder, Term};
use proptest::prelude::*;

// -------------------------------------------------------------- конструкторы

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(
        Binder::explicit(mult),
        name.into(),
        Rc::new(domain),
        Row::empty(),
        Rc::new(codomain),
    )
}

/// Стрелка без зависимости. Кодомен сдвигать не нужно: он замкнут.
fn arrow(domain: Term, codomain: Term) -> Term {
    pi(Mult::Many, "_", domain, codomain)
}

/// Параметр уровня по индексу.
fn u(index: u32) -> Level {
    Level::Var(LevelVar(index))
}

/// Ссылка на определение без параметров уровня.
fn c(name: &str) -> Term {
    Term::constant(name)
}

// -------------------------------------------------------------- заготовки

/// Разворачивает объявление: отказ здесь - поломка заготовки, а не проверки.
fn declared(what: &str, outcome: &Result<(), TypeError>) {
    assert!(outcome.is_ok(), "{what} корректен: {outcome:?}");
}

/// Ссылка на член **объявляемой** группы: `arity` дырок уровня.
///
/// Спросить арность у сигнатуры нельзя - члена там ещё нет, - поэтому число
/// дырок пишется. Разойдётся с выведенной арностью - будет `LevelArity`.
fn ahead(name: &str, metas: &mut Metas, arity: u32) -> Term {
    let levels: Vec<Level> = (0..arity).map(|_| metas.fresh_level()).collect();
    Term::Const(name.into(), levels.into())
}

/// `Bool : Type 0` с двумя конструкторами - минимальный перечислимый тип.
fn booleans() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    declared(
        "Bool",
        &signature.declare_data(
            &mut metas,
            "Bool",
            0,
            Term::universe(0),
            &[("true", c("Bool")), ("false", c("Bool"))],
        ),
    );
    signature
}

/// `Nat : Type 0` поверх `Bool` - первый рекурсивный тип.
fn naturals() -> Signature {
    let mut signature = booleans();
    let mut metas = Metas::default();
    declared(
        "Nat",
        &signature.declare_data(
            &mut metas,
            "Nat",
            0,
            Term::universe(0),
            &[("zero", c("Nat")), ("succ", arrow(c("Nat"), c("Nat")))],
        ),
    );
    signature
}

/// `List : (0 A : Type u) -> Type u` - параметр и полиморфизм по уровню.
///
/// Уровни нигде не написаны: и в типе-формере, и в конструкторах стоят дырки,
/// а параметр уровня появляется обобщением (§9, implicit universe
/// polymorphism).
fn lists() -> Signature {
    let mut signature = naturals();
    let mut metas = Metas::default();

    let level = metas.fresh_level();
    let list_of = |metas: &mut Metas, element: Term| ahead("List", metas, 1).apply([element]);

    let nil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        list_of(&mut metas, Term::var(0)),
    );
    let cons = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::One,
            "x",
            Term::var(0),
            pi(
                Mult::One,
                "xs",
                list_of(&mut metas, Term::var(1)),
                list_of(&mut metas, Term::var(2)),
            ),
        ),
    );
    declared(
        "List",
        &signature.declare_data(
            &mut metas,
            "List",
            1,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
            &[("nil", nil), ("cons", cons)],
        ),
    );
    signature
}

/// `Vect : (0 A : Type u) -> (0 n : Nat) -> Type u` - параметр и индекс рядом.
fn vectors() -> Signature {
    let mut signature = naturals();
    let mut metas = Metas::default();

    let level = metas.fresh_level();
    let vect_of = |metas: &mut Metas, element: Term, length: Term| {
        ahead("Vect", metas, 1).apply([element, length])
    };

    let vnil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        vect_of(&mut metas, Term::var(0), c("zero")),
    );
    let vcons = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::Zero,
            "n",
            c("Nat"),
            pi(
                Mult::One,
                "x",
                Term::var(1),
                pi(
                    Mult::One,
                    "xs",
                    vect_of(&mut metas, Term::var(2), Term::var(1)),
                    vect_of(&mut metas, Term::var(3), c("succ").apply([Term::var(2)])),
                ),
            ),
        ),
    );
    declared(
        "Vect",
        &signature.declare_data(
            &mut metas,
            "Vect",
            1,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                pi(Mult::Zero, "n", c("Nat"), Term::Universe(level)),
            ),
            &[("vnil", vnil), ("vcons", vcons)],
        ),
    );
    signature
}

// ------------------------------------------------------------------ базовое

#[test]
fn a_data_declaration_populates_a_universe() {
    let signature = booleans();
    assert_eq!(
        infer_closed(&signature, &c("true")),
        Ok(c("Bool")),
        "конструктор синтезирует свой тип"
    );
    assert_eq!(
        infer_closed(&signature, &c("Bool")),
        Ok(Term::universe(0)),
        "сам тип живёт в объявленном универсуме"
    );
}

#[test]
fn constructors_are_recorded_in_declaration_order() {
    let signature = booleans();
    let recorded: Vec<&str> = signature
        .constructors("Bool")
        .expect("Bool индуктивен")
        .iter()
        .map(AsRef::as_ref)
        .collect();
    assert_eq!(
        recorded,
        ["true", "false"],
        "порядок задаёт ветви будущего `case`"
    );
}

#[test]
fn an_ordinary_definition_has_no_constructors() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate(&mut metas, "Opaque", Mult::Many, 0, Term::universe(0))
        .expect("постулат корректен");
    assert_eq!(
        signature.constructors("Opaque"),
        None,
        "постулат не индуктивный тип, и `case` по нему невозможен"
    );
}

#[test]
fn a_recursive_constructor_builds_a_tower() {
    let signature = naturals();
    let two = c("succ").apply([c("succ").apply([c("zero")])]);
    assert_eq!(infer_closed(&signature, &two), Ok(c("Nat")));
}

#[test]
fn constructors_do_not_reduce() {
    // Конструктор - постулат: тела нет, δ-редукции нет. `succ zero` и `zero`
    // остаются разными нормальными формами, иначе `Nat` был бы одноэлементным.
    let signature = naturals();
    let outcome = check_closed(&signature, &c("succ").apply([c("zero")]), &c("Nat"));
    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(
        matches!(
            check_closed(&signature, &c("zero"), &arrow(c("Nat"), c("Nat")),),
            Err(TypeError {
                kind: ErrorKind::Mismatch { .. },
                ..
            })
        ),
        "нулевой конструктор не функция"
    );
}

// ---------------------------------------------------------------- параметры

#[test]
fn a_parameter_may_live_above_the_type_it_parameterizes() {
    // `List : Type u -> Type u`, но `Type u : Type (u+1)`. Универсумная
    // проверка на параметры не распространяется - иначе полиморфного списка не
    // объявить вообще.
    let signature = lists();
    let arity = signature.lookup("List").expect("List объявлен").level_arity;
    assert_eq!(arity, 1, "уровень обобщён в параметр");
    assert_eq!(
        infer_closed(&signature, &Term::Const("List".into(), [u(0)].into())),
        Ok(pi(
            Mult::Zero,
            "A",
            Term::Universe(u(0)),
            Term::Universe(u(0))
        )),
        "дырки в объявлении стали одним параметром уровня"
    );
}

#[test]
fn a_parametric_constructor_applies_to_its_parameter() {
    let signature = lists();
    let empty = Term::Const("nil".into(), [Level::Zero].into()).apply([c("Bool")]);
    let single = Term::Const("cons".into(), [Level::Zero].into()).apply([
        c("Bool"),
        c("true"),
        empty.clone(),
    ]);
    let expected = Term::Const("List".into(), [Level::Zero].into()).apply([c("Bool")]);
    assert_eq!(infer_closed(&signature, &empty), Ok(expected.clone()));
    assert_eq!(infer_closed(&signature, &single), Ok(expected));
}

#[test]
fn a_parameter_must_be_repeated_verbatim() {
    // Кратность параметра - часть телескопа: `0` у типа и `ω` у конструктора
    // означали бы, что конструктор хранит то, чего в типе нет.
    let mut signature = naturals();
    let mut metas = Metas::default();
    let level = metas.fresh_level();
    let wrong = pi(
        Mult::Many,
        "A",
        Term::Universe(metas.fresh_level()),
        ahead("List", &mut metas, 1).apply([Term::var(0)]),
    );
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "List",
                1,
                pi(
                    Mult::Zero,
                    "A",
                    Term::Universe(level.clone()),
                    Term::Universe(level),
                ),
                &[("wrong", wrong)],
            ),
            Err(TypeError {
                kind: ErrorKind::ConstructorParameter { index: 0, .. },
                ..
            })
        ),
        "телескоп параметров обязан совпасть"
    );
}

#[test]
fn a_parameter_must_stay_the_same_under_recursion() {
    // `data Nest A where nest : Nest Bool -> Nest A` - параметр меняется, и
    // хранить его в значении уже нельзя. Это индекс, а не параметр.
    let mut signature = naturals();
    let mut metas = Metas::default();
    let nest = pi(
        Mult::Zero,
        "A",
        Term::universe(0),
        arrow(
            c("Nest").apply([c("Bool")]),
            c("Nest").apply([Term::var(1)]),
        ),
    );
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Nest",
                1,
                pi(Mult::Zero, "A", Term::universe(0), Term::universe(0)),
                &[("nest", nest)],
            ),
            Err(TypeError {
                kind: ErrorKind::NotStrictlyPositive { .. },
                ..
            })
        ),
        "неединообразный параметр отвергается"
    );
}

#[test]
fn declaring_more_parameters_than_binders_is_rejected() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(&mut metas, "Bool", 1, Term::universe(0), &[]),
            Err(TypeError {
                kind: ErrorKind::DataParameters {
                    expected: 1,
                    found: 0,
                    ..
                },
                ..
            })
        ),
        "параметров не может быть больше, чем связываний"
    );
}

// ------------------------------------------------------------------ индексы

#[test]
fn an_index_may_differ_between_constructors() {
    let signature = vectors();
    let one = Term::Const("vcons".into(), [Level::Zero].into()).apply([
        c("Bool"),
        c("zero"),
        c("true"),
        Term::Const("vnil".into(), [Level::Zero].into()).apply([c("Bool")]),
    ]);
    let expected = Term::Const("Vect".into(), [Level::Zero].into())
        .apply([c("Bool"), c("succ").apply([c("zero")])]);
    assert_eq!(infer_closed(&signature, &one), Ok(expected));
}

#[test]
fn an_index_is_checked_against_the_declared_length() {
    let signature = vectors();
    // `vcons` строит вектор длины `succ n`; сверять его с `Vect Bool zero`
    // нельзя, и именно на этом держится вся польза индекса.
    let one = Term::Const("vcons".into(), [Level::Zero].into()).apply([
        c("Bool"),
        c("zero"),
        c("true"),
        Term::Const("vnil".into(), [Level::Zero].into()).apply([c("Bool")]),
    ]);
    let wrong = Term::Const("Vect".into(), [Level::Zero].into()).apply([c("Bool"), c("zero")]);
    assert!(
        matches!(
            check_closed(&signature, &one, &wrong),
            Err(TypeError {
                kind: ErrorKind::Mismatch { .. },
                ..
            })
        ),
        "длина входит в тип"
    );
}

// -------------------------------------------------------------- позитивность

#[test]
fn a_negative_occurrence_is_rejected() {
    // `mk : (Bad -> Bad) -> Bad` даёт незавершающийся терм без единой рекурсии
    // в термах, а с ним - жителя любого типа.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Bad",
                0,
                Term::universe(0),
                &[("mk", arrow(arrow(c("Bad"), c("Bad")), c("Bad")))],
            ),
            Err(TypeError {
                kind: ErrorKind::NotStrictlyPositive { .. },
                ..
            })
        ),
        "слева от стрелки тип встречаться не может"
    );
}

#[test]
fn a_positive_occurrence_under_an_arrow_is_accepted() {
    // `node : (Bool -> Tree) -> Tree` - бесконечно ветвящееся дерево. Тип
    // справа от стрелки, и это законно.
    let mut signature = booleans();
    let mut metas = Metas::default();
    let outcome = signature.declare_data(
        &mut metas,
        "Tree",
        0,
        Term::universe(0),
        &[("node", arrow(arrow(c("Bool"), c("Tree")), c("Tree")))],
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_nested_occurrence_in_an_argument_is_rejected() {
    // `mk : Box (Box A) -> Box A` протаскивает тип в позицию, которую
    // синтаксическая проверка не контролирует. Консервативный отказ.
    let mut signature = booleans();
    let mut metas = Metas::default();
    let mk = pi(
        Mult::Zero,
        "A",
        Term::universe(0),
        arrow(
            c("Box").apply([c("Box").apply([Term::var(0)])]),
            c("Box").apply([Term::var(1)]),
        ),
    );
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Box",
                1,
                pi(Mult::Zero, "A", Term::universe(0), Term::universe(0)),
                &[("mk", mk)],
            ),
            Err(TypeError {
                kind: ErrorKind::NotStrictlyPositive { .. },
                ..
            })
        ),
        "рекурсивное вхождение под собственным аргументом отвергается"
    );
}

// ----------------------------------------------------------------- универсум

#[test]
fn a_field_above_the_type_is_rejected() {
    // Ровно это и есть импредикативность через data-декларацию: `Small` жил бы
    // в `Type 0`, а хранил бы обитателя `Type 0`, то есть значение из
    // `Type 1`. Дальше - парадокс Жирара.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Small",
                0,
                Term::universe(0),
                &[("pack", pi(Mult::Zero, "A", Term::universe(0), c("Small")))],
            ),
            Err(TypeError {
                kind: ErrorKind::ConstructorUniverse { .. },
                ..
            })
        ),
        "поле не может жить выше самого типа"
    );
}

#[test]
fn a_field_at_the_type_universe_is_accepted() {
    // Тот же `pack`, но тип объявлен в `Type 1` - и всё сходится.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.declare_data(
        &mut metas,
        "Large",
        0,
        Term::universe(1),
        &[("pack", pi(Mult::Zero, "A", Term::universe(0), c("Large")))],
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_concrete_field_fits_a_polymorphic_type() {
    // `Nat : Type 0` укладывается в `Type u` при любой подстановке `u`, потому
    // что уровни неотрицательны. Проверяет `Level::leq`, а не только его
    // тривиальный случай.
    let mut signature = naturals();
    let mut metas = Metas::default();
    let level = metas.fresh_level();
    let tag = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::One,
            "n",
            c("Nat"),
            ahead("Tagged", &mut metas, 1).apply([Term::var(1)]),
        ),
    );
    let outcome = signature.declare_data(
        &mut metas,
        "Tagged",
        1,
        pi(
            Mult::Zero,
            "A",
            Term::Universe(level.clone()),
            Term::Universe(level),
        ),
        &[("tag", tag)],
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

// ------------------------------------------------------------------- отказы

#[test]
fn a_type_former_must_end_in_a_universe() {
    let mut signature = naturals();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(&mut metas, "Odd", 0, arrow(c("Nat"), c("Nat")), &[]),
            Err(TypeError {
                kind: ErrorKind::NotADataSort { .. },
                ..
            })
        ),
        "тип-формер обязан заканчиваться универсумом"
    );
}

#[test]
fn a_constructor_must_return_its_own_type() {
    let mut signature = naturals();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Odd",
                0,
                Term::universe(0),
                &[("weird", c("Bool"))],
            ),
            Err(TypeError {
                kind: ErrorKind::ConstructorResult { .. },
                ..
            })
        ),
        "конструктор чужого типа не конструктор"
    );
}

#[test]
fn a_rejected_group_leaves_no_trace() {
    // Группа добавляется целиком или не добавляется вовсе: наблюдаемого
    // промежуточного состояния у сигнатуры нет (§10 вопрос 50).
    let mut signature = naturals();
    let mut metas = Metas::default();
    let before = signature.len();
    assert!(
        signature
            .declare_data(
                &mut metas,
                "Odd",
                0,
                Term::universe(0),
                &[("fine", c("Odd")), ("weird", c("Bool"))],
            )
            .is_err()
    );
    assert_eq!(signature.len(), before, "сигнатура не изменилась");
    assert!(signature.lookup("Odd").is_none(), "имя семейства свободно");
    assert!(
        signature.lookup("fine").is_none(),
        "и проверенный конструктор не остался"
    );
}

#[test]
fn a_group_colliding_with_an_existing_name_leaves_it_alone() {
    // Откат снимает имена группы, поэтому занятость проверяется до фаз: иначе
    // столкновение с `zero` снесло бы конструктор `Nat`, объявленный раньше.
    let mut signature = naturals();
    let mut metas = Metas::default();
    let before = signature.len();
    let group = Group::of(Member::data("Odd", 0, Term::universe(0))).and(Member::definition(
        "zero",
        Mult::Many,
        Term::universe(0),
    ));
    assert!(matches!(
        signature.declare(&mut metas, &group),
        Err(TypeError {
            kind: ErrorKind::DuplicateDefinition { .. },
            ..
        })
    ));
    assert_eq!(signature.len(), before, "сигнатура не изменилась");
    assert!(
        signature.lookup("zero").is_some(),
        "занятое имя осталось за прежним определением"
    );
}

#[test]
fn a_family_with_a_declared_arity_takes_polymorphic_constructors() {
    // Арность записана, значит параметры уровня уже стоят в типах как
    // `LevelVar` и обобщать нечего. Обобщение конструктора свело бы его
    // арность к нулю и отвергло бы всякий полиморфный конструктор объявленного
    // семейства - расхождением с арностью самого семейства.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let former = pi(
        Mult::Zero,
        "A",
        Term::Universe(u(0)),
        Term::Universe(u(0).succ()),
    );
    let pack = pi(
        Mult::Zero,
        "A",
        Term::Universe(u(0)),
        pi(
            Mult::Many,
            "x",
            Term::var(0),
            Term::Const("Box".into(), Rc::from([u(0)])).apply([Term::var(1)]),
        ),
    );
    let group = Group::of(
        Member::data("Box", 1, former)
            .with_arity(1)
            .with_constructor("pack", pack),
    );
    let outcome = signature.declare(&mut metas, &group);
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_data_name_cannot_be_reused() {
    let mut signature = naturals();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data(&mut metas, "Nat", 0, Term::universe(0), &[]),
            Err(TypeError {
                kind: ErrorKind::DuplicateDefinition { .. },
                ..
            })
        ),
        "имя типа занято"
    );
    assert!(
        matches!(
            signature.declare_data(
                &mut metas,
                "Other",
                0,
                Term::universe(0),
                &[("zero", c("Other"))],
            ),
            Err(TypeError {
                kind: ErrorKind::DuplicateDefinition { .. },
                ..
            })
        ),
        "имя конструктора тоже"
    );
}

#[test]
fn a_negative_occurrence_hidden_behind_a_definition_is_rejected() {
    // Позитивность синтаксическая, а определение - это ещё один синтаксис для
    // того же типа. `def G = Bad -> Bad` и следом `mk : G -> Bad` - после
    // δ-разворота ровно тот негативный конструктор, который отвергается в
    // прямой записи, и обходить проверку он не должен.
    //
    // Конфигурация выразима **только группой**: при ordered scoping (§4.8) `G`
    // не может стоять ни до `Bad` (не видит его), ни после (семейство уже
    // объявлено). Это и есть довод §10 вопроса 50 за разнородную группу.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.declare(
        &mut metas,
        &Group::of(
            Member::data("Bad", 0, Term::universe(0))
                .with_constructor("mk", arrow(c("G"), c("Bad"))),
        )
        .and(
            Member::definition("G", Mult::Many, Term::universe(0))
                .with_body(arrow(c("Bad"), c("Bad"))),
        ),
    );
    assert!(
        matches!(
            outcome,
            Err(TypeError {
                kind: ErrorKind::NotStrictlyPositive { .. },
                ..
            })
        ),
        "негативность за определением обязана отвергаться так же, как прямая: {outcome:?}"
    );
}

#[test]
fn a_definition_free_of_the_type_stays_usable_as_a_field() {
    // Контроль к предыдущему тесту: запрет касается определений, упоминающих
    // сам тип, а не определений вообще.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define_inferred(
            &mut metas,
            "Unit",
            Mult::Many,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .expect("определение корректно");
    assert!(
        signature
            .declare_data(
                &mut metas,
                "Wrap",
                0,
                Term::universe(1),
                &[("wrap", arrow(c("Unit"), c("Wrap")))],
            )
            .is_ok(),
        "поле-определение, не упоминающее тип, законно"
    );
}

#[test]
fn a_positive_occurrence_behind_a_definition_is_accepted() {
    // `def Cont = Bool -> Tree` и записанное буквально `(Bool -> Tree)` - один
    // и тот же тип после δ, и позитивность обязана отвечать на них одинаково.
    let mut signature = booleans();
    let mut metas = Metas::default();
    let outcome = signature.declare(
        &mut metas,
        &Group::of(
            Member::data("Tree", 0, Term::universe(0))
                .with_constructor("node", arrow(arrow(c("Bool"), c("Tree")), c("Tree")))
                .with_constructor("node2", arrow(c("Cont"), c("Tree"))),
        )
        .and(
            Member::definition("Cont", Mult::Many, Term::universe(0))
                .with_body(arrow(c("Bool"), c("Tree"))),
        ),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_self_referential_definition_does_not_loop_the_positivity_check() {
    // Разворот головы поля обязан помнить уже развёрнутое: `def Loop = D`
    // ссылается на разбираемое семейство, и без памяти обход не закончился бы.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let outcome = signature.declare(
        &mut metas,
        &Group::of(
            Member::data("D", 0, Term::universe(0))
                .with_constructor("mk", arrow(c("Loop"), c("D"))),
        )
        .and(Member::definition("Loop", Mult::Many, Term::universe(0)).with_body(c("D"))),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_chain_of_definitions_is_walked_once_per_name() {
    // Проверка позитивности разворачивает тела определений, и память об уже
    // развёрнутых обязана быть множеством посещённых, а не стеком текущего
    // пути. Со стеком `d_k = d_{k-1} -> d_{k-1}` обходится за 2^k: цепочка из
    // 25 занимала 17 секунд, из 32 - не заканчивается вовсе.
    //
    // Порог намеренно на три порядка выше фактического времени: тест ловит
    // смену асимптотики, а не колебания машины.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .define_inferred(
            &mut metas,
            "Unit",
            Mult::Many,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .expect("Unit корректен");
    signature
        .define_inferred(
            &mut metas,
            "d0",
            Mult::Many,
            Term::universe(1),
            Some(c("Unit")),
        )
        .expect("d0 корректен");
    for step in 1..=32 {
        let previous = format!("d{}", step - 1);
        signature
            .define_inferred(
                &mut metas,
                &format!("d{step}"),
                Mult::Many,
                Term::universe(1),
                Some(arrow(c(&previous), c(&previous))),
            )
            .expect("звено цепочки корректно");
    }

    let started = std::time::Instant::now();
    let outcome = signature.declare_data(
        &mut metas,
        "Chain",
        0,
        Term::universe(1),
        &[("link", arrow(c("d32"), c("Chain")))],
    );
    let elapsed = started.elapsed();

    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "обход занял {elapsed:?} - память о развёрнутых телах перестала работать"
    );
}

#[test]
fn a_denormalised_level_in_the_result_is_still_the_family() {
    // `max u u` и `u` - один уровень, и результат конструктора обязан
    // сравниваться семантически. Запись эта возникает не вручную: дырка,
    // решённая в `max ?a ?b`, после позднего `?a := ?b` зонкается в `max ?b ?b`
    // и обобщается в `max u0 u0`.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let carrier = metas.fresh_level();
    signature
        .postulate_inferred(&mut metas, "E", Mult::Many, Term::Universe(carrier))
        .expect("E корректен");

    let sort = metas.fresh_level();
    let field = metas.fresh_level();
    let doubled = field.clone().max(field.clone());
    let outcome = signature.declare_data(
        &mut metas,
        "D",
        0,
        Term::Universe(sort),
        &[(
            "mk",
            pi(
                Mult::Zero,
                "_",
                Term::Const("E".into(), Rc::from([field])),
                Term::Const("D".into(), Rc::from([doubled])),
            ),
        )],
    );
    assert!(
        outcome.is_ok(),
        "`D{{max u0 u0}}` - то же семейство, что `D{{u0}}`: {outcome:?}"
    );
}

// ------------------------------------------------------------------ свойства

/// Формы полей, из которых собираются конструкторы: часть законна, часть нет.
///
/// Генератор нарочно смешивает и то и другое: интересен не столько принятый
/// конструктор, сколько граница - что именно проверка пропускает.
#[derive(Clone, Debug)]
enum Field {
    /// Само `D` - прямая рекурсия, законна.
    Recursive,
    /// `D -> D` - негативное вхождение, незаконно.
    Negative,
    /// `Unit -> D` - положительное вхождение под стрелкой, законно.
    PositiveUnderArrow,
    /// `Alias`, где `Alias = D -> D` - та же негативность за определением.
    HiddenNegative,
    /// `Unit` - тип, не упоминающий `D` вовсе.
    Neutral,
}

fn any_field() -> impl Strategy<Value = Field> {
    prop_oneof![
        Just(Field::Recursive),
        Just(Field::Negative),
        Just(Field::PositiveUnderArrow),
        Just(Field::HiddenNegative),
        Just(Field::Neutral),
    ]
}

fn field_term(field: &Field) -> Term {
    match field {
        Field::Recursive => c("D"),
        Field::Negative => arrow(c("D"), c("D")),
        Field::PositiveUnderArrow => arrow(c("Unit"), c("D")),
        Field::HiddenNegative => c("Alias"),
        Field::Neutral => c("Unit"),
    }
}

/// `Unit`, `Alias = D -> D` - всё, что нужно полям, кроме самого `D`.
///
/// Само `D` объявляется в тесте вместе с конструктором: список конструкторов
/// принадлежит группе, и добавить его отдельно нечем.
fn playground(metas: &mut Metas) -> Signature {
    let mut signature = Signature::default();
    let add = |outcome: Result<(), TypeError>| assert!(outcome.is_ok(), "{outcome:?}");
    add(signature.define_inferred(
        metas,
        "Unit",
        Mult::Many,
        Term::universe(1),
        Some(Term::universe(0)),
    ));
    signature
}

/// Группа `D` с единственным конструктором `mk` и синонимом `Alias = D -> D`.
///
/// Разнородная по необходимости: `Alias` упоминает `D`, поэтому вне группы он
/// не пишется (§10 вопрос 50).
fn with_carrier(field: Term) -> Group {
    Group::of(Member::data("D", 0, Term::universe(0)).with_constructor("mk", field)).and(
        Member::definition("Alias", Mult::Many, Term::universe(0)).with_body(arrow(c("D"), c("D"))),
    )
}

/// Развернуть определения в поле - так видно, что проверка увидела бы, если бы
/// смотрела на δ-нормальную форму, а не на запись.
fn unfolded(field: &Field) -> Term {
    match field {
        Field::HiddenNegative => arrow(c("D"), c("D")),
        other => field_term(other),
    }
}

/// Есть ли `D` слева от стрелки.
fn has_negative_occurrence(term: &Term) -> bool {
    fn mentions_d(term: &Term) -> bool {
        match term {
            Term::Record(_)
            | Term::Row(_)
            | Term::RowKind(_)
            | Term::Object(_)
            | Term::With(..)
            | Term::Project(..) => {
                unreachable!("генератор термов записей не порождает")
            }
            Term::Const(name, _) => &**name == "D",
            Term::Pi(_, _, domain, _, codomain) => mentions_d(domain) || mentions_d(codomain),
            Term::App(a, b) => mentions_d(a) || mentions_d(b),
            Term::Lam(_, _, body) => mentions_d(body),
            Term::Let(_, _, ty, value, body) => {
                mentions_d(ty) || mentions_d(value) || mentions_d(body)
            }
            Term::Case(_) => unreachable!("генератор полей не порождает разбор"),
            Term::Var(_) | Term::Universe(_) | Term::Meta(_) => false,
        }
    }
    match term {
        Term::Pi(_, _, domain, _, codomain) => {
            mentions_d(domain) || has_negative_occurrence(codomain)
        }
        _ => false,
    }
}

proptest! {
    /// Принятый конструктор не содержит `D` слева от стрелки **после разворота
    /// определений**.
    ///
    /// Позитивность синтаксическая, а определение - ещё одна запись того же
    /// типа. Свойство смотрит на развёрнутую форму, поэтому ловит попытку
    /// спрятать негативное вхождение за именем.
    #[test]
    fn an_accepted_constructor_has_no_negative_occurrence(fields in proptest::collection::vec(any_field(), 1..4)) {
        let mut metas = Metas::default();
        let mut signature = playground(&mut metas);

        let ty = fields
            .iter()
            .rev()
            .fold(c("D"), |acc, field| arrow(field_term(field), acc));

        if signature.declare(&mut metas, &with_carrier(ty)).is_ok() {
            for field in &fields {
                prop_assert!(
                    !has_negative_occurrence(&unfolded(field)),
                    "принято поле с негативным вхождением: {:?}", field
                );
            }
        }
    }

    /// Отвергнутая группа не оставляет следа в сигнатуре.
    ///
    /// Половинчатое объявление хуже отказа: имя занято, а типа за ним нет.
    #[test]
    fn a_rejected_group_leaves_nothing_behind(fields in proptest::collection::vec(any_field(), 1..4)) {
        let mut metas = Metas::default();
        let mut signature = playground(&mut metas);

        let ty = fields
            .iter()
            .rev()
            .fold(c("D"), |acc, field| arrow(field_term(field), acc));

        if signature.declare(&mut metas, &with_carrier(ty)).is_err() {
            prop_assert!(signature.lookup("mk").is_none());
            prop_assert!(signature.lookup("D").is_none(), "и само семейство тоже");
            prop_assert!(signature.lookup("Alias").is_none(), "и сосед по группе");
        }
    }
}

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

use adamas_core::check::{TypeError, check_closed, infer_closed};
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use proptest::prelude::*;

// -------------------------------------------------------------- конструкторы

fn pi(mult: Mult, name: &str, domain: Term, codomain: Term) -> Term {
    Term::Pi(mult, name.into(), Rc::new(domain), Rc::new(codomain))
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

/// Ссылка на определение со свежими дырками вместо аргументов уровня.
fn at(signature: &Signature, name: &str, metas: &mut Metas) -> Term {
    signature
        .instantiate(name, metas)
        .unwrap_or_else(|| panic!("{name} объявлен"))
}

/// `Bool : Type 0` с двумя конструкторами - минимальный перечислимый тип.
fn booleans() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    declared(
        "Bool",
        &signature.declare_data("Bool", 0, &mut metas, Term::universe(0)),
    );
    for name in ["true", "false"] {
        declared(
            name,
            &signature.declare_constructor("Bool", name, &mut metas, c("Bool")),
        );
    }
    signature
}

/// `Nat : Type 0` поверх `Bool` - первый рекурсивный тип.
fn naturals() -> Signature {
    let mut signature = booleans();
    let mut metas = Metas::default();
    declared(
        "Nat",
        &signature.declare_data("Nat", 0, &mut metas, Term::universe(0)),
    );
    declared(
        "zero",
        &signature.declare_constructor("Nat", "zero", &mut metas, c("Nat")),
    );
    declared(
        "succ",
        &signature.declare_constructor("Nat", "succ", &mut metas, arrow(c("Nat"), c("Nat"))),
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
    declared(
        "List",
        &signature.declare_data(
            "List",
            1,
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
        ),
    );

    let list_of = |signature: &Signature, metas: &mut Metas, element: Term| {
        at(signature, "List", metas).apply([element])
    };

    let nil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        list_of(&signature, &mut metas, Term::var(0)),
    );
    declared(
        "nil",
        &signature.declare_constructor("List", "nil", &mut metas, nil),
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
                list_of(&signature, &mut metas, Term::var(1)),
                list_of(&signature, &mut metas, Term::var(2)),
            ),
        ),
    );
    declared(
        "cons",
        &signature.declare_constructor("List", "cons", &mut metas, cons),
    );
    signature
}

/// `Vect : (0 A : Type u) -> (0 n : Nat) -> Type u` - параметр и индекс рядом.
fn vectors() -> Signature {
    let mut signature = naturals();
    let mut metas = Metas::default();

    let level = metas.fresh_level();
    declared(
        "Vect",
        &signature.declare_data(
            "Vect",
            1,
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                pi(Mult::Zero, "n", c("Nat"), Term::Universe(level)),
            ),
        ),
    );

    let vect_of = |signature: &Signature, metas: &mut Metas, element: Term, length: Term| {
        at(signature, "Vect", metas).apply([element, length])
    };

    let vnil = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        vect_of(&signature, &mut metas, Term::var(0), c("zero")),
    );
    declared(
        "vnil",
        &signature.declare_constructor("Vect", "vnil", &mut metas, vnil),
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
                    vect_of(&signature, &mut metas, Term::var(2), Term::var(1)),
                    vect_of(
                        &signature,
                        &mut metas,
                        Term::var(3),
                        c("succ").apply([Term::var(2)]),
                    ),
                ),
            ),
        ),
    );
    declared(
        "vcons",
        &signature.declare_constructor("Vect", "vcons", &mut metas, vcons),
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
    signature
        .postulate("Opaque", Mult::Many, 0, Term::universe(0))
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
            Err(TypeError::Mismatch { .. })
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
    let mut signature = lists();
    let mut metas = Metas::default();
    let wrong = pi(
        Mult::Many,
        "A",
        Term::Universe(metas.fresh_level()),
        signature
            .instantiate("List", &mut metas)
            .expect("List объявлен")
            .apply([Term::var(0)]),
    );
    assert!(
        matches!(
            signature.declare_constructor("List", "wrong", &mut metas, wrong),
            Err(TypeError::ConstructorParameter { index: 0, .. })
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
    signature
        .declare_data(
            "Nest",
            1,
            &mut metas,
            pi(Mult::Zero, "A", Term::universe(0), Term::universe(0)),
        )
        .expect("Nest корректен");
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
            signature.declare_constructor("Nest", "nest", &mut metas, nest),
            Err(TypeError::NotStrictlyPositive { .. })
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
            signature.declare_data("Bool", 1, &mut metas, Term::universe(0)),
            Err(TypeError::DataParameters {
                expected: 1,
                found: 0,
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
            Err(TypeError::Mismatch { .. })
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
    signature
        .declare_data("Bad", 0, &mut metas, Term::universe(0))
        .expect("тип-формер корректен");
    assert!(
        matches!(
            signature.declare_constructor(
                "Bad",
                "mk",
                &mut metas,
                arrow(arrow(c("Bad"), c("Bad")), c("Bad")),
            ),
            Err(TypeError::NotStrictlyPositive { .. })
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
    signature
        .declare_data("Tree", 0, &mut metas, Term::universe(0))
        .expect("Tree корректен");
    let outcome = signature.declare_constructor(
        "Tree",
        "node",
        &mut metas,
        arrow(arrow(c("Bool"), c("Tree")), c("Tree")),
    );
    assert!(outcome.is_ok(), "{outcome:?}");
}

#[test]
fn a_nested_occurrence_in_an_argument_is_rejected() {
    // `mk : Box (Box A) -> Box A` протаскивает тип в позицию, которую
    // синтаксическая проверка не контролирует. Консервативный отказ.
    let mut signature = booleans();
    let mut metas = Metas::default();
    signature
        .declare_data(
            "Box",
            1,
            &mut metas,
            pi(Mult::Zero, "A", Term::universe(0), Term::universe(0)),
        )
        .expect("Box корректен");
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
            signature.declare_constructor("Box", "mk", &mut metas, mk),
            Err(TypeError::NotStrictlyPositive { .. })
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
    signature
        .declare_data("Small", 0, &mut metas, Term::universe(0))
        .expect("Small корректен");
    assert!(
        matches!(
            signature.declare_constructor(
                "Small",
                "pack",
                &mut metas,
                pi(Mult::Zero, "A", Term::universe(0), c("Small")),
            ),
            Err(TypeError::ConstructorUniverse { .. })
        ),
        "поле не может жить выше самого типа"
    );
}

#[test]
fn a_field_at_the_type_universe_is_accepted() {
    // Тот же `pack`, но тип объявлен в `Type 1` - и всё сходится.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .declare_data("Large", 0, &mut metas, Term::universe(1))
        .expect("Large корректен");
    let outcome = signature.declare_constructor(
        "Large",
        "pack",
        &mut metas,
        pi(Mult::Zero, "A", Term::universe(0), c("Large")),
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
    signature
        .declare_data(
            "Tagged",
            1,
            &mut metas,
            pi(
                Mult::Zero,
                "A",
                Term::Universe(level.clone()),
                Term::Universe(level),
            ),
        )
        .expect("Tagged корректен");
    let tag = pi(
        Mult::Zero,
        "A",
        Term::Universe(metas.fresh_level()),
        pi(
            Mult::One,
            "n",
            c("Nat"),
            signature
                .instantiate("Tagged", &mut metas)
                .expect("Tagged объявлен")
                .apply([Term::var(1)]),
        ),
    );
    let outcome = signature.declare_constructor("Tagged", "tag", &mut metas, tag);
    assert!(outcome.is_ok(), "{outcome:?}");
}

// ------------------------------------------------------------------- отказы

#[test]
fn a_type_former_must_end_in_a_universe() {
    let mut signature = naturals();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data("Odd", 0, &mut metas, arrow(c("Nat"), c("Nat"))),
            Err(TypeError::NotADataSort { .. })
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
            signature.declare_constructor("Nat", "weird", &mut metas, c("Bool")),
            Err(TypeError::ConstructorResult { .. })
        ),
        "конструктор чужого типа не конструктор"
    );
}

#[test]
fn a_constructor_needs_an_inductive_type() {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .postulate("Opaque", Mult::Many, 0, Term::universe(0))
        .expect("постулат корректен");
    assert!(
        matches!(
            signature.declare_constructor("Opaque", "mk", &mut metas, c("Opaque")),
            Err(TypeError::NotADataType { .. })
        ),
        "у постулата конструкторов быть не может"
    );
    assert!(
        matches!(
            signature.declare_constructor("Missing", "mk", &mut metas, Term::universe(0)),
            Err(TypeError::UnknownConstant { .. })
        ),
        "и у несуществующего имени тоже"
    );
}

#[test]
fn a_rejected_constructor_leaves_no_trace() {
    let mut signature = naturals();
    let before = signature.len();
    let mut metas = Metas::default();
    assert!(
        signature
            .declare_constructor("Nat", "weird", &mut metas, c("Bool"))
            .is_err()
    );
    assert_eq!(signature.len(), before, "сигнатура не изменилась");
    assert!(signature.lookup("weird").is_none(), "имя свободно");
    assert_eq!(
        signature.constructors("Nat").expect("Nat индуктивен").len(),
        2,
        "список конструкторов не пополнился"
    );
}

#[test]
fn a_data_name_cannot_be_reused() {
    let mut signature = naturals();
    let mut metas = Metas::default();
    assert!(
        matches!(
            signature.declare_data("Nat", 0, &mut metas, Term::universe(0)),
            Err(TypeError::DuplicateDefinition { .. })
        ),
        "имя типа занято"
    );
    assert!(
        matches!(
            signature.declare_constructor("Nat", "zero", &mut metas, c("Nat")),
            Err(TypeError::DuplicateDefinition { .. })
        ),
        "имя конструктора тоже"
    );
}

#[test]
fn a_negative_occurrence_hidden_behind_a_definition_is_rejected() {
    // Позитивность синтаксическая, а определение - это ещё один синтаксис для
    // того же типа. `def G : Type 0 = Bad -> Bad` и следом `mk : G -> Bad` -
    // после δ-разворота ровно тот негативный конструктор, который отвергается
    // в прямой записи, и обходить проверку он не должен.
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    signature
        .declare_data("Bad", 0, &mut metas, Term::universe(0))
        .expect("тип-формер корректен");
    signature
        .define_inferred(
            "G",
            Mult::Many,
            &mut metas,
            Term::universe(0),
            Some(arrow(c("Bad"), c("Bad"))),
        )
        .expect("определение корректно само по себе");

    assert!(
        matches!(
            signature.declare_constructor("Bad", "mk", &mut metas, arrow(c("G"), c("Bad"))),
            Err(TypeError::NotStrictlyPositive { .. })
        ),
        "негативность за определением обязана отвергаться так же, как прямая"
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
            "Unit",
            Mult::Many,
            &mut metas,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .expect("определение корректно");
    signature
        .declare_data("Wrap", 0, &mut metas, Term::universe(1))
        .expect("тип-формер корректен");

    assert!(
        signature
            .declare_constructor("Wrap", "wrap", &mut metas, arrow(c("Unit"), c("Wrap")))
            .is_ok(),
        "поле-определение, не упоминающее тип, законно"
    );
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
            "Unit",
            Mult::Many,
            &mut metas,
            Term::universe(1),
            Some(Term::universe(0)),
        )
        .expect("Unit корректен");
    signature
        .define_inferred(
            "d0",
            Mult::Many,
            &mut metas,
            Term::universe(1),
            Some(c("Unit")),
        )
        .expect("d0 корректен");
    for step in 1..=32 {
        let previous = format!("d{}", step - 1);
        signature
            .define_inferred(
                &format!("d{step}"),
                Mult::Many,
                &mut metas,
                Term::universe(1),
                Some(arrow(c(&previous), c(&previous))),
            )
            .expect("звено цепочки корректно");
    }
    signature
        .declare_data("Chain", 0, &mut metas, Term::universe(1))
        .expect("тип-формер корректен");

    let started = std::time::Instant::now();
    let outcome =
        signature.declare_constructor("Chain", "link", &mut metas, arrow(c("d32"), c("Chain")));
    let elapsed = started.elapsed();

    assert!(outcome.is_ok(), "{outcome:?}");
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "обход занял {elapsed:?} - память о развёрнутых телах перестала работать"
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

/// Сигнатура с `Unit`, `D` и `Alias = D -> D`.
fn playground(metas: &mut Metas) -> Signature {
    let mut signature = Signature::default();
    let add = |outcome: Result<(), TypeError>| assert!(outcome.is_ok(), "{outcome:?}");
    add(signature.define_inferred(
        "Unit",
        Mult::Many,
        metas,
        Term::universe(1),
        Some(Term::universe(0)),
    ));
    add(signature.declare_data("D", 0, metas, Term::universe(0)));
    add(signature.define_inferred(
        "Alias",
        Mult::Many,
        metas,
        Term::universe(0),
        Some(arrow(c("D"), c("D"))),
    ));
    signature
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
            Term::Const(name, _) => &**name == "D",
            Term::Pi(_, _, domain, codomain) => mentions_d(domain) || mentions_d(codomain),
            Term::App(a, b) => mentions_d(a) || mentions_d(b),
            Term::Lam(_, _, body) => mentions_d(body),
            Term::Let(_, _, ty, value, body) => {
                mentions_d(ty) || mentions_d(value) || mentions_d(body)
            }
            Term::Case(_) => unreachable!("генератор полей не порождает разбор"),
            Term::Var(_) | Term::Universe(_) => false,
        }
    }
    match term {
        Term::Pi(_, _, domain, codomain) => mentions_d(domain) || has_negative_occurrence(codomain),
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

        if signature.declare_constructor("D", "mk", &mut metas, ty).is_ok() {
            for field in &fields {
                prop_assert!(
                    !has_negative_occurrence(&unfolded(field)),
                    "принято поле с негативным вхождением: {:?}", field
                );
            }
        }
    }

    /// Отвергнутый конструктор не оставляет следа в сигнатуре.
    ///
    /// Половинчатое объявление хуже отказа: имя занято, а типа за ним нет.
    #[test]
    fn a_rejected_constructor_leaves_nothing_behind(fields in proptest::collection::vec(any_field(), 1..4)) {
        let mut metas = Metas::default();
        let mut signature = playground(&mut metas);

        let ty = fields
            .iter()
            .rev()
            .fold(c("D"), |acc, field| arrow(field_term(field), acc));

        if signature.declare_constructor("D", "mk", &mut metas, ty).is_err() {
            prop_assert!(signature.lookup("mk").is_none());
            prop_assert!(
                signature.constructors("D").is_some_and(<[_]>::is_empty),
                "список конструкторов не должен пополняться"
            );
        }
    }
}

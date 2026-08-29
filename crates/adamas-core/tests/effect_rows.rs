//! Row эффектов как поле `Pi` (§3.2, §3.4, §9 Фаза 2).
//!
//! Правил у row сегодня нет - они Фаза 4, - но представление есть, и всё, что
//! ходит по терму, обязано в неё заходить. Проверяется здесь именно это:
//! пропуск обхода не увидит ни один снапшот и ни одна программа, потому что
//! синтаксиса для непустой row не существует. Собрать её можно только отсюда.
//!
//! Что уже проверено в другом месте: сравнение row конвертируемостью и
//! канонический порядок меток - unit-тесты `conv`, печать - unit-тесты `term`.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, TypeError};
use adamas_core::eval::normalize;
use adamas_core::level::{Level, LevelVar};
use adamas_core::meta::{Generalization, Metas, unsolved_level_meta, zonk_term};
use adamas_core::mult::Mult;
use adamas_core::row::{Label, Row};
use adamas_core::sig::Signature;
use adamas_core::term::{Binder, Term};

/// `(ω _ : domain) -> row codomain`.
fn rowed(row: Row<Term>, domain: Term, codomain: Term) -> Term {
    Term::Pi(
        Binder::explicit(Mult::Many),
        "_".into(),
        Rc::new(domain),
        row,
        Rc::new(codomain),
    )
}

/// Row из одной метки с одним аргументом.
fn effect(name: &str, argument: Term) -> Row<Term> {
    Row::new([Label {
        name: name.into(),
        arguments: vec![argument],
    }])
}

/// Терм, у которого весь интерес спрятан в метке: домен и кодомен заведомо
/// закрыты и заведомо ни на что не влияют.
fn only_in_a_label(argument: Term) -> Term {
    rowed(
        effect("State", argument),
        Term::universe(0),
        Term::universe(0),
    )
}

/// Аргумент единственной метки.
fn label_argument(term: &Term) -> &Term {
    let Term::Pi(_, _, _, row, _) = term else {
        panic!("терм собран как `Pi`")
    };
    let [label] = row.labels() else {
        panic!("метка одна")
    };
    let [argument] = &label.arguments[..] else {
        panic!("аргумент один")
    };
    argument
}

#[test]
fn substituting_levels_reaches_a_label_argument() {
    // Тип определения инстанцируется в месте использования подстановкой
    // уровней; метка, которую подстановка обошла бы, осталась бы с параметром
    // вместо аргумента.
    let term = only_in_a_label(Term::Universe(Level::Var(LevelVar(0))));
    let substituted = term.substitute_levels(&[Level::number(3)]);
    assert_eq!(label_argument(&substituted).to_string(), "Type 3");
}

#[test]
fn a_level_parameter_only_in_a_label_still_counts() {
    // `max_level_var` считает арность параметров уровня. Пропусти она метку -
    // арность вышла бы меньше, а `Const` с недостающим аргументом даёт
    // `LevelArity` в лучшем случае и неверную подстановку в худшем.
    let term = only_in_a_label(Term::Universe(Level::Var(LevelVar(2))));
    assert_eq!(term.max_level_var(), Some(2));
}

#[test]
fn zonking_and_generalisation_reach_a_label_argument() {
    let mut metas = Metas::default();
    let hole = metas.fresh_level();
    let term = only_in_a_label(Term::Universe(hole.clone()));

    // Нерешённая дырка внутри метки обязана быть видна: иначе обобщение не
    // сделает её параметром, а `check` не откажет там, где обобщать нельзя.
    assert!(unsolved_level_meta(&metas, &term).is_some());
    let mut generalization = Generalization::default();
    generalization.collect_term(&metas, &term);
    assert_eq!(generalization.arity(), 1, "дырка в метке - параметр уровня");

    // А решённая обязана быть подставлена: незонканная дырка в сохранённой
    // ошибке протухает вместе с `base` хранилища (§10 вопрос 51).
    assert!(metas.unify_levels(&hole, &Level::number(1)));
    assert_eq!(
        label_argument(&zonk_term(&metas, &term)).to_string(),
        "Type 1"
    );
}

#[test]
fn evaluation_and_quoting_round_trip_a_row() {
    // Аргументы метки - обычные термы, и вычисляются как всё прочее. Редекс в
    // метке, доживший до нормальной формы, означал бы, что `eval` в неё не
    // зашла, а `quote` вернула не то, что вычисляла.
    let identity = Term::Lam(Mult::Many, "y".into(), Rc::new(Term::var(0)));
    let redex = identity.apply([Term::universe(0)]);
    let normalized = normalize(&only_in_a_label(redex));
    assert_eq!(label_argument(&normalized).to_string(), "Type 0");
    assert_eq!(
        normalized.to_string(),
        "(ω _ : Type 0) -> {State Type 0} Type 0"
    );
}

/// `Bool : Type 0` - обитаемый тип, которым заполняются позиции, к делу не
/// относящиеся.
fn booleans() -> Signature {
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let declared = signature.declare_data(
        &mut metas,
        "Bool",
        0,
        Term::universe(0),
        &[("False", Term::constant("Bool"))],
    );
    assert!(
        declared.is_ok(),
        "перечислимый тип объявляется: {declared:?}"
    );
    signature
}

fn refused(constructor: Term) -> bool {
    let mut signature = booleans();
    let mut metas = Metas::default();
    matches!(
        signature.declare_data(
            &mut metas,
            "Bad",
            0,
            Term::universe(0),
            &[("mk", constructor)],
        ),
        Err(TypeError {
            kind: ErrorKind::NotStrictlyPositive { .. },
            ..
        })
    )
}

/// `Bool -> {State Bad} Bool` - стрелка, упоминающая тип **только** меткой.
fn hiding_place() -> Term {
    rowed(
        effect("State", Term::constant("Bad")),
        Term::constant("Bool"),
        Term::constant("Bool"),
    )
}

// Три места, откуда метка видна по-разному, и каждое проверяет свой обход.
// Осторожность здесь сознательная: положительна метка или нет, решают операции
// эффекта, а их объявление - Фаза 4. Пока позиция метки считается той же, что
// у домена.

#[test]
fn a_label_in_a_field_type_is_a_negative_occurrence() {
    // `mk : (Bool -> {State Bad} Bool) -> Bad` - проверка позитивности идёт по
    // типу поля и упирается в стрелку с меткой.
    assert!(refused(rowed(
        Row::empty(),
        hiding_place(),
        Term::constant("Bad")
    )));
}

#[test]
fn a_label_deeper_in_a_field_type_is_found_too() {
    // `mk : ((Bool -> {State Bad} Bool) -> Bool) -> Bad` - здесь позитивность
    // до метки не спускается, а спрашивает «упоминается ли тип в домене», и
    // ответить обязана «да».
    let deeper = rowed(Row::empty(), hiding_place(), Term::constant("Bool"));
    assert!(refused(rowed(Row::empty(), deeper, Term::constant("Bad"))));
}

#[test]
fn a_label_on_the_constructors_own_arrow_is_found_too() {
    // `mk : Bool -> {State Bad} Bad` - метка стоит на стрелке самого
    // конструктора, а телескоп снимается по доменам, и метку легко потерять по
    // дороге.
    assert!(refused(rowed(
        effect("State", Term::constant("Bad")),
        Term::constant("Bool"),
        Term::constant("Bad"),
    )));
}

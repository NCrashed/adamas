//! Записи как телескоп полей (§4.2).
//!
//! Проверяется не форма терма, а то, что из неё следует: проекция **вычисляет**,
//! тип зависимого поля подставляет значения предыдущих, а универсум записи
//! вмещает универсумы полей.
//!
//! Row-полиморфизма здесь нет и не проверяется: решение от 2026-08-29 - запись
//! с зависимостью между полями закрыта, а полиморфизм над независимой приезжает
//! отдельным срезом.

use std::rc::Rc;

use adamas_core::check::{ErrorKind, check_closed, infer_closed};
use adamas_core::eval::normalize;
use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::{Field, Fields, Term};

/// Поле кратности `1` - умолчание §4.1.
fn field(name: &str, ty: Term) -> Field {
    Field {
        name: name.into(),
        mult: Mult::One,
        ty: Rc::new(ty),
    }
}

/// `{ name = value, … }`.
fn object(fields: &[(&str, Term)]) -> Term {
    Term::Object(
        fields
            .iter()
            .map(|(name, value)| ((*name).into(), Rc::new(value.clone())))
            .collect(),
    )
}

/// Тип терма в пустой сигнатуре, приведённый к нормальной форме.
fn typing(term: &Term) -> Term {
    let signature = Signature::default();
    match infer_closed(&signature, term) {
        Ok(ty) => normalize(&ty),
        Err(error) => panic!("не типизировалось: {error:?}"),
    }
}

#[test]
fn a_projection_computes() {
    // `{ a = Type 0, b = Type 1 }.b` сводится к `Type 1`: проекция - обычная
    // элиминация, и на построенной записи она срабатывает вычислением.
    let record = object(&[("a", Term::universe(0)), ("b", Term::universe(1))]);
    let projected = Term::Project(Rc::new(record), "b".into());
    assert_eq!(
        normalize(&projected).to_string(),
        normalize(&Term::universe(1)).to_string()
    );
}

#[test]
fn a_record_lives_where_its_fields_do() {
    // Универсум записи - максимум по полям, как у `Pi`. `{ a : Type 0 }` живёт
    // в `Type 1`, потому что `Type 0` живёт там.
    let ty = Term::Record(Fields::closed(Rc::from([field("a", Term::universe(0))])));
    assert_eq!(typing(&ty).to_string(), "Type 1");

    let higher = Term::Record(Fields::closed(Rc::from([
        field("a", Term::universe(0)),
        field("b", Term::universe(3)),
    ])));
    assert_eq!(typing(&higher).to_string(), "Type 4");
}

#[test]
fn the_type_of_a_later_field_sees_the_earlier_ones() {
    // Зависимое поле: `{ t : Type 2, x : t }`. Тип `x` - это **значение** поля
    // `t`, а не переменная, поэтому проверка записи подставляет туда уже
    // проверенное значение.
    let ty = Term::Record(Fields::closed(Rc::from([
        field("t", Term::universe(2)),
        field("x", Term::var(0)),
    ])));
    let signature = Signature::default();

    // `t = Type 1` делает типом `x` именно `Type 1`, и `Type 0` его населяет.
    let fits = object(&[("t", Term::universe(1)), ("x", Term::universe(0))]);
    let outcome = check_closed(&signature, &fits, &ty);
    assert!(outcome.is_ok(), "{outcome:?}");

    // То же значение `x` при другом `t` уже не подходит: `Type 1` не населяет
    // сам себя. Отказ приходит на **втором** поле - там, где зависимость.
    let broken = object(&[("t", Term::universe(1)), ("x", Term::universe(1))]);
    let outcome = check_closed(&signature, &broken, &ty);
    assert!(outcome.is_err(), "предикативность: {outcome:?}");
}

#[test]
fn a_projection_of_a_dependent_field_carries_the_earlier_ones() {
    // `r.x` при `r : { t : Type 2, x : t }` имеет тип `r.t`, а не переменную:
    // значения предыдущих полей у записи есть - это её же проекции. На
    // построенной записи это видно вычислением.
    let record = object(&[("t", Term::universe(1)), ("x", Term::universe(0))]);
    let ty = Term::Record(Fields::closed(Rc::from([
        field("t", Term::universe(2)),
        field("x", Term::var(0)),
    ])));
    let signature = Signature::default();
    assert!(check_closed(&signature, &record, &ty).is_ok());

    // Тип `r.x` есть `r.t`, то есть `Type 1`; значит `r.x` населяет `Type 1`.
    let projected = Term::Project(Rc::new(record), "x".into());
    assert_eq!(typing(&projected).to_string(), "Type 1");
}

#[test]
fn a_field_name_is_declared_once() {
    // Два поля с одним именем сделали бы проекцию неоднозначной.
    let ty = Term::Record(Fields::closed(Rc::from([
        field("a", Term::universe(0)),
        field("a", Term::universe(0)),
    ])));
    let signature = Signature::default();
    let outcome = infer_closed(&signature, &ty);
    assert!(
        matches!(
            outcome,
            Err(ref error) if matches!(error.kind, ErrorKind::DuplicateField { .. })
        ),
        "получено {outcome:?}"
    );
}

#[test]
fn a_missing_field_is_refused() {
    // Имя, которого в типе нет, - отказ, а не застрявшая проекция.
    let record = object(&[("a", Term::universe(0))]);
    let projected = Term::Project(Rc::new(record), "b".into());
    let signature = Signature::default();
    let outcome = infer_closed(&signature, &projected);
    assert!(
        matches!(
            outcome,
            Err(ref error) if matches!(error.kind, ErrorKind::NoSuchField { .. })
        ),
        "получено {outcome:?}"
    );
}

#[test]
fn an_erased_field_has_no_value_to_take() {
    // Поле кратности `0` стёрто: значения у него в рантайме нет, и вынуть его
    // проекцией нельзя - то же правило, что у стёртой переменной.
    let ty = Term::Record(Fields::closed(Rc::from([Field {
        name: "a".into(),
        mult: Mult::Zero,
        ty: Rc::new(Term::universe(0)),
    }])));
    let signature = Signature::default();
    let mut metas = adamas_core::meta::Metas::default();
    let ctx = adamas_core::ctx::Ctx::new(&signature);
    let value = ctx.eval(&ty);
    let record = ctx.bind("r".into(), Mult::Many, value);
    let projected = Term::Project(Rc::new(Term::var(0)), "a".into());

    // При судейской кратности `0` проекция законна: там всё стёрто.
    assert!(adamas_core::check::infer(&record, &mut metas, Mult::Zero, &projected).is_ok());

    let outcome = adamas_core::check::infer(&record, &mut metas, Mult::One, &projected);
    assert!(
        matches!(
            outcome,
            Err(ref error) if matches!(error.kind, ErrorKind::ErasedField { .. })
        ),
        "получено {outcome:?}"
    );
}

/// `{ fields | tail }`.
fn open(fields: &[Field], tail: Term) -> Fields {
    Fields {
        fields: fields.iter().cloned().collect(),
        tail: Some(Rc::new(tail)),
    }
}

#[test]
fn a_row_is_a_sort_of_its_own() {
    // `Row ℓ` - третий сорт рядом с `Type` и `Level` (§3.2). Живёт он в
    // `Type (ℓ+1)`, поэтому `{0 r : Row ℓ} -> …` есть обычная `Pi`, а
    // row-переменная - обычное связывание.
    assert_eq!(
        typing(&Term::RowKind(Level::number(0))).to_string(),
        "Type 1"
    );
    assert_eq!(
        typing(&Term::RowKind(Level::number(2))).to_string(),
        "Type 3"
    );

    // Набор полей в позиции ряда - значение сорта `Row`, а не тип.
    // Уровень тот же, что у записи с теми же полями: `Type 0` живёт в
    // `Type 1`, значит и ряд из него - в `Row 1`.
    let row = Term::Row(Fields::closed(Rc::from([field("a", Term::universe(0))])));
    assert_eq!(typing(&row).to_string(), "Row 1");
}

#[test]
fn a_tail_makes_the_record_open() {
    // Хвост - часть типа: `{ x : Nat }` и `{ x : Nat | r }` не одно и то же,
    // иначе значение одного встало бы на место другого.
    let signature = Signature::default();
    let mut metas = adamas_core::meta::Metas::default();
    let ctx = adamas_core::ctx::Ctx::new(&signature);
    let kind = ctx.eval(&Term::RowKind(Level::number(0)));
    let inner = ctx.bind("r".into(), Mult::Zero, kind);

    let closed = Term::Record(Fields::closed(Rc::from([field("x", Term::universe(0))])));
    let opened = Term::Record(open(&[field("x", Term::universe(0))], Term::var(0)));

    // Обе формы - типы, и универсум открытой вмещает уровень хвоста.
    assert!(adamas_core::check::is_type(&inner, &mut metas, &closed).is_ok());
    assert!(adamas_core::check::is_type(&inner, &mut metas, &opened).is_ok());

    let (left, right) = (inner.eval(&closed), inner.eval(&opened));
    assert!(
        !adamas_core::conv::convertible(&signature, &mut metas, inner.size(), &left, &right),
        "открытая и закрытая - разные типы"
    );
}

#[test]
fn a_tail_that_is_not_a_row_is_refused() {
    // Хвостом бывает только ряд: `{ x : Nat | Nat }` - отказ.
    let opened = Term::Record(open(&[field("x", Term::universe(0))], Term::universe(0)));
    let signature = Signature::default();
    let outcome = infer_closed(&signature, &opened);
    assert!(
        matches!(
            outcome,
            Err(ref error) if matches!(error.kind, ErrorKind::NotARow { .. })
        ),
        "получено {outcome:?}"
    );
}

#[test]
fn a_tail_absorbs_what_the_other_side_has() {
    // `{ x : Type 0 | ?r } ~ { x : Type 0, y : Type 1 }` решается однозначно:
    // общая метка совпала, а недостающее уходит в хвост. Это и есть то, на чём
    // стоит §4.2: `magnitude` над записью с лишними полями.
    let signature = Signature::default();
    let mut metas = adamas_core::meta::Metas::default();
    let ctx = adamas_core::ctx::Ctx::new(&signature);

    let kind = ctx.eval(&Term::RowKind(Level::number(2)));
    let hole = metas.fresh_term(kind, 0);
    let opened = Term::Record(open(&[field("x", Term::universe(0))], hole));
    let closed = Term::Record(Fields::closed(Rc::from([
        field("x", Term::universe(0)),
        field("y", Term::universe(1)),
    ])));

    let (left, right) = (ctx.eval(&opened), ctx.eval(&closed));
    assert!(
        adamas_core::conv::convertible(&signature, &mut metas, 0, &left, &right),
        "хвост обязан вобрать `y`"
    );
    // Решение наблюдается тем же способом, каким его увидит проверка: после
    // него открытая запись конвертируема с закрытой и только с ней.
    let other = Term::Record(Fields::closed(Rc::from([field("x", Term::universe(0))])));
    let other = ctx.eval(&other);
    assert!(
        !adamas_core::conv::convertible(&signature, &mut metas, 0, &left, &other),
        "решение окончательно"
    );
}

#[test]
fn a_common_label_must_agree() {
    // Хвост берёт только то, чего у другой стороны нет; общая метка обязана
    // сойтись типом.
    let signature = Signature::default();
    let mut metas = adamas_core::meta::Metas::default();
    let ctx = adamas_core::ctx::Ctx::new(&signature);

    let kind = ctx.eval(&Term::RowKind(Level::number(2)));
    let hole = metas.fresh_term(kind, 0);
    let opened = Term::Record(open(&[field("x", Term::universe(0))], hole));
    let clashing = Term::Record(Fields::closed(Rc::from([field("x", Term::universe(1))])));

    let (left, right) = (ctx.eval(&opened), ctx.eval(&clashing));
    assert!(
        !adamas_core::conv::convertible(&signature, &mut metas, 0, &left, &right),
        "`x : Type 0` против `x : Type 1`"
    );
}

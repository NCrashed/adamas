//! Мономорфизация имплиситов: договор с исполнением (§4.11, §6).
//!
//! Проход подставляет известные словари и объявляет производные определения.
//! Проверяется он тем же способом, каким проверена машина, - **вторым мнением
//! о том же значении**: `adamas eval` до прохода и после обязан ответить одно
//! и то же. Разойдись они - и специализация говорит о другой программе, а не о
//! той, которую проверил `adamas check`.
//!
//! Второе обещание проверяется рядом: после прохода словарь не передаётся
//! имплиситом **нигде**, куда терм дотягивается. До прохода передаётся - иначе
//! корпус ничего не показывает.

use std::path::{Path, PathBuf};

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::mono;
use adamas_elab::{Owned, Warnings};

/// `Bool`, `Nat`, `List` и `Unit` - база, без которой не пишется ни один пример.
const BASE: &str = "\
data Bool where
  False : Bool
  True : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

not : Bool -> Bool
not True = False
not False = True

and : Bool -> Bool -> Bool
and True b = b
and False b = False

or : Bool -> Bool -> Bool
or True b = True
or False b = b
";

/// Все четыре формы, в которых словарь доезжает до места вызова.
///
/// Метод (`eq`), умолчание (`neq`), инстанс с контекстом (`Eqv (List a)` зовёт
/// сам себя на хвосте) и суперкласс (`atMost` берёт `eq` из словаря `Ord`,
/// которого автор не писал). Плюс **косвенность**: словарь стоит не в корне, а
/// под именем, которое корень зовёт, - без неё «в терме чисто» было бы правдой
/// ни о чём.
const CLASSES: &str = "\
class Eqv a where
  eq : a -> a -> Bool
  neq : a -> a -> Bool
  neq x y = not (eq x y)

instance Eqv Nat where
  eq Zero Zero = True
  eq (Succ a) (Succ b) = eq a b
  eq a b = False

instance {Eqv a} => Eqv (List a) where
  eq Nil Nil = True
  eq (Cons x xs) (Cons y ys) = and (eq x y) (eq xs ys)
  eq p q = False

class Ord a when Eqv a where
  below : a -> a -> Bool

instance Ord Nat where
  below Zero (Succ b) = True
  below a b = False

atMost : {Ord a} => a -> a -> Bool
atMost x y = or (below x y) (eq x y)

same : {Eqv a} => a -> a -> Bool
same x y = neq x y

answers : List Bool
answers =
  Cons (same Zero Zero)
    (Cons (same (Cons Zero Nil) (Cons Zero (Cons Zero Nil)))
      (Cons (atMost Zero (Succ Zero)) Nil))

main : List Bool
main = answers
";

/// Эффектный метод: словарь несёт row-аргумент, а тело - операцию.
///
/// Первая отметка стоит в `let`, чьё связывание дальше не упоминается, и в
/// этом весь смысл корпуса: подстановка **вычислением** такой `let` снимает
/// вместе с операцией, и ответом остаётся `[1]` вместо `[0, 1]`. Порядок
/// эффектов - часть программы (§3.4), а не деталь её записи.
const EFFECTS: &str = "\
effect Log where
  note : Nat -> Unit

class Emit a where
  emit : a -> {Log} Unit

instance Emit Nat where
  emit n = note n

logged : {Log} Unit
logged =
  let u : Unit = emit Zero
  emit (Succ Zero)

main : List Nat
main = handle logged with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
";

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
///
/// `elaborate_into`, а не `elaborate`: проходу нужны инстансы, а короткая
/// форма их не отдаёт - словарь она про них не спрашивает.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отвергнутый исходник означает сломанный тест, и падать он должен громко"
)]
fn elaborated(source: &str) -> (Signature, Metas, Instances) {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect("исходник обязан проходить проверку");
    (signature, metas, instances)
}

/// Тело определения с подставленными аргументами уровня и row - ровно то, что
/// инстанцирует драйвер перед вычислением.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отсутствие определения означает сломанный тест"
)]
fn body(signature: &Signature, name: &str) -> Term {
    let definition = signature.lookup(name).expect("определение объявлено");
    let body = definition.body.as_ref().expect("у определения есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

/// Значение по мнению машины - то же, что печатает `adamas eval`.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: непогашенная операция означает сломанный тест"
)]
fn ran(signature: &Signature, term: &Term) -> String {
    adamas_interp::run(signature, term)
        .expect("операция обязана встретить хендлер")
        .to_string()
}

/// Значение до прохода и после совпадает.
///
/// Это договор: проход заведён ради представления, а не ради другого ответа на
/// то же самое. Ожидаемое значение написано рядом с равенством - без него оба
/// вычислителя вправе оказаться сломаны одинаково.
#[test]
fn specialising_keeps_the_value() {
    for (source, answer) in [
        (
            format!("{BASE}{CLASSES}"),
            "Cons False (Cons True (Cons True Nil))",
        ),
        (
            format!("{BASE}{EFFECTS}"),
            "Cons Zero (Cons (Succ Zero) Nil)",
        ),
    ] {
        let (mut signature, mut metas, instances) = elaborated(&source);
        let written = body(&signature, "main");
        let before = ran(&signature, &written);
        let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
            .expect("проход обязан пройти");
        let after = ran(&signature, &made.term);
        assert_eq!(before, answer, "корпус посчитан не тем, чем ожидалось");
        assert_eq!(after, before, "специализация посчиталась по-другому");
    }
}

/// После прохода словарь не передаётся имплиситом нигде, куда терм дотягивается.
///
/// До прохода передаётся - и это половина утверждения: пустой список на входе
/// сделал бы пустой список на выходе обещанием ни о чём.
#[test]
fn nothing_passes_a_dictionary_after_specialising() {
    for source in [format!("{BASE}{CLASSES}"), format!("{BASE}{EFFECTS}")] {
        let (mut signature, mut metas, instances) = elaborated(&source);
        let written = body(&signature, "main");
        assert!(
            !mono::residual(&signature, &instances, &written).is_empty(),
            "корпус обязан передавать словарь до прохода"
        );
        let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
            .expect("проход обязан пройти");
        assert_eq!(
            mono::residual(&signature, &instances, &made.term),
            Vec::new(),
            "словарь остался переданным имплиситом"
        );
        // Производных определений корпус требует: без них равенство остатков
        // означало бы, что проход не сделал ничего.
        assert!(!made.created.is_empty(), "проход ничего не произвёл");
    }
}

/// Golden-корпус целиком: ни одна программа не меняет своего значения.
///
/// Написанные здесь исходники показывают, что проход **делает**; корпус
/// показывает, чего он **не портит**, - и это разные утверждения. За три
/// прогона он нашёл три расхождения, каждое на форме, которой в написанном
/// корпусе не было: подстановка вычислением теряла эффект из неиспользуемого
/// `let`, ссылка с недописанной арностью оставляла в теле свободный `e0`, а
/// метод с параметром кратности - `q0`.
///
/// Проверяется значение, а не остаток: границы прохода названы в
/// [`mono`](adamas_elab::mono), и под них попадают четыре фикстуры корпуса.
/// Требовать от них пустого остатка значило бы требовать снятия границ.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус, и падать он должен громко"
)]
#[test]
fn no_golden_program_changes_its_value() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval");
    let mut fixtures: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    fixtures.sort();
    assert!(!fixtures.is_empty(), "корпус {} пуст", dir.display());
    for path in fixtures {
        let source = std::fs::read_to_string(&path).unwrap();
        let (mut signature, mut metas, instances) = elaborated(&source);
        let written = body(&signature, "main");
        let before = ran(&signature, &written);
        let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
            .unwrap_or_else(|error| panic!("{}: проход отказал: {error}", path.display()));
        assert_eq!(
            ran(&signature, &made.term),
            before,
            "{}: специализация посчиталась по-другому",
            path.display()
        );
    }
}

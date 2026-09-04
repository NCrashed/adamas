//! Исполнение: машина считает то же, что ядро, и сверх того - эффекты.
//!
//! Два вычислителя обязаны сходиться на чистом фрагменте, иначе второй не
//! интерпретатор, а второй язык. Поэтому первым делом здесь стоит сверка с
//! `conv::evaluated`, и только потом то, чего ядро не умеет вовсе.

use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;

/// `Nat`, `Bool` и `Unit` - база, без которой не пишется ни один пример.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Unit where
  MkUnit : Unit

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

infixl 6 +
(+) : Nat -> Nat -> Nat
(+) Zero m = m
(+) (Succ k) m = Succ (k + m)
";

/// Элаборирует исходник, проверяя, что он принят.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отвергнутый исходник означает сломанный тест, и падать он должен громко"
)]
fn elaborated(source: &str) -> Signature {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    adamas_elab::elaborate(&module).expect("исходник обязан проходить проверку")
}

/// Тело определения с подставленными аргументами уровня и row.
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

/// Значение по мнению машины.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: непогашенная операция означает сломанный тест"
)]
fn ran(source: &str, name: &str) -> String {
    let signature = elaborated(source);
    let body = body(&signature, name);
    adamas_interp::run(&signature, &body)
        .expect("операция обязана встретить хендлер")
        .to_string()
}

/// Значение по мнению ядра.
fn normalized(source: &str, name: &str) -> String {
    let signature = elaborated(source);
    let body = body(&signature, name);
    adamas_core::conv::evaluated(&signature, &body).to_string()
}

/// На чистом фрагменте вычислители сходятся.
///
/// Это договор между ними: машина заведена ради эффектов, а не ради другого
/// ответа на то же самое. Разойдись они здесь - и `adamas eval` перестал бы
/// говорить о той же программе, которую проверил `adamas check`.
#[test]
fn the_machine_agrees_with_the_core_on_the_pure_fragment() {
    let source = format!(
        "{BASE}
double : Nat -> Nat
double n = n + n

sum : List Nat -> Nat
sum Nil = Zero
sum (Cons x xs) = x + sum xs

nested : List Nat
nested = [double 2, sum [1, 2], 0]

applied : Nat
applied = double (double 3)

matched : Bool
matched = case Succ Zero of
  Zero -> False
  Succ k -> True
"
    );
    for name in ["nested", "applied", "matched", "double", "sum"] {
        assert_eq!(
            ran(&source, name),
            normalized(&source, name),
            "определение `{name}` посчиталось по-разному"
        );
    }
}

/// Хендлер глубокий: операция после возобновления попадает ему же.
#[test]
fn a_handler_survives_its_own_resumption() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

twice : {{Ask}} Nat
twice =
  let a : Nat = ask
  let b : Nat = ask
  a + b

main : Nat
main = handle twice with
  return v -> v
  ask -> resume 1
"
    );
    assert_eq!(ran(&source, "main"), "Succ (Succ Zero)");
}

/// Ветка, не зовущая резумпцию, обрывает вычисление.
#[test]
fn a_branch_without_resume_abandons_the_computation() {
    let source = format!(
        "{BASE}
effect Fail where
  fail : a

broken : {{Fail}} Nat
broken =
  let n : Nat = fail
  Succ (Succ n)

main : Nat
main = handle broken with
  return v -> Succ v
  fail -> Zero
"
    );
    // Ни `Succ` из `broken`, ни `Succ` из `return` не случились: ветка `fail`
    // и есть ответ хендлера.
    assert_eq!(ran(&source, "main"), "Zero");
}

/// `handleMulti` зовёт резумпцию дважды, и оба хода доходят до конца.
#[test]
fn a_multi_shot_resumption_runs_twice() {
    let source = format!(
        "{BASE}
effect Amb where
  toss : Bool

branching : {{Amb}} Nat
branching =
  let b : Bool = toss
  case b of
    True -> 1
    False -> 2

main : Nat
main = handleMulti branching with
  return v -> v
  toss -> resume True + resume False
"
    );
    assert_eq!(ran(&source, "main"), "Succ (Succ (Succ Zero))");
}

/// Чужая метка уходит наружу, а внутренний хендлер встаёт на её продолжении.
#[test]
fn a_foreign_label_passes_through_and_reinstalls_the_handler() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

effect Fail where
  fail : a

mixed : {{Ask, Fail}} Nat
mixed =
  let n : Nat = ask
  let m : Nat = ask
  n + m

inner : {{Ask}} Nat
inner = handle mixed with
  return v -> v
  fail -> Zero

main : Nat
main = handle inner with
  return v -> v
  ask -> resume 1
"
    );
    // Второй `ask` доходит до внешнего хендлера только если внутренний
    // переустановился после первого.
    assert_eq!(ran(&source, "main"), "Succ (Succ Zero)");
}

/// Вложенные хендлеры одной метки: операция достаётся ближайшему.
///
/// Это тот случай, где машина и проверка типов расходились. Правило погашения
/// было `ε' ≡ Λ ++ ε` и отдавало вызываемому **внешнее** вхождение, машина -
/// внутреннее; развёрнутое правило `ε' ≡ ε ++ Λ` отдаёт внутреннее обеим, и
/// смещение вектора evidence обращается в нуль.
#[test]
fn the_nearest_handler_of_a_repeated_label_wins() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

twice : {{Ask, Ask}} Nat
twice =
  let n : Nat = ask
  n

inner : {{Ask}} Nat
inner = handle twice with
  return v -> v
  ask -> resume 1

main : Nat
main = handle inner with
  return v -> v
  ask -> resume 2
"
    );
    assert_eq!(ran(&source, "main"), "Succ Zero");
}

/// Операция считается там, где написанный тип ждёт значение.
#[test]
fn an_operation_runs_in_an_argument_position() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

sums : {{Ask}} Nat
sums = ask + ask + ask

main : Nat
main = handle sums with
  return v -> v
  ask -> resume 2
"
    );
    assert_eq!(
        ran(&source, "main"),
        "Succ (Succ (Succ (Succ (Succ (Succ Zero)))))"
    );
}

/// Ресурс закрывается на выходе из scope, а не на входе в него.
///
/// Порядок стал наблюдаем вместе с исполнением эффектов: до него `drop` не
/// производил ничего, и `let _ = drop h in тело` считало то же, что и обратная
/// форма. Считало - но не в том порядке, и §3.3 обещает exit-point.
#[test]
fn a_resource_closes_after_the_body_not_before_it() {
    let source = format!(
        "{BASE}
effect Log where
  note : Nat -> Unit

resource File where
  Open : File
  closeFile : (1 h : File) -> {{Log}} Bool
  closeFile h =
    note 9
    True

plain : File -> {{Log}} Bool
plain h =
  note 1
  True

opened : {{Log}} Bool
opened = plain Open

-- Первая отметка - тела, вторая - деструктора.
main : List Nat
main = handle opened with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
"
    );
    assert_eq!(
        ran(&source, "main"),
        "Cons{0} Nat (Succ Zero) (Cons{0} Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) (Nil{0} Nat))"
    );
}

/// Ресурс закрывается и тогда, когда вычисление оборвано операцией.
///
/// Ветка `fail` не зовёт `resume`, поэтому продолжение выброшено - а `drop`
/// стоял в нём. Без раскрутки дескриптор уезжал молча: отметок было одна вместо
/// двух, и половина ответа при этом оставалась верной.
#[test]
fn a_resource_closes_when_the_computation_is_abandoned() {
    let source = format!(
        "{BASE}
effect Log where
  note : Nat -> Unit

effect Fail where
  fail : a

resource File where
  Open : File
  closeFile : (1 h : File) -> {{Log}} Bool
  closeFile h =
    note 9
    True

leaky : File -> {{Fail, Log}} Bool
leaky h =
  note 1
  let n : Bool = fail
  True

broken : {{Fail, Log}} Bool
broken = leaky Open

guarded : {{Log}} Bool
guarded = handle broken with
  return v -> v
  fail -> False

main : List Nat
main = handle guarded with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
"
    );
    assert_eq!(
        ran(&source, "main"),
        "Cons{0} Nat (Succ Zero) (Cons{0} Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) (Nil{0} Nat))"
    );
}

/// Значение, которое только возвращают, всё равно досчитывается.
///
/// Регрессия: разворот определения стоит у применения, разбора и проекции, а
/// `Cons answer Nil` не делает ни того, ни другого, ни третьего. Дочитывало
/// такое значение обратное чтение ядра, и хендлер под ним оставался нейтралью -
/// при том что соседний элемент списка, попавший под разбор, считался верно.
#[test]
fn a_value_that_is_only_returned_is_computed_too() {
    let source = format!(
        "{BASE}
effect Ask where
  ask : Nat

asked : {{Ask}} Nat
asked =
  let n : Nat = ask
  n

answer : Nat
answer = handle asked with
  return v -> v
  ask -> resume 1

main : List Nat
main = Cons answer Nil
"
    );
    assert_eq!(ran(&source, "main"), "Cons{0} Nat (Succ Zero) (Nil{0} Nat)");
}

/// Единица без единственного конструктора: `#closing` не объявляется, и
/// машина её не встречает.
///
/// Объявление вставки требовало «`Unit` объявлен», а машина строит значение
/// единицы по её **единственному** конструктору. Расходились они молча:
/// `data Unit` с двумя конструкторами вместе с любым ресурсом давал принятую
/// проверкой программу, которая роняла исполнение на `unreachable!` в
/// раскрутке. Спрашивается теперь одно и то же с обеих сторон.
#[test]
fn a_unit_with_two_constructors_leaves_the_insertion_out() {
    let source = "\
data Unit where
  A : Unit
  B : Unit

data Bool where
  False : Bool
  True : Bool

resource File where
  Open : File
  closeFile : (1 h : File) -> Bool
  closeFile h = True

use : File -> Bool
use h = True

main : Bool
main = use Open
";
    assert_eq!(ran(source, "main"), "True");
}

/// Ресурс, связанный `let`, закрывается при обрыве и тогда, когда между `let`
/// и хвостом блока что-то стоит.
///
/// Вставка оборачивала **хвост** блока, а область видимости связывания
/// начинается на `let`: всё, что между ними, оказывалось снаружи, и машина не
/// знала, что вошла в scope. Разница между «закрылся» и «утёк» была ровно в
/// одной строке между `let` и хвостом.
#[test]
fn a_let_bound_resource_closes_when_the_block_is_abandoned() {
    let source = format!(
        "{BASE}
effect Log where
  note : Nat -> Unit

effect Ask where
  ask : Nat

resource File where
  Open : File
  closeFile : (1 h : File) -> {{Log}} Bool
  closeFile h =
    note 9
    True

leaky : Unit -> {{Ask, Log}} Bool
leaky u =
  let h : File = Open
  note 1
  let n : Nat = ask
  True

broken : {{Ask, Log}} Bool
broken = leaky MkUnit

-- Ветка резумпцию не зовёт: вычисление обрывается на `ask`, и деструктор
-- обязан сработать при раскрутке.
guarded : {{Log}} Bool
guarded = handle broken with
  return v -> v
  ask -> False

main : List Nat
main = handle guarded with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
"
    );
    // Отметка тела, затем отметка деструктора: `[1, 9]`.
    assert_eq!(
        ran(&source, "main"),
        "Cons{0} Nat (Succ Zero) (Cons{0} Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) (Nil{0} Nat))"
    );
}

/// Ветка, сама производящая операцию, не теряет отложенных деструкторов.
///
/// Ветка `fail` производит `boom`, а внешний хендлер `boom` обрывает.
/// Выброшенным тогда оказывается продолжение раскрутки, и запустить отложенное
/// стало некому: ресурс уходил молча, а половина ответа оставалась верной.
#[test]
fn a_branch_that_performs_keeps_its_pending_destructors() {
    let source = format!(
        "{BASE}
effect Log where
  note : Nat -> Unit

effect Fail where
  fail : a

effect Boom where
  boom : a

resource File where
  Open : File
  closeFile : (1 h : File) -> {{Log}} Bool
  closeFile h =
    note 9
    True

leaky : File -> {{Fail, Log}} Bool
leaky h =
  note 1
  let n : Bool = fail
  True

broken : {{Fail, Boom, Log}} Bool
broken = leaky Open

boomed : Unit -> {{Boom, Log}} Bool
boomed u =
  let b : Bool = boom
  b

guarded : {{Boom, Log}} Bool
guarded = handle broken with
  return v -> v
  fail -> boomed MkUnit

outer : {{Log}} Bool
outer = handle guarded with
  return v -> v
  boom -> False

main : List Nat
main = handle outer with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
"
    );
    // Отметка тела и отметка деструктора - обе.
    assert_eq!(
        ran(&source, "main"),
        "Cons{0} Nat (Succ Zero) (Cons{0} Nat (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) (Nil{0} Nat))"
    );
}

/// Обрыв внутри деструктора не съедает остаток раскрутки.
///
/// Два ресурса; первый по порядку деструктор сам производит операцию, которую
/// обрывают. Долг - деструкторы, до которых не дошли, - обязан уехать с
/// исходом, иначе второй ресурс уходит молча.
#[test]
fn an_abort_inside_a_destructor_leaves_the_rest_of_the_unwinding() {
    let effects = "\
resource Socket where
  Listen : Socket
  closeSocket : (1 s : Socket) -> {Log} Bool
  closeSocket s =
    note 8
    True

held : Socket -> File -> {Fail, Boom, Log} Bool
held s h =
  note 1
  let n : Bool = fail
  True

broken : {Fail, Boom, Log} Bool
broken = held Listen Open

guarded : {Boom, Log} Bool
guarded = handle broken with
  return v -> v
  fail -> False

outer : {Log} Bool
outer = handle guarded with
  return v -> v
  boom -> False

main : List Nat
main = handle outer with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
";
    // Деструктор, который обрывают, и тот же без обрыва: ответ обязан совпасть.
    let declared = format!(
        "{BASE}
effect Log where
  note : Nat -> Unit

effect Fail where
  fail : a

effect Boom where
  boom : a
"
    );
    let aborting = format!(
        "{declared}
resource File where
  Open : File
  closeFile : (1 h : File) -> {{Boom, Log}} Bool
  closeFile h =
    note 9
    let z : Bool = boom
    True

{effects}"
    );
    let quiet = format!(
        "{declared}
resource File where
  Open : File
  closeFile : (1 h : File) -> {{Log}} Bool
  closeFile h =
    note 9
    True

{effects}"
    );
    assert_eq!(ran(&aborting, "main"), ran(&quiet, "main"));
}

/// Глубина исполнения не упирается в кадры Rust.
///
/// До явного стека `even (times 100 20)` - обычная структурная рекурсия -
/// роняла процесс `SIGABRT`'ом, а порог двигался от профиля сборки
/// **компилятора**: ~450 уровней в debug, ~1500 в release. Свойством программы
/// он, стало быть, не был вовсе (§10 вопрос 89).
#[test]
fn execution_depth_does_not_ride_the_rust_stack() {
    let source = format!(
        "{BASE}
times : Nat -> Nat -> Nat
times Zero m = Zero
times (Succ k) m = m + times k m

even : Nat -> Bool
even Zero = True
even (Succ Zero) = False
even (Succ (Succ k)) = even k

main : Bool
main = even (times 100 40)
"
    );
    assert_eq!(ran(&source, "main"), "True");
}

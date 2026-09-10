//! Плоское значение в понижении: заголовка нет, счётчика нет (§4.11).
//!
//! Договор ABI (§13, 2026-09-08) говорит про `Flat` три вещи, и каждая здесь
//! показана прогоном, а не чтением кода.
//!
//! - *Заголовка нет вовсе.* Арифметика не выдаёт ни одной ячейки кучи -
//!   [`arithmetic_costs_no_cell`].
//! - *Лежит по значению внутри чужого объекта.* Список с плоским полем стоит
//!   ровно по ячейке на звено, а с указательным - ещё по ячейке на элемент;
//!   разница и есть отсутствующий заголовок ([`a_flat_field_costs_no_cell_of_its_own`]).
//! - *RC по нему не идёт.* `dup` и `drop` по плоскому связыванию не эмитятся
//!   вовсе ([`flat_bindings_carry_no_reference_counting`]) - проверено по самому
//!   представлению, потому что «не эмитится» есть утверждение об отсутствии, а
//!   его в ответе программы не видно.
//!
//! Ответ каждой программы по дороге сверяется с `adamas eval`
//! ([`harness::agreed`]): счётчик показывает цену, а сверка - что цена
//! заплачена за то же самое значение.

mod harness;

use std::collections::BTreeSet;

use adamas_codegen::ir::{Binding, Function, LocalId};

/// Сколько блоков выдал прогон. Ответ по дороге сверяется с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    allocated
}

/// Арифметика целиком: литералы, три операции, вызов с плоским аргументом.
const ARITHMETIC: &str = "\
gap : Int64 -> Int64 -> Int64
gap a b = subInt64 a b

main : Int64
main = gap (mulInt64 5 4) (addInt64 20 3)
";

/// Программа, считающая арифметику, не выдаёт ни одной ячейки кучи.
///
/// Это ABI, а не оптимизация: у плоского значения заголовка нет вовсе, а
/// заголовок и есть то, ради чего выдаётся блок. Ответ `-3` заодно ловит
/// порядок операндов - вычитание не коммутативно.
#[test]
fn arithmetic_costs_no_cell() {
    assert_eq!(
        allocated("арифметика", ARITHMETIC),
        0,
        "под арифметику выдана ячейка: у плоского значения заголовка нет (§4.11)"
    );
}

/// Звеньев в списке. Три - чтобы разница считалась, а не угадывалась.
const LINKS: usize = 3;

/// Один и тот же список с плоским полем и с указательным.
///
/// Форма у обоих одна: три звена, у каждого поле и хвост. Разошлись они только
/// представлением поля - `Int64` против `Nat`, - и по этому же разошлись в
/// цене. Значения полей выбраны так, чтобы указательное стоило **ровно одну**
/// ячейку: `Succ Zero` - одна ячейка, `Zero` непосредствен и блока не занимает.
///
/// Плоское поле здесь **чётное** нарочно: у нечётного младший бит стоит, и
/// рантайм принял бы его за непосредственное значение, а `drop` по нему
/// оказался бы безобидным. Мутант «дропать плоский слот» на единице выживал -
/// измерено.
const LISTS: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Row where
  End : Row
  Item : Int64 -> Row -> Row

data Pile where
  Empty : Pile
  Heap : Nat -> Pile -> Pile

flat : Row
flat = Item 2 (Item 2 (Item 2 End))

boxed : Pile
boxed = Heap (Succ Zero) (Heap (Succ Zero) (Heap (Succ Zero) Empty))
";

/// Плоское поле лежит в слоте по значению и своей ячейки не занимает.
///
/// Свидетель дифференциальный, как `reuse_shows_up_as_allocations_not_saved`:
/// одно число ни о чём не говорит - говорит разница. Плоский список стоит
/// ровно по ячейке на звено, указательный - ещё по ячейке на элемент.
#[test]
fn a_flat_field_costs_no_cell_of_its_own() {
    let flat = allocated(
        "плоские-поля",
        &format!("{LISTS}\nmain : Row\nmain = flat\n"),
    );
    let boxed = allocated(
        "указательные-поля",
        &format!("{LISTS}\nmain : Pile\nmain = boxed\n"),
    );
    assert_eq!(
        flat, LINKS,
        "плоское поле обошлось не в ноль ячеек: звеньев {LINKS}, выдано {flat}"
    );
    assert_eq!(
        boxed - flat,
        LINKS,
        "указательное поле обязано стоить ячейку на элемент: плоский {flat}, \
         указательный {boxed}, звеньев {LINKS}"
    );
}

/// Плоские связывания в трёх позициях, каждая - повод для RC у боксированного.
///
/// `twice` называет параметр **дважды**: боксированному первое употребление
/// стоило бы `dup`. `ignore` не называет второй вовсе: боксированному это
/// стоило бы `drop`. `peel` разбирает объект, у которого плоское поле рядом с
/// указательным: `dup` полей ставится по одному на названное поле, и плоское
/// туда попасть не должно, а указательное - должно, иначе свидетель пуст.
const COUNTED: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Box where
  MkBox : Int64 -> Nat -> Box

twice : Int64 -> Int64
twice x = addInt64 x x

ignore : Int64 -> Int64 -> Int64
ignore a b = a

carry : Int64 -> Nat -> Nat
carry a k = k

peel : Box -> Nat
peel (MkBox n k) = carry (twice (ignore n 7)) (Succ k)

main : Nat
main = peel (MkBox 8 (Succ Zero))
";

/// По плоскому связыванию счётчик не считается: `dup`/`drop` не эмитятся.
///
/// Утверждение про **отсутствие**, поэтому проверяется по представлению, а не
/// по ответу: программа, где `dup` по плоскому всё-таки встал бы, до ответа не
/// дожила бы вовсе - `adamas_dup` от битов числа есть запись по адресу этого
/// числа. Сперва тест требует, чтобы RC-узлы в программе вообще были, иначе он
/// зелен и пуст.
#[test]
fn flat_bindings_carry_no_reference_counting() {
    let program = harness::lowered("счёт", COUNTED);
    let mut counted = 0usize;
    for function in &program.functions {
        let flat = flat_locals(function);
        let mut named = Vec::new();
        harness::rc_nodes(&function.body, &mut named);
        counted += named.len();
        for local in named {
            assert!(
                !flat.contains(&local),
                "`{}`: RC по плоскому связыванию v{} - счётчика у него нет (§4.11)",
                function.name,
                local.0
            );
        }
    }
    assert!(
        counted > 0,
        "RC-узлов в программе нет вовсе: свидетелю нечего было отвергать"
    );
    // Ответ той же программы обязан сойтись с машиной: пустой счёт легко
    // получить, посчитав не то.
    let _ = allocated("счёт-ответ", COUNTED);
}

/// Плоские связывания функции.
fn flat_locals(function: &Function) -> BTreeSet<LocalId> {
    let mut found = BTreeSet::new();
    let mut note = |binding: &Binding| {
        if !binding.fact.repr.boxed() {
            found.insert(binding.local);
        }
    };
    for binding in function.captured.iter().chain(&function.parameters) {
        note(binding);
    }
    harness::bindings(&function.body, &mut note);
    found
}

/// Плавающие всех форм печати: позиционной, экспоненциальной, со знаком.
///
/// Печать плавающего в порождённом C повторяет `{:?}` Rust'а не приблизительно,
/// а посимвольно - иначе договор с `adamas eval` держался бы на том, что в
/// корпусе нет дробей. Здесь стоят обе границы позиционной формы (`1e-4` и
/// `1e16`), обе точности и минус.
const REALS: &str = "\
data Row where
  End : Row
  Item : Float64 -> Row -> Row

data Thin where
  Stop : Thin
  Slim : Float32 -> Thin -> Thin

wide : Row
wide =
  Item (mulFloat64 0.1 3.0)
    (Item (addFloat64 1.0 1.5)
      (Item (mulFloat64 2.5 (-4.0))
        (Item (addFloat64 1.0 0.00000001)
          (Item (mulFloat64 1.0e20 1.0)
            (Item (mulFloat64 1.0e-9 1.0)
              (Item (addFloat64 0.0001 0.0)
                (Item (subFloat64 0.00001 0.0)
                  (Item (mulFloat64 1.0e15 1.0)
                    (Item (mulFloat64 1.0e16 1.0)
                      (Item (subFloat64 0.0 0.0) End))))))))))

narrow : Thin
narrow =
  Slim (addFloat32 1.0 0.00000001)
    (Slim (mulFloat32 3.14159 1.0)
      (Slim (mulFloat32 1.0e38 1.0)
        (Slim (mulFloat32 1.0e-38 1.0)
          (Slim (subFloat32 0.0 0.1) Stop))))
";

/// Дробное печатается так же, как его печатает `adamas eval`.
#[test]
fn a_real_prints_the_way_the_interpreter_prints_it() {
    let _ = allocated(
        "дробные-широкие",
        &format!("{REALS}\nmain : Row\nmain = wide\n"),
    );
    let _ = allocated(
        "дробные-узкие",
        &format!("{REALS}\nmain : Thin\nmain = narrow\n"),
    );
}

/// Плоское значение через границу замыкания не проходит, и отказ это говорит.
///
/// Граница названа в §4.11: обобщённый код над `{Flat a}` получает дескриптор
/// layout имплиситом, а дескрипторов в рантайме ещё нет. Свидетель нужен
/// потому, что молчаливое приведение здесь означало бы биты числа в позиции
/// указателя.
const THROUGH: &str = "\
apply : (Int64 -> Int64) -> Int64 -> Int64
apply f x = f x

main : Int64
main = apply (\\n -> addInt64 n 1) 41
";

/// Плоский аргумент замыкания отвергается названной причиной.
#[test]
fn a_flat_value_does_not_cross_a_closure() {
    let error = harness::compiled(THROUGH).expect_err("плоское через замыкание не проходит");
    let text = error.to_string();
    assert!(
        text.contains("§4.11"),
        "отказ не назвал причину представлением: {text}"
    );
}

/// Ближайший проходящий сосед: та же арифметика без замыкания.
#[test]
fn the_same_arithmetic_without_a_closure_passes() {
    let source = "\
bump : Int64 -> Int64
bump n = addInt64 n 1

main : Int64
main = bump 41
";
    assert_eq!(allocated("сосед", source), 0);
}

/// Прелюдные синонимы `Int` и `Float` (§4.3, лог 2026-09-09).
///
/// `type Int = Int64` - каноническое имя написанной программы и умолчание
/// литерала, поэтому представление обязано смотреть сквозь него: иначе
/// идиоматичный `f : Int -> Int` понижался бы по указательному пути, а
/// арифметика в нём отвергалась. Свидетель различает не написание, а цену:
/// ноль ячеек кучи есть у плоского пути и только у него.
const ALIAS: &str = "\
type Int = Int64
type Wide = Int

gap : Wide -> Int -> Int
gap a b = subInt64 a b

main : Int
main = gap 3 10
";

/// Синоним примитива разворачивается: `Int` понижается как `Int64`.
#[test]
fn a_prelude_synonym_lowers_as_its_primitive() {
    assert_eq!(
        allocated("синоним", ALIAS),
        0,
        "синоним примитива поехал по указательному пути: `Int` есть `Int64` (§4.3)"
    );
}

// Арифметика через класс жила здесь отказом
// (`arithmetic_through_a_class_is_refused_by_name`): специализация отдавала
// метод свёрнутым по эте, понижение брало арность у тела, и аргументы уходили
// через границу замыкания. Вопрос 153 закрыт - арность берётся у типа, - и
// свидетель переехал в `eta.rs` проходящим.

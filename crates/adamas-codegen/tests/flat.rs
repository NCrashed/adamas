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

/// Плоское значение пересекает границу замыкания обёрткой (§5.1, §10
/// вопросы 158 и 159).
///
/// Решение 158: граница боксирует, и цена записана источником боксирования.
/// Обёртка примитива с прозрачной печатью - её реализация: биты не лежат в
/// позиции указателя молча, они лежат в ячейке кучи, и счётчик блоков эту
/// цену называет числом - три блока там, где без замыкания ноль.
const THROUGH: &str = "\
apply : (Int64 -> Int64) -> Int64 -> Int64
apply f x = f x

main : Int64
main = apply (\\n -> addInt64 n 1) 41
";

/// Плоский аргумент замыкания проходит, и цена границы видна счётчиком.
#[test]
fn a_flat_value_crosses_a_closure_at_a_named_price() {
    let stderr = harness::agreed("плоское-через-замыкание", THROUGH).unwrap_or_else(|error| {
        panic!("плоское через замыкание: {error}");
    });
    let (allocated, live) = harness::blocks("плоское-через-замыкание", &stderr);
    assert_eq!(
        allocated, 3,
        "цена границы замыкания разошлась: обёртка аргумента, обёртка ответа и само замыкание"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Плоский **массив** через ту же границу, и обеими позициями (вопрос 189).
///
/// Отличается он от плоского скаляра выше не льготой, а сортом: `Array n a`
/// при `Flat a` есть один объект кучи с заголовком на всю длину (§4.11), и
/// наружу он ходит указателем всегда - плоская у него нагрузка внутри.
/// Поэтому обёртки ему не заводится, и счётчик это называет числом.
///
/// Считается так: массив - ячейка, два замыкания - две, плоский **ответ**
/// каждого боксируется решением 158 - ещё две, и плоский аргумент `10` у
/// второго - шестая. Итого шесть, и **ни одной** на сам массив: боксируйся он
/// наравне со скаляром, их было бы семь.
const ARRAY_THROUGH: &str = "\
type Int = Int64

applying : Array 2 Int64 -> (Array 2 Int64 -> Int64) -> Int64
applying xs f = f xs

calling : Int64 -> (Int64 -> Int64) -> Int64
calling x f = f x

main : Int64
main =
  let xs : Array 2 Int64 = arraySet (arrayNew 2 3) 1 4
  addInt64
    (applying xs (\\ys -> arrayIndex ys 1))
    (calling 10 (\\k -> mulInt64 k (arrayIndex xs 0)))
";

/// Плоский массив проходит замыкание аргументом и захватом, без обёртки.
#[test]
fn a_flat_array_crosses_a_closure_by_both_positions() {
    assert_eq!(
        harness::printed(ARRAY_THROUGH),
        "34",
        "печать машины изменилась - свидетель говорит не о том"
    );
    let stderr = harness::agreed("массив-через-замыкание", ARRAY_THROUGH)
        .unwrap_or_else(|error| panic!("массив через замыкание: {error}"));
    let (allocated, live) = harness::blocks("массив-через-замыкание", &stderr);
    assert_eq!(
        allocated, 6,
        "цена разошлась: массив, два замыкания, две обёртки ответа и одна \
         обёртка плоского аргумента - боксируйся сам массив, их было бы семь"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Вектор (§4.9) не проходит **ни одной** из тех же двух позиций.
///
/// Свидетель написан прогоном и стоит здесь ровно затем, чтобы опровержение
/// вопроса 189 - «та же правка нужна вектору» - держалось тестом, а не
/// памятью. Массив пускать было нечего чинить: он уже указатель. Вектор
/// указателем не бывает - заголовка нет, счётчика нет, а `Simd 4 Float32`
/// занимает шестнадцать байт при слоте в слово (`adamas.h`), и боксированной
/// формы у него нет ни одной: ни укладки в дескрипторе (`Flat` для него не
/// выводится, `adamas-elab/src/flat.rs`), ни конструктора-обёртки
/// (`simd.rs::a_vector_does_not_fit_an_object_slot`).
const VECTOR_LANE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

one : Float32
one = 1.0

two : Float32
two = 2.0

seeded : Simd 4 Float32
seeded = simdSet (simdSplat 4 one) 1 two
";

#[test]
fn a_vector_crosses_a_closure_by_neither_position() {
    let refused = |what: &str, source: &str| -> String {
        harness::text(source)
            .err()
            .unwrap_or_else(|| panic!("{what}: вектор прошёл границу замыкания"))
            .to_string()
    };

    let argument = refused(
        "аргументом",
        &format!(
            "{VECTOR_LANE}
applying : Simd 4 Float32 -> (Simd 4 Float32 -> Float32) -> Float32
applying v f = f v

main : Float32
main = applying seeded (\\w -> simdLane w 1)
"
        ),
    );
    assert!(
        argument.contains("Simd 4 Float32"),
        "отказ в позиции аргумента не называет вектор: {argument}"
    );

    let capture = refused(
        "захватом",
        &format!(
            "{VECTOR_LANE}
calling : Float32 -> (Float32 -> Float32) -> Float32
calling x f = f x

main : Float32
main =
  let v : Simd 4 Float32 = seeded
  calling one (\\k -> addFloat32 k (simdLane v 1))
"
        ),
    );
    assert!(
        capture.contains("захват замыкания") && capture.contains("Simd 4 Float32"),
        "отказ в позиции захвата не называет ни позицию, ни вектор: {capture}"
    );
}

/// Плоский **скаляр** проходит обеими позициями, и цены у них разные (§10
/// вопрос 191).
///
/// Вторая половина решения 158, которой в коде не было: аргумент боксировался
/// ([`a_flat_value_crosses_a_closure_at_a_named_price`]), а захват отвергался -
/// «захват замыкания: ожидалось указательное значение, а пришло плоское
/// `Int64`». Свидетель на месте прежнего отказа, и говорит он то же, что
/// говорил тот: разница между массивом и словом здесь обратная той, какую
/// читает глаз, - массиву обёртки не нужно, слову нужна.
///
/// Цены **две**, и различаются они не величиной, а тем, на что умножаются.
/// Аргумент боксируется на **каждое** пересечение, захват - **один раз**, на
/// сборку среды. Считается это здесь, а различие меряет
/// [`capturing_a_flat_scalar_costs_a_cell_per_closure_not_per_call`].
#[test]
fn a_flat_scalar_crosses_a_closure_by_both_positions() {
    let (by_argument, by_capture) = crossing_thrice("обе-позиции");
    // Три применения: замыкание, три обёртки аргумента, три обёртки ответа.
    assert_eq!(
        by_argument, 7,
        "цена аргумента разошлась: замыкание, три обёртки аргумента и три обёртки ответа"
    );
    // То же плюс **одна** обёртка на захват, и она одна на всю программу.
    assert_eq!(
        by_capture, 8,
        "цена захвата разошлась: те же семь плюс одна обёртка среды"
    );
}

/// Захват плоского скаляра стоит ячейки на замыкание, а не на пересечение.
///
/// Утверждение сверх счёта выше, и стоит оно отдельным свидетелем потому, что
/// это и есть опровергнутая верхняя граница: §10 вопрос 191 называл ценой
/// захвата «ячейку на пересечение», измеренную у аргумента, а пересечений
/// захват не считает вовсе. Мерится это разностью **двух пар**: захват против
/// аргумента при одном применении и он же при трёх. Одна пара такого не
/// скажет - прибавку в единицу даст и «ячейка на пересечение» при единственном
/// пересечении.
#[test]
fn capturing_a_flat_scalar_costs_a_cell_per_closure_not_per_call() {
    let (argument_once, capture_once) = crossing_once("на-замыкание");
    let (argument_thrice, capture_thrice) = crossing_thrice("на-замыкание");
    assert_eq!(
        capture_once - argument_once,
        1,
        "одно пересечение: аргументом {argument_once}, захватом {capture_once}"
    );
    assert_eq!(
        capture_thrice - argument_thrice,
        1,
        "три пересечения: аргументом {argument_thrice}, захватом {capture_thrice}"
    );
}

/// Одно и то же замыкание с плоским множителем: литералом и захватом.
///
/// Ответ у пары один, и это нарочно: разойдись он - счётчики говорили бы о
/// разных программах. Сверяет его [`allocated`] через `adamas eval`.
///
/// Имя прогона своё у каждой пары: `harness` кладёт бинарь по имени, а тесты
/// крейта идут потоками - совпади имена, второй поток получил бы «Text file
/// busy» вместо числа.
fn crossing(what: &str, applications: &str) -> (usize, usize) {
    let source = format!(
        "\
applying : Int64 -> (Int64 -> Int64) -> Int64
applying x f = f x

taking : (Int64 -> Int64) -> Int64
taking f = {applications}
"
    );
    let by_argument = allocated(
        &format!("скаляр-аргументом-{what}"),
        &format!("{source}\nmain : Int64\nmain = taking (\\x -> mulInt64 x 10)\n"),
    );
    let by_capture = allocated(
        &format!("скаляр-захватом-{what}"),
        &format!(
            "{source}\nmain : Int64\nmain =\n  let w : Int64 = 10\n  \
             taking (\\x -> mulInt64 x w)\n"
        ),
    );
    (by_argument, by_capture)
}

/// Одно пересечение границы.
fn crossing_once(what: &str) -> (usize, usize) {
    crossing(what, "applying 1 f")
}

/// Три пересечения той же границы тем же замыканием.
fn crossing_thrice(what: &str) -> (usize, usize) {
    crossing(
        what,
        "addInt64 (applying 1 f) (addInt64 (applying 2 f) (applying 3 f))",
    )
}

/// Операция с **плоским ответом** понижается (§10 вопрос 191, находка трека D
/// волны 3).
///
/// Прежде отвергалась вовсе - «ответ операции: ожидалось указательное
/// значение, а пришло плоское `UInt64`», - и обходить это приходилось массивом
/// из одной ячейки прямо в фикстуре колбэка. Обёртку кладёт `resume` (аргумент
/// резумпции указателен), снимает её место операции; счётчик называет цену
/// числом.
#[test]
fn an_operation_with_a_flat_answer_lowers() {
    const SOURCE: &str = "\
data Unit where
  MkUnit : Unit

effect Width where
  width : UInt64

sized : {Width} UInt64
sized = addUInt64 width 1

main : UInt64
main = handle sized with
  return v -> v
  width -> resume 8
";
    assert_eq!(
        harness::printed(SOURCE),
        "9",
        "печать машины изменилась - свидетель говорит не о том"
    );
    let _ = allocated("операция-с-плоским-ответом", SOURCE);
}

/// Та же операция, взятая **значением** (§10 вопрос 169).
///
/// Путь другой и отказ там стоял свой: недобранная операция едет замыканием над
/// синтетическим телом ([`Lowerer::performer`] в `lower.rs`), и оно отвергало
/// плоский ответ у себя. Отдаёт синтетическое тело обёртку - зовут его через
/// `adamas_apply`, а тот говорит указателями, - и разворачивает её место
/// употребления обычным правилом ответа применения.
///
/// Ответ определения здесь **указательный** нарочно: у функции с плоским
/// ответом операция отвергается раньше и по другой причине - обрыв возвращать
/// нечем (`handlers.rs`, `an_operation_needs_a_pointer_answer_to_abort_through`),
/// - и мерялась бы тогда не та граница.
#[test]
fn an_operation_with_a_flat_answer_is_taken_by_value() {
    const SOURCE: &str = "\
data Unit where
  MkUnit : Unit

data Sum where
  MkSum : UInt64 -> Sum

effect Store where
  fetch : UInt64 -> {Store} UInt64

taking : (UInt64 -> {Store} UInt64) -> {Store} Sum
taking f = MkSum (f 3)

held : {Store} Sum
held = taking fetch

main : Sum
main = handle held with
  return v -> v
  fetch n -> resume (mulUInt64 n 7)
";
    assert_eq!(
        harness::printed(SOURCE),
        "MkSum 21",
        "печать машины изменилась - свидетель говорит не о том"
    );
    let _ = allocated("операция-значением-с-плоским-ответом", SOURCE);
}

/// Плоский **ответ** через границу вызова: имя значением (§10 вопрос 158).
///
/// Третья половина решения 158, и до этого трека её не было: аргумент боксирует
/// [`a_flat_value_crosses_a_closure_at_a_named_price`], ответ лямбды - её
/// объявленное представление, а имя, взятое значением, отвергалось. Замыкание
/// строится над **обёрткой** самого определения: она зовёт его прямым вызовом и
/// кладёт биты в ячейку с прозрачной печатью.
///
/// Мера границы куска (§10 вопрос 164) - слово вместо ячейки - здесь не годится
/// и не применена: слово-биты не указатель, счётчика у него нет, а `run`
/// принимает ответ указательным по объявлению и дропает его.
///
/// Параметр здесь указательный нарочно: плоский параметр недобранного вызова
/// остаётся отказом (`pointing`), и мерялась бы тогда не та половина. Ответ
/// `38` печатается собой - обёртки в нём не видно.
///
/// Значением берутся **два** имени, и вычитание не коммутативно: обёртка
/// заводится на определение, а не на ширину его ответа. Дай им одну на двоих -
/// и ответ станет `0`.
const NAMED_THROUGH: &str = "\
data Unit where
  MkUnit : Unit

run : ((ω u : Unit) -> Int64) -> Int64
run f = f MkUnit

answer : Unit -> Int64
answer u = 40

other : Unit -> Int64
other u = 2

main : Int64
main = subInt64 (run answer) (run other)
";

/// Плоский ответ пересекает границу вызова обёрткой, и цена названа числом.
#[test]
fn a_flat_answer_crosses_a_call_boundary_at_a_named_price() {
    assert_eq!(
        harness::printed(NAMED_THROUGH),
        "38",
        "печать машины изменилась - свидетель говорит не о том"
    );
    let stderr = harness::agreed("плоский-ответ-имени", NAMED_THROUGH).unwrap_or_else(|error| {
        panic!("плоский ответ через границу вызова: {error}");
    });
    let (allocated, live) = harness::blocks("плоский-ответ-имени", &stderr);
    assert_eq!(
        allocated, 4,
        "цена границы вызова разошлась: на каждое имя - замыкание над обёрткой и обёртка ответа"
    );
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Соседняя половина той же границы по-прежнему отказывает по имени.
///
/// Разошлись эти двое ровно позицией плоского: там ответ, здесь параметр.
/// Трамплин-разворачиватель для второй §10 вопрос 158 называет отдельно, и
/// волне он не понадобился.
#[test]
fn a_flat_parameter_of_an_undersaturated_call_is_still_named() {
    let error = harness::compiled(
        "\
apply : (Int64 -> Int64) -> Int64 -> Int64
apply f x = f x

bump : Int64 -> Int64
bump n = addInt64 n 1

main : Int64
main = apply bump 41
",
    )
    .expect_err("плоский параметр недобранного вызова не проходит");
    let text = error.to_string();
    assert!(
        text.contains("параметр недобранного вызова"),
        "отказ назван иначе: {text}"
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

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

/// Плоский **скаляр** проходит обеими позициями, и платит **одна** (§10
/// вопрос 158, пересмотр 2026-09-22).
///
/// История у свидетеля две правки. Сперва захват отвергался вовсе - «захват
/// замыкания: ожидалось указательное значение, а пришло плоское `Int64`», - и
/// трек B волны 4 закрыл отказ обёрткой: восемь ячеек против семи. Потом
/// пересмотр решения 158 снял и обёртку: слот среды разнороден, биты лежат в
/// нём сами, и ячеек снова семь.
///
/// Разница между массивом и словом при этом остаётся обратной той, какую
/// читает глаз, и остаётся по **другой** причине: массиву ничего не нужно было
/// потому, что он указатель; слову нужен разнородный слот, потому что биты в
/// позиции указателя не живут.
///
/// Аргумент боксируется как боксировался, и на **каждое** пересечение: там
/// `adamas_apply` один на все формы. Различие двух позиций меряет
/// [`a_flat_capture_is_free_while_the_argument_pays_per_crossing`].
#[test]
fn a_flat_scalar_crosses_a_closure_by_both_positions() {
    let (by_argument, by_capture) = crossing_thrice("обе-позиции");
    // Три применения: замыкание, три обёртки аргумента, три обёртки ответа.
    assert_eq!(
        by_argument, 7,
        "цена аргумента разошлась: замыкание, три обёртки аргумента и три обёртки ответа"
    );
    // Столько же: захват обёртки не получает вовсе.
    assert_eq!(
        by_capture, 7,
        "цена захвата разошлась: слот среды разнороден, и обёртки там быть не должно"
    );
}

/// Захват плоского скаляра не стоит **ничего**, а аргумент платит на витке.
///
/// Свидетель этот - мера пересмотра 158, и мерит он обе его половины разом.
/// Прежняя его редакция утверждала «ячейка на замыкание, а не на пересечение»:
/// это было опровержением верхней границы, записанной в §10 вопросе 191, и
/// опровержение держалось. Пересмотр 2026-09-22 снял и её.
///
/// Пар по-прежнему **две**, и обе обязательны. Первая говорит, что захват
/// сравнялся с аргументом; вторая - что сравнялся он не потому, что аргумент
/// перестал платить: три пересечения стоят аргументу на четыре ячейки больше,
/// чем одно, и разность захвата с ним всё равно ноль. Останься одна пара, и
/// «граница перестала боксировать **вообще**» читалось бы так же.
#[test]
fn a_flat_capture_is_free_while_the_argument_pays_per_crossing() {
    let (argument_once, capture_once) = crossing_once("на-замыкание");
    let (argument_thrice, capture_thrice) = crossing_thrice("на-замыкание");
    assert_eq!(
        capture_once, argument_once,
        "одно пересечение: аргументом {argument_once}, захватом {capture_once}"
    );
    assert_eq!(
        capture_thrice, argument_thrice,
        "три пересечения: аргументом {argument_thrice}, захватом {capture_thrice}"
    );
    assert_eq!(
        argument_thrice - argument_once,
        4,
        "аргумент перестал платить на пересечение: {argument_once} против {argument_thrice}"
    );
}

/// Одна и та же величина словом: и в слоте кадра, и в слоте замыкания.
///
/// `a` живёт через точку приостановки, `w` уезжает средой замыкания - оба
/// `UInt64`, оба в одной программе, и оба лежат в слоте **битами**.
const BESIDE: &str = "\
data Unit where
  MkUnit : Unit

data Wrap where
  MkWrap : UInt64 -> Wrap

effect State where
  get : UInt64
  put : UInt64 -> Unit

start : UInt64
start = 10

counter : {State} Wrap
counter =
  let a : UInt64 = get
  let u : Unit = put (addUInt64 a 1)
  let b : UInt64 = get
  MkWrap (addUInt64 a b)

threaded : Wrap
threaded = handle counter with
  state start
  return v -> v
  get -> resume state state
  put x -> resume MkUnit x

shifted : UInt64
shifted =
  let w : UInt64 = 7
  let f : UInt64 -> UInt64 = \\n -> addUInt64 n w
  f 1

combine : Wrap -> UInt64 -> Wrap
combine (MkWrap x) y = MkWrap (addUInt64 x y)

main : Wrap
main = combine threaded shifted
";

/// Пары «слотов, счётных» у каждого `adamas_kont_push` порождённой единицы.
fn frame_slots(text: &str) -> Vec<(u32, u32)> {
    text.lines()
        .filter(|line| line.contains("adamas_kont_push(kont, ADAMAS_MARK_PLAIN"))
        .filter_map(|line| {
            let parts: Vec<&str> = line.split(", ").collect();
            let counted = parts.iter().rev().nth(1)?.trim_end_matches('u');
            let fields = parts.iter().rev().nth(2)?.trim_end_matches('u');
            Some((fields.parse().ok()?, counted.parse().ok()?))
        })
        .collect()
}

/// Ветка порождённого дропа по названному тегу, до её `return`.
fn release_branch(text: &str, tag: &str) -> String {
    let from = text
        .find(&format!("if (tag == {tag}) {{"))
        .unwrap_or_else(|| panic!("в порождённом дропе нет ветки {tag}"));
    let rest = &text[from..];
    let to = rest
        .find("return;")
        .unwrap_or_else(|| panic!("ветка {tag} не кончается возвратом"));
    rest[..to].to_owned()
}

/// Разнородных слотов в понижении **три**, и способов различать сорт два
/// (§4.11).
///
/// До пересмотра решения 158 (2026-09-22) слот замыкания был единственным
/// единообразным, и на этом стояла принятая цена: плоское значение туда
/// боксировалось. Пересмотр снял боксирование в позиции **захвата**, и способа
/// изобретать не пришлось - в дереве их уже было два.
///
/// *Слот конструктора* различает сорт **таблицей**: `adamas_slot_kind` по
/// индексу из `adamas_con_slot0`, и порождённый дроп плоский слот пропускает.
///
/// *Слот кадра продолжения* различает **префиксом**: счётные слоты идут
/// первыми, их число уезжает в `adamas_kont_push` (`adamas_frame_counted`), а
/// кадру из одних плоских слотов release не порождается вовсе.
///
/// *Слот замыкания* взял **префикс**, и взял его вынужденно: таблицу выбирает
/// тег, а тег у всех замыканий один (`ADAMAS_TAG_CLOSURE`). Число счётных
/// поэтому лежит в самом блоке, дроп спрашивает его поимённо
/// (`adamas_closure_slot_counted`), и полос у слота две - среда с префиксом и
/// накопленные аргументы, считающиеся всегда: позиция аргумента боксирует.
///
/// **Прежняя редакция этого свидетеля пересмотра не заметила.** Она
/// утверждала, что дроп замыкания не спрашивает `adamas_slot_kind` и считает
/// слоты `adamas_closure_taken`, - и оба утверждения пережили правку дословно,
/// потому что префикс не таблица, а `taken` осталась `taken`. Утверждения
/// подбирались под «слот единообразен», а проверяли форму ветки. Здесь
/// утверждается то самое: **что лежит в слоте**.
#[test]
fn a_closure_slot_is_heterogeneous_by_a_prefix_and_a_constructor_slot_by_a_table() {
    let stderr =
        harness::agreed("рядом", BESIDE).unwrap_or_else(|error| panic!("рядом не прошло: {error}"));
    let (_, live) = harness::blocks("рядом", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");

    let text = harness::text(BESIDE).unwrap_or_else(|error| panic!("не понизилось: {error}"));

    // Кадр: плоский слот есть, и он не считается.
    let slots = frame_slots(&text);
    assert!(
        slots.iter().any(|(fields, counted)| counted < fields),
        "ни один кадр не несёт плоского слота: {slots:?}"
    );
    assert!(
        text.contains("_env[0] = adamas_slot_of(adamas_word_UInt64("),
        "плоское связывание легло в слот кадра не битами"
    );

    // Замыкание: та же величина, та же мера, и обёртки под неё нет.
    assert!(
        text.contains("adamas_closure_set(t1, 0, adamas_slot_of(adamas_word_UInt64(v0)))"),
        "плоский захват лёг в слот замыкания не битами"
    );
    assert!(
        text.contains("adamas_closure(box_"),
        "программа не собирает среды замыкания - сравнивать не с чем"
    );
    // Пятый аргумент - число счётных слотов среды; у единственного плоского
    // захвата он ноль при одном слоте.
    assert!(
        text.contains("1u, 0u); /* лямбда"),
        "счётных слотов у среды с одним плоским захватом оказалось не ноль"
    );
    // Трамплин читает его сужением, а не `dup`'ом: владения у битов нет.
    assert!(
        text.contains("adamas_bits_UInt64(adamas_slot_word(adamas_closure_get(self, 0)))"),
        "трамплин читает плоский слот не битами"
    );

    // Дроп: сорт слота спрашивается у обоих соседей, и разными способами.
    let closure = release_branch(&text, "ADAMAS_TAG_CLOSURE");
    assert!(
        closure.contains("adamas_closure_slot_counted(value, index)"),
        "дроп замыкания перестал спрашивать сорт слота: плоские биты уйдут счётчику"
    );
    assert!(
        closure.contains("adamas_closure_taken(value)"),
        "дроп замыкания считает слоты не рантаймом: форма ветки сменилась"
    );
    assert!(
        text.contains("adamas_slot_kind[adamas_con_slot0[tag] + index] != ADAMAS_FLAT_BOXED"),
        "дроп конструктора перестал спрашивать таблицу сортов"
    );
}

/// Тот же плоский слот кадра, но на пути, где префикс `counted` **читают**.
///
/// Свидетель выше утверждает форму - что слот у кадра разнородный, - и
/// утверждение это текстовое. Здесь то же утверждение проверяется прогоном, и
/// путь взят не любой: число счётных слотов рантайм спрашивает ровно дважды -
/// при копии сегмента (`handleMulti`, многократная резумпция) и при пометке
/// его разделяемым (`spawn`, §5.2). На однократной резумпции оно не читается
/// вовсе, и мутант, объявивший плоский слот счётным, там проходит молча -
/// проверено прогоном.
///
/// `a` здесь **чётное**: биты нечётного значения младшим битом совпадают с
/// непосредственным (`adamas_is_imm`), и `adamas_dup` по ним ничего не делает.
/// На семёрке мутант выжил бы, на десятке роняет процесс сигналом 11.
const REPLAYED: &str = "\
data Unit where
  MkUnit : Unit

data Bool where
  False : Bool
  True : Bool

data Wrap where
  MkWrap : UInt64 -> Wrap

effect Amb where
  toss : Bool

branching : {Amb} Wrap
branching =
  let a : UInt64 = 10
  let b : Bool = toss
  case b of
    True -> MkWrap (addUInt64 a 1)
    False -> MkWrap (addUInt64 a 2)

joined : Wrap -> Wrap -> Wrap
joined (MkWrap x) (MkWrap y) = MkWrap (addUInt64 x y)

main : Wrap
main = handleMulti branching with
  return v -> v
  toss -> joined (resume True) (resume False)
";

/// Плоский слот кадра переживает повторённый сегмент, и переживает прогоном.
#[test]
fn a_flat_frame_slot_survives_a_replayed_segment() {
    let text = harness::text(REPLAYED).unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let slots = frame_slots(&text);
    assert!(
        slots.iter().any(|(fields, counted)| counted < fields),
        "плоский слот кадра из программы пропал - мерить нечего: {slots:?}"
    );
    let stderr = harness::agreed("повторённый", REPLAYED)
        .unwrap_or_else(|error| panic!("повторённый не прошёл: {error}"));
    let (_, live) = harness::blocks("повторённый", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Захват **ветки хендлера** плоское по-прежнему боксирует, и это граница.
///
/// Пересмотр решения 158 (2026-09-22) снял боксирование у слота **замыкания**.
/// Слот кадра хендлера - соседний, и путь к нему в понижении **тот же**
/// (`Lowerer::capturing`), но снятие туда не распространяется: точка входа
/// `adamas_kont_handler` числа счётных слотов не берёт вовсе, и дроп среды
/// (`release_N`) отдаёт каждый занятый слот. Положи туда биты - и `adamas_drop`
/// уменьшит счётчик по адресу числа.
///
/// Свидетель отрицательный, и стоит он ровно за границу: правка, «заодно»
/// объявившая захват ветки разнородным, собирается молча и корпусом не ловится
/// - измерено мутантом, он был зелен целиком до этого свидетеля.
const BRANCH: &str = "\
data Unit where
  MkUnit : Unit

data Wrap where
  MkWrap : UInt64 -> Wrap

effect Ask where
  ask : UInt64

asking : {Ask} Wrap
asking =
  let a : UInt64 = ask
  let b : UInt64 = ask
  MkWrap (addUInt64 a b)

answering : UInt64 -> Wrap
answering w = handle asking with
  return v -> v
  ask -> resume (addUInt64 w 1)

main : Wrap
main = answering 10
";

/// Плоский захват ветки хендлера уезжает в кадр обёрткой, а не битами.
#[test]
fn a_handler_branch_still_boxes_its_flat_capture() {
    let text = harness::text(BRANCH).unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert!(
        text.contains("adamas_slot_write(t0, 0, adamas_word_UInt64(v0));")
            && text.contains("t3_env[0] = t0;"),
        "плоский захват ветки лёг в слот кадра не обёрткой:\n{text}"
    );
    assert!(
        !text.contains("t3_env[0] = adamas_slot_of("),
        "слот кадра хендлера понёс биты: `adamas_kont_handler` числа счётных не берёт"
    );
    // Дроп среды кадра отдаёт **каждый** слот: сорта он не спрашивает, и
    // спросить ему не у кого.
    assert!(
        text.contains("adamas_drop_value(env[0]);"),
        "дроп среды ветки перестал отдавать слот 0"
    );
    let stderr = harness::agreed("ветка-плоское", BRANCH)
        .unwrap_or_else(|error| panic!("ветка с плоским захватом: {error}"));
    let (_, live) = harness::blocks("ветка-плоское", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Счётные слоты среды идут **префиксом**, и порядок написанного его не задаёт.
///
/// Соглашение с рантаймом у разнородного слота одно - `counted` первых слотов
/// среды считаются, - и держать его обязано понижение. Проверить это можно
/// только на среде, где сорта **разные** и написаны они в обратном порядке:
/// `mul` плоский и объявлен раньше указательного `add`. Без перестановки
/// счётным оказался бы слот с битами числа, а число счётных осталось бы
/// единицей - то есть дроп отдал бы `adamas_drop` биты.
///
/// Свидетель этот текстовый, и текстовый он не от лени: перестановка
/// наблюдаема **только** в номерах слотов. Прогоном её ловит корпус
/// (`flat-scalar-through-a-closure`, множитель там чётный), а здесь называется
/// сам порядок - иначе мутант «не сортировать» жил бы молча на любой среде,
/// где сорт один.
const MIXED: &str = "\
data Wrap where
  MkWrap : UInt64 -> Wrap

unwrap : Wrap -> UInt64
unwrap (MkWrap n) = n

applying : UInt64 -> (UInt64 -> UInt64) -> UInt64
applying x f = f x

main : UInt64
main =
  let mul : UInt64 = 10
  let add : Wrap = MkWrap 4
  applying 2 (\\k -> addUInt64 (mulUInt64 mul k) (unwrap add))
";

/// Счётный захват встаёт в слот 0, плоский - за ним, при обратном написании.
#[test]
fn the_counted_capture_goes_first_whatever_the_written_order() {
    let text = harness::text(MIXED).unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert!(
        text.contains("adamas_closure(box_2, adamas_release_value, 1u, 2u, 1u)"),
        "среда перестала быть разнородной: захватов два, счётный обязан быть один"
    );
    let counted = text
        .find("adamas_closure_set(t4, 0, v1);")
        .unwrap_or_else(|| panic!("счётный захват не стоит слотом 0:\n{text}"));
    let flat = text
        .find("adamas_closure_set(t4, 1, adamas_slot_of(adamas_word_UInt64(v0)));")
        .unwrap_or_else(|| panic!("плоский захват не стоит слотом 1:\n{text}"));
    assert!(counted < flat, "слоты напечатаны не по порядку");
    let stderr = harness::agreed("разнородная-среда", MIXED)
        .unwrap_or_else(|error| panic!("разнородная среда: {error}"));
    let (_, live) = harness::blocks("разнородная-среда", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Плоский захват под **частичным применением**: копия замыкания его не дупает.
///
/// Путь этот в корпусе не проходит никто, и это измерено, а не предположено:
/// накопление аргументов в слотах случается только у замыкания арности больше
/// одного, применяемого по аргументу, - а плоский захват до этого трека вообще
/// был обёрткой. `adamas_apply` на нехватке аргументов **копирует** замыкание и
/// дупает занятые слоты; плоский слот дупать нечем, и знает об этом рантайм по
/// префиксу счётных (`adamas_closure_slot_counted`).
///
/// `w` здесь **чётное** нарочно: биты нечётного младшим битом совпадают с
/// признаком непосредственного (`adamas_is_imm`), и `adamas_dup` по ним не
/// делает ничего - на семёрке мутант «дупать все занятые слоты» выжил бы.
/// На десятке он правит заголовок по адресу `10` и роняет процесс.
const PARTIAL: &str = "\
mixing : (UInt64 -> UInt64 -> UInt64) -> UInt64
mixing g = addUInt64 (g 1 2) (g 3 4)

main : UInt64
main =
  let w : UInt64 = 10
  mixing (\\x y -> addUInt64 (mulUInt64 w x) y)
";

/// Копия замыкания переносит плоский слот, а не дупает его.
#[test]
fn a_flat_capture_survives_partial_application() {
    let text = harness::text(PARTIAL).unwrap_or_else(|error| panic!("не понизилось: {error}"));
    // Без двухместного замыкания, применяемого по аргументу, копии не
    // случается вовсе, и свидетель мерил бы не тот путь.
    assert!(
        text.contains("adamas_closure(box_") && text.contains(", 2u, 1u, 0u);"),
        "программа не строит двухместного замыкания с плоским захватом"
    );
    let stderr = harness::agreed("частичное-плоское", PARTIAL)
        .unwrap_or_else(|error| panic!("частичное применение: {error}"));
    let (_, live) = harness::blocks("частичное-плоское", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Сколько воркеров просит свидетель промоушена у круга (§5.2).
///
/// Число нужно **больше единицы**, и это не украшение: `adamas_share` на теле
/// задачи стоит под ветвью `hands != 0` (`fiber.c`), то есть однопоточный круг
/// обхода промоушена не зовёт вовсе. Первая редакция свидетеля ниже переменной
/// не ставила и мутанта «метить все занятые слоты» не убивала - проверено
/// прогоном, а не рассуждением.
const THREADS: &str = "4";

/// Плоский захват, уезжающий в **чужой поток**: промоушен его не метит.
///
/// Второй из двух путей, где число счётных слотов читает рантайм. Первый -
/// копия при частичном применении ([`a_flat_capture_survives_partial_application`]);
/// этот - `spawn` (§5.2): тело задачи есть замыкание, и `adamas_share` метит его
/// детей разделяемыми. Пометить биты числа значило бы записать флаг по адресу
/// этого числа, и `w` здесь **чётное** по той же причине, что и там.
///
/// Задач две, и уступка стоит внутри задачи: без неё файбер не переезжает между
/// воркерами, и половина пути промоушена не задействована.
const SPAWNED: &str = "\
data Unit where
  MkUnit : Unit

data Wrap where
  MkWrap : UInt64 -> Wrap

data Task where
  MkTask : Wrap -> Task

effect Async where
  suspend : Unit
  spawn : ({Async} Wrap) -> Task
  await : (1 t : Task) -> Wrap

withNursery : ({Async} Wrap) -> Wrap

work : UInt64 -> {Async} Wrap
work w =
  let s : Unit = suspend
  MkWrap (mulUInt64 w 3)

joined : Wrap -> Wrap -> Wrap
joined (MkWrap x) (MkWrap y) = MkWrap (addUInt64 x y)

two : {Async} Wrap
two =
  let w : UInt64 = 10
  let t1 : Task = spawn (work w)
  let t2 : Task = spawn (work w)
  let a1 : Wrap = await t1
  let a2 : Wrap = await t2
  joined a1 a2

main : Wrap
main = withNursery two
";

/// Плоский слот среды переживает переезд задачи в чужой поток.
#[test]
fn a_flat_capture_survives_a_spawned_task() {
    let text = harness::text(SPAWNED).unwrap_or_else(|error| panic!("не понизилось: {error}"));
    // Без плоского слота у тела задачи мерить нечего: промоушен обошёл бы
    // одни указатели.
    assert!(
        text.contains("adamas_closure_set(t12, 0, adamas_slot_of(adamas_word_UInt64(v1)))"),
        "тело задачи не несёт плоского захвата"
    );
    assert!(
        text.contains("adamas_closure_slot_counted(value, index)"),
        "порождённый промоушен перестал спрашивать сорт слота"
    );
    let expected = harness::machine_printed(SPAWNED)
        .unwrap_or_else(|why| panic!("машина обязана отвечать, а сказала `{why}`"));
    let ran = harness::c_printed_with("задача-плоское", SPAWNED, &[("ADAMAS_THREADS", THREADS)]);
    assert_eq!(
        ran.printed,
        expected,
        "на {THREADS} воркерах ответ разошёлся с машиной; stderr `{}`",
        ran.reason.trim_end()
    );
    assert_eq!(
        ran.live,
        Some(0),
        "прогон оставил блоки живыми: `{}`",
        ran.reason.trim_end()
    );
}

/// Плоский **агрегат** упирается в обеих позициях в одну и ту же стену.
///
/// Граница замыкания у него теперь одна на две позиции: боксирует его тот же
/// [`Lowerer::moved`], что и скаляр, и потому дальше обе позиции доходят до
/// одного и того же места - формы записи, потерянной вместе с представлением
/// (§4.2). До трека B волны 4 позиции расходились: аргумент боксировался и
/// упирался здесь, а захват отвергался раньше, у себя, и говорил другое.
///
/// Свидетель отрицательный, и стоит он ровно за симметрию: сузь боксирование
/// захвата до скаляра - и тексты двух отказов снова разойдутся.
#[test]
fn a_dense_aggregate_meets_the_same_wall_by_both_positions() {
    const SHAPE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

type Vec3 = { x : Float64, y : Float64, z : Float64 }
";
    let refused = |what: &str, source: &str| -> String {
        harness::text(source)
            .err()
            .unwrap_or_else(|| panic!("{what}: плоский агрегат прошёл границу замыкания"))
            .to_string()
    };

    let argument = refused(
        "аргументом",
        &format!(
            "{SHAPE}
applying : Vec3 -> (Vec3 -> Float64) -> Float64
applying v f = f v

main : Float64
main = applying {{ x = 1.5, y = 2.5, z = 3.5 }} (\\w -> w.y)
"
        ),
    );
    let capture = refused(
        "захватом",
        &format!(
            "{SHAPE}
applying : Float64 -> (Float64 -> Float64) -> Float64
applying x f = f x

main : Float64
main =
  let v : Vec3 = {{ x = 1.5, y = 2.5, z = 3.5 }}
  applying 2.0 (\\k -> mulFloat64 k v.y)
"
        ),
    );
    assert_eq!(
        argument, capture,
        "позиции разошлись текстом отказа: аргумент `{argument}`, захват `{capture}`"
    );
    assert!(
        argument.contains("форма записи потеряна"),
        "стена сменилась, и свидетель говорит не о том: {argument}"
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

/// Операция **круга** (§5.2) плоский ответ по-прежнему не отдаёт.
///
/// Разворот ответа держится на том, что обёртку положил `resume`. За ответом
/// файбера `resume` не стоит: его кладёт завершение задачи, и там лежит само
/// значение. Разверни понижение и его - разбор прочёл бы за тег чужие биты, и
/// это не догадка: с этим мутантом программа ниже собирается и **обрывается**
/// на прогоне («разбор не знает конструктора», сигнал 6).
///
/// Отказ поэтому остаётся, и остаётся названным.
#[test]
fn a_fiber_operation_still_needs_a_pointer_answer() {
    let error = harness::compiled(
        "\
data Unit where
  MkUnit : Unit

data Sum where
  MkSum : Int64 -> Sum

data Task where
  MkTask : Sum -> Task

effect Async where
  suspend : Unit
  spawn : ({Async} Sum) -> Task
  await : (1 t : Task) -> Int64

withNursery : ({Async} Sum) -> Sum

work : {Async} Sum
work = MkSum 7

two : {Async} Sum
two =
  let t1 : Task = spawn work
  let a1 : Int64 = await t1
  MkSum (addInt64 a1 1)

main : Sum
main = withNursery two
",
    )
    .expect_err("плоский ответ операции круга не понижается");
    let text = error.to_string();
    assert!(
        text.contains("ответ операции") && text.contains("плоское `Int64`"),
        "отказ назван иначе: {text}"
    );
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

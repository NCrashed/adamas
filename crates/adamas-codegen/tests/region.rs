//! Представление региона в понижении (§3.6).
//!
//! §3.6 обещает про регион две вещи, и обе здесь показаны прогоном.
//!
//! - *Освобождение одно на всю область.* Область есть **один** блок кучи
//!   Perceus независимо от числа значений в ней
//!   ([`a_region_costs_one_block_whatever_it_holds`]), и после неё живых блоков
//!   ноль. Свидетель дифференциальный: те же значения ячейками кучи стоят по
//!   блоку на каждое.
//! - *Нагрузка счёта не платит.* `dup` и `drop` по значению, лежащему в
//!   области, не эмитятся вовсе ([`a_payload_inside_a_region_carries_no_rc`]) -
//!   счётчика у плоского нет, а плоской нагрузка обязана быть по §3.6.
//!
//! Ответ каждой программы по дороге сверяется с `adamas eval`
//! ([`harness::agreed`]): счётчик показывает цену, а сверка - что цена
//! заплачена за то же самое значение.

mod harness;

use std::collections::BTreeSet;

use adamas_codegen::ir::{Binding, Function, LocalId, Repr};

/// Сколько блоков выдал прогон. Ответ по дороге сверяется с `adamas eval`.
fn allocated(name: &str, source: &str) -> usize {
    named(name, source).1
}

/// Он же вместе с ответом - для свидетелей, которым нужно и то и другое.
fn named(name: &str, source: &str) -> (String, usize) {
    let answer = harness::printed(source);
    let stderr = harness::agreed(name, source).unwrap_or_else(|error| panic!("{name}: {error}"));
    let (allocated, live) = harness::blocks(name, &stderr);
    assert_eq!(live, 0, "{name}: прогон оставил блоки живыми");
    (answer, allocated)
}

/// Общее начало: класс представления, дескриптор и ячейка кучи для сравнения.
///
/// `Cell` завёрнут нарочно тонко - одно плоское поле, - чтобы разница в цене
/// показывала наличие заголовка, а не вес значения.
const SHAPE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

data Cell where
  MkCell : Int64 -> Cell

peel : Cell -> Int64
peel (MkCell n) = n
";

/// Три значения в области.
const THREE: &str = "\
main : Int64
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let c : Int64 = 4
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 a
  let at : Ptr = regionLast r1
  let r2 : Block = regionAlloc r1 b
  let r3 : Block = regionAlloc r2 c
  regionRead r3 at
";

/// Шесть значений в той же области. Форма та же дословно.
const SIX: &str = "\
main : Int64
main =
  let a : Int64 = 1
  let b : Int64 = 2
  let c : Int64 = 4
  let d : Int64 = 8
  let e : Int64 = 16
  let f : Int64 = 32
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 a
  let at : Ptr = regionLast r1
  let r2 : Block = regionAlloc r1 b
  let r3 : Block = regionAlloc r2 c
  let r4 : Block = regionAlloc r3 d
  let r5 : Block = regionAlloc r4 e
  let r6 : Block = regionAlloc r5 f
  regionRead r6 at
";

/// Те же шесть значений ячейками кучи Perceus.
const BOXED: &str = "\
main : Int64
main =
  let a : Cell = MkCell 1
  let b : Cell = MkCell 2
  let c : Cell = MkCell 4
  let d : Cell = MkCell 8
  let e : Cell = MkCell 16
  let f : Cell = MkCell 32
  peel a
";

/// Сколько значений кладёт [`SIX`] и [`BOXED`].
const MANY: usize = 6;

/// Область - один блок, сколько бы значений в ней ни лежало.
///
/// Это и есть «освобождение одно на всю область» (§3.6), измеренное с той
/// стороны, с которой оно наблюдаемо: значение внутри области ячейки кучи не
/// занимает, потому что заголовка у плоского нет вовсе (§4.11).
///
/// Три числа, и ни одно не выводится из остальных. Область на три значения и
/// область на шесть стоят одинаково - цена не растёт с числом. Те же шесть
/// значений ячейками кучи стоят по блоку на каждое - иначе «один блок» говорил
/// бы лишь о том, что значения дёшевы.
#[test]
fn a_region_costs_one_block_whatever_it_holds() {
    let three = allocated("регион-три", &format!("{SHAPE}{THREE}"));
    let six = allocated("регион-шесть", &format!("{SHAPE}{SIX}"));
    let boxed = allocated("ячейки-шесть", &format!("{SHAPE}{BOXED}"));
    assert_eq!(
        three, 1,
        "область на три значения обошлась не в один блок: выдано {three}"
    );
    assert_eq!(
        six, three,
        "цена области выросла с числом значений: три - {three}, шесть - {six}"
    );
    assert_eq!(
        boxed, MANY,
        "ячейка кучи обязана стоить блок: значений {MANY}, выдано {boxed}"
    );
}

/// Нагрузка разной ширины: смещения расходятся, и хендл это показывает.
const MIXED: &str = "\
type Vec3 = { x : Float32, y : Float32, z : Float32 }

data Answer where
  MkAnswer : Int64 -> Float32 -> Float32 -> Answer

main : Answer
main =
  let count : Int64 = 20
  let scale : Float32 = 0.25
  let point : Vec3 = { x = 1.0, y = 2.0, z = 3.0 }
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 count
  let ip : Ptr = regionLast r1
  let r2 : Block = regionAlloc r1 scale
  let sp : Ptr = regionLast r2
  let r3 : Block = regionAlloc r2 point
  let vp : Ptr = regionLast r3
  let got : Vec3 = regionRead r3 vp
  MkAnswer (regionRead r3 ip) (regionRead r3 sp) got.y
";

/// Нагрузка внутри области счётчика не платит.
///
/// Утверждение про **отсутствие**, поэтому проверяется по представлению, а не
/// по ответу: программа, где `dup` по плоской нагрузке всё-таки встал бы, до
/// ответа не дожила бы вовсе. Сперва тест требует, чтобы RC-узлы в программе
/// вообще были - счёт по самой области идёт, и один заголовок на всю область
/// как раз то, что §3.6 обещает, - иначе свидетель зелен и пуст.
#[test]
fn a_payload_inside_a_region_carries_no_rc() {
    let program = harness::lowered("регион-счёт", &format!("{SHAPE}{MIXED}"));
    let mut counted = 0usize;
    let mut payloads = 0usize;
    for function in &program.functions {
        let flat = payload_locals(function);
        payloads += flat.len();
        let mut named = Vec::new();
        harness::rc_nodes(&function.body, &mut named);
        counted += named.len();
        for local in named {
            assert!(
                !flat.contains(&local),
                "`{}`: RC по нагрузке региона v{} - счётчика у неё нет (§3.6, §4.11)",
                function.name,
                local.0
            );
        }
    }
    assert!(
        payloads > 0,
        "плоских связываний в программе нет вовсе: свидетелю нечего было защищать"
    );
    assert!(
        counted > 0,
        "RC-узлов в программе нет вовсе: свидетелю нечего было отвергать"
    );
    let _ = allocated("регион-счёт-ответ", &format!("{SHAPE}{MIXED}"));
}

/// Нагрузка семейством с тегом: одна и та же программа над `Bit` и над `Int8`.
///
/// Разошлись они только типом нагрузки. `Flat Bit` типовая сторона выводит, и
/// понижение с ней согласно: перечисление из двух конструкторов занимает байт
/// (§4.11, §10 вопрос 157 закрыт - тег вошёл в плотную укладку).
const TAGGED: &str = "\
data Bit where
  Off : Bit
  On : Bit

main : Bit
main =
  let one : Bit = On
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 one
  let at : Ptr = regionLast r1
  regionRead r1 at
";

/// Он же над примитивом - ближайший проходящий сосед.
const UNTAGGED: &str = "\
main : Int8
main =
  let one : Int8 = 1
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 one
  let at : Ptr = regionLast r1
  regionRead r1 at
";

/// Нагрузка с тегом кладётся в регион наравне с примитивом.
///
/// Прежде здесь стоял отказ: у семейства с тегом не было плотной укладки в
/// понижении, и перечни типовой стороны и понижения расходились. Вопрос 157
/// закрыт, перечни сошлись, и свидетель перевернулся - программа проходит,
/// отвечает тем же, чем машина, и стоит тот же один блок, что сосед.
#[test]
fn a_tagged_payload_packs_like_a_primitive() {
    assert_eq!(allocated("регион-тег", &format!("{SHAPE}{TAGGED}")), 1);
    // Ближайший сосед: тот же регион над примитивом.
    assert_eq!(
        allocated("регион-примитив", &format!("{SHAPE}{UNTAGGED}")),
        1
    );
}

/// Возврат ячейки соблюдает договор о владении наравне с прочими операциями.
///
/// Область названа здесь трижды - хендлом, возвратом и чтением, - поэтому к
/// возврату она приходит **разделённой**, и лишняя ссылка обязана быть взята
/// именно в этом узле. Дальше срабатывает тот же договор, что у `regionAlloc` и
/// у массива (§5.1, §10 вопрос 149): разделённая копируется целиком вместе с
/// журналом, прежняя остаётся как была, и чтение по старому хендлу это
/// показывает.
///
/// Свидетель написан **примитивами**, а не через стратегию, и это существенно.
/// Через стратегию узел возврата лежит внутри её `free`, где область приходит
/// параметром и называется один раз, - весь счёт достаётся месту вызова, и
/// вставку RC в самом узле можно снять, не сломав ничего. Измерено мутантом.
const SHARED_RETURN: &str = "\
data Seen where
  MkSeen : Ptr -> Int64 -> Seen

main : Seen
main =
  let a : Int64 = 11
  let b : Int64 = 22
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 a
  let h1 : Ptr = regionLast r1
  let r2 : Block = regionRecycle r1 h1
  let r3 : Block = regionAlloc r2 b
  MkSeen (regionLast r3) (regionRead r1 h1)
";

/// То же опусканием курсора: узел другой, договор тот же.
const SHARED_POP: &str = "\
data Seen where
  MkSeen : Ptr -> Int64 -> Seen

main : Seen
main =
  let a : Int64 = 11
  let b : Int64 = 22
  let r0 : Block = regionNew
  let r1 : Block = regionAlloc r0 a
  let h1 : Ptr = regionLast r1
  let r2 : Block = regionPop r1 h1
  let r3 : Block = regionAlloc r2 b
  MkSeen (regionLast r3) (regionRead r1 h1)
";

#[test]
fn a_returned_cell_keeps_the_ownership_contract() {
    let (answer, allocated) = named("возврат-разделённой", &format!("{SHAPE}{SHARED_RETURN}"));
    assert_eq!(
        answer, "MkSeen 0 11",
        "копия обязана унести свободную ячейку, а прежняя область - остаться целой"
    );
    assert_eq!(
        allocated, 3,
        "прежняя область, копия и ответ - три блока, выдано {allocated}"
    );
    let (answer, allocated) = named("вершина-разделённой", &format!("{SHAPE}{SHARED_POP}"));
    assert_eq!(answer, "MkSeen 0 11");
    assert_eq!(allocated, 3);
}

/// Связывания плоской нагрузки: примитив либо плотный агрегат.
///
/// Блок сюда **не** входит, и это существенно: счёт по нему идёт, и попади он
/// в этот список, тест отверг бы ровно то, что §3.6 разрешает.
fn payload_locals(function: &Function) -> BTreeSet<LocalId> {
    let mut found = BTreeSet::new();
    let mut note = |binding: &Binding| {
        if matches!(binding.fact.repr, Repr::Flat(_) | Repr::Packed(_)) {
            found.insert(binding.local);
        }
    };
    for binding in function.captured.iter().chain(&function.parameters) {
        note(binding);
    }
    harness::bindings(&function.body, &mut note);
    found
}

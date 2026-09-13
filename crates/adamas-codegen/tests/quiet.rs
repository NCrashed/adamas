//! Тихая программа: операция - не точка приостановки (§3.4, вопрос 74).
//!
//! Первая ступень инлайнинга хвостово-резумптивных хендлеров. Если все ветки
//! всех площадок достижимой программы хвостовые и мультишота нет, то у
//! операции нет ни одного пути не вернуться: ветка бежит на месте и отвечает
//! значением операции, а обрыв невозможен по построению - `SUPPRESSED` требует
//! разрезанного сегмента, резать который умеют только абортивная ветка, общая
//! ветка и дроп резумпции. Такую программу дробление не трогает: тело с
//! операциями бежит обычным C, кадров продолжения нет, переиспользование
//! ячейки перестаёт упираться в границу куска.
//!
//! Чего ступень **не** снимает - evidence-косвенность: поиск хендлера
//! (`adamas_evidence_lookup`) и непрямой вызов ветки остаются на каждой
//! операции. Их снимала бы специализация по row (вопрос 74, вариант б), и её
//! цена считается от числа, которое даёт стенд `benches/native.rs`.
//!
//! Корпус (`tests/agreement.rs`) отвечает за то, что тихий путь считает то же,
//! что машина, - все хвостово-резумптивные фикстуры идут теперь им. Здесь
//! стоит то, чего ответ не различает: форма порождённого кода и цена в блоках.

mod harness;

/// Общая часть свидетелей: алгоритм стенда `benches/native.rs` на глубине 2.
///
/// Метка, множитель, дерево и три прохода - дословно форма `handled` стенда,
/// чтобы свидетели стерегли ровно ту программу, по которой мерится выигрыш.
const SHAPE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Int64 -> Tree
  Node : Tree -> Tree -> Tree

data Mult where
  Triple : Mult
  Double : Mult

data Unit where
  MkUnit : Unit

scale : Mult -> Int64 -> Tree
scale Triple x = Leaf (mulInt64 x 3)
scale Double x = Leaf (mulInt64 x 2)

grow : Nat -> Int64 -> Tree
grow Zero seed = Leaf seed
grow (Succ k) seed =
  let doubled : Int64 = mulInt64 seed 2
  Node (grow k doubled) (grow k (addInt64 doubled 1))

total : Tree -> Int64
total (Leaf x) = x
total (Node l r) = addInt64 (total l) (total r)

depth : Nat
depth = (Succ (Succ Zero))
";

/// Тихая форма: единственная площадка, ветка хвостовая.
const QUIET: &str = "\
effect Ask where
  ask : Mult

scaled : Tree -> {Ask} Tree
scaled (Leaf x) = scale ask x
scaled (Node l r) = Node (scaled l) (scaled r)

computed : {Ask} Tree
computed = scaled (grow depth 1)

answered : Tree
answered = handle computed with
  return v -> v
  ask -> resume Triple

main : Int64
main = total answered
";

/// Нетихий сосед: та же программа плюс абортивная ветка `quit`.
///
/// Не зовёт её никто - тишину гасит само её существование, условие
/// глобальное. Разность двух форм и есть то, что ступень снимает.
const NOISY: &str = "\
effect Ask where
  ask : Mult
  quit : Mult

scaled : Tree -> {Ask} Tree
scaled (Leaf x) = scale ask x
scaled (Node l r) = Node (scaled l) (scaled r)

computed : {Ask} Tree
computed = scaled (grow depth 1)

answered : Tree
answered = handle computed with
  return v -> v
  ask -> resume Triple
  quit -> Leaf 0

main : Int64
main = total answered
";

/// Операция бежит на месте: ни одного кадра, ветка зовётся значением.
///
/// Цена названа блоками, и каждый именован: дерево `grow` - семь (четыре
/// листа, три узла), счётчик глубины - два `Succ`, новые листья `scale` -
/// четыре (reuse через границу вызова не проходит, и `boxed`-сосед стенда
/// платит те же), кадр хендлера и два вектора evidence - пустой корень и
/// расширенный им. Узлы `scaled` не стоят ничего: переиспользование ячейки
/// вернулось вместе с недроблёным телом. До ступени было 29: три кадра на
/// узел и лист плюс потерянный reuse узла.
#[test]
fn a_quiet_operation_runs_in_place_without_frames() {
    let source = format!("{SHAPE}{QUIET}");
    let text = harness::text(&source).unwrap_or_else(|error| panic!("тихая форма: {error}"));
    assert!(
        !text.contains("adamas_kont_push"),
        "тихая программа ставит кадры:\n{text}"
    );
    assert!(
        text.contains("= adamas_frame_perform("),
        "операция не бежит на месте значением:\n{text}"
    );
    assert!(
        text.contains("adamas_reuse"),
        "переиспользование ячейки не вернулось в недроблёное тело:\n{text}"
    );

    let stderr = harness::agreed("quiet-in-place", &source)
        .unwrap_or_else(|error| panic!("тихая форма: {error}"));
    let (allocated, live) = harness::blocks("quiet-in-place", &stderr);
    assert_eq!(live, 0, "тихая форма оставила блоки живыми");
    assert_eq!(allocated, 16, "цена тихой формы в блоках изменилась");
}

/// Один не-хвостовой хендлер гасит тишину везде: кадры возвращаются.
///
/// Ловит мутанта «тишина не смотрит на вердикт»: посчитай `NOISY` тихой - и
/// абортивная ветка вернула бы ответ хендлера прямо в середину чистого
/// отрезка, который продолжил бы считать с чужим значением. Здесь это видно
/// формой кода; в корпусе то же ловят абортивные фикстуры расхождением с
/// машиной.
#[test]
fn one_abortive_branch_silences_the_quiet_path_everywhere() {
    let source = format!("{SHAPE}{NOISY}");
    let text = harness::text(&source).unwrap_or_else(|error| panic!("нетихий сосед: {error}"));
    assert!(
        text.contains("adamas_kont_push"),
        "абортивная ветка не вернула дробление:\n{text}"
    );
    let stderr = harness::agreed("quiet-noisy", &source)
        .unwrap_or_else(|error| panic!("нетихий сосед: {error}"));
    let (_, live) = harness::blocks("quiet-noisy", &stderr);
    assert_eq!(live, 0, "нетихий сосед оставил блоки живыми");
}

/// Плоский ответ с операцией в тихой программе компилируется.
///
/// Граница «операция в функции с плоским ответом - обрыв вернуть нечем»
/// принадлежит нетихой программе: там `SUPPRESSED` возвращает значение
/// `adamas_kont_abort`, и `int64_t` его не вынесет. В тихой программе обрыва
/// нет, операция отвечает на месте, и функция с плоским ответом законна.
/// Нетихий отказ стережёт `tests/handlers.rs`
/// (`an_operation_needs_a_pointer_answer_to_abort_through`).
#[test]
fn a_flat_answer_may_perform_in_a_quiet_program() {
    let source = format!(
        "{SHAPE}\
effect Ask where
  ask : Mult

factor : Mult -> Int64
factor Triple = 3
factor Double = 2

weigh : Int64 -> {{Ask}} Int64
weigh x = mulInt64 x (factor ask)

scaled : Tree -> {{Ask}} Tree
scaled (Leaf x) = Leaf (weigh x)
scaled (Node l r) = Node (scaled l) (scaled r)

computed : {{Ask}} Tree
computed = scaled (grow depth 1)

answered : Tree
answered = handle computed with
  return v -> v
  ask -> resume Triple

main : Int64
main = total answered
"
    );
    let stderr = harness::agreed("quiet-flat-answer", &source)
        .unwrap_or_else(|error| panic!("плоский ответ в тихой программе: {error}"));
    let (_, live) = harness::blocks("quiet-flat-answer", &stderr);
    assert_eq!(live, 0, "плоский ответ оставил блоки живыми");
}

//! Питомник на обоих бэкендах, и два его инварианта - **обрывом** (§5.2).
//!
//! Корпус (`tests/llvm.rs`, `tests/agreement.rs`) отвечает за то, что
//! одиннадцать питомничных фикстур считают то же, что машина. Здесь стоит то,
//! чего корпус не различает **по построению**: программы, у которых ответа нет
//! вовсе.
//!
//! # Почему обрыв, а не ответ
//!
//! Два инварианта рантайма питомника были при закрытии волны 5 Фазы 6 названы
//! **выжившими мутантами**: сними строку - корпус зелёный целиком, включая ноль
//! живых блоков. Различающая программа у каждого существовала и тогда, и обе
//! кончаются обрывом, а наблюдать обрыв ни один прогон тогда не умел: и
//! `harness::agreed`, и `harness::llvm_agreed` роняют тест на ненулевом коде
//! возврата. Обрыв у них - поломка окружения, а не наблюдение.
//!
//! Этот трек добавил наблюдение (`harness::c_printed`, `harness::machine_printed`
//! рядом с уже стоявшим `harness::llvm_printed`), и оба мутанта убиваются.
//! Утверждение здесь поэтому не «программа работает», а «программа обрывается,
//! и вот чем»: сними проверяемую строку - обрыв исчезает, и тест краснеет.
//!
//! # Что именно различает каждая программа
//!
//! *Ответ отменённой снимается с готовых* (`fiber.c`, `adamas_nursery_cancel`).
//! Отменить договорившую задачу можно: файбера уже нет, но ответ её лежит в
//! готовых, и `await` по копии его бы нашёл. Копию написать даёт **обычный**
//! `data Task` - у ресурса кратность значения `1`, и второго упоминания не
//! написать вовсе, то есть свидетеля этой строки на ресурсе не бывает. Оставь
//! ответ на месте - и `await` после отмены ответит пятёркой, вместо того чтобы
//! уйти в круг ждать никого.
//!
//! *Кадр питомника подавляется в векторе деструктора* (`frame.c`,
//! `closing_evidence`). Деструктор брошенной задачи бежит на стеке того, кто
//! раскручивает, а её собственного кадра `NURSERY` там уже нет. Уступи такой
//! деструктор - и поиск круга обязан пройти **мимо** подавленной записи к тому
//! кругу, который жив. Сними подавление - и след `1 7 4 9` становится
//! `1 7 9 4`.
//!
//! Предсказание `frame.c` тут стоит поправить, и поправка измерена: там
//! сказано «молча портила бы цепочку», то есть обрыв. Обрыва нет - есть
//! **переставленный порядок**: уступка уходит в брошенный круг, тот пуст, и
//! деструктор возвращается на место немедленно, не дав соседу живого круга
//! пробежать. Дефект от этого не меньше, но ловится он ответом, а не падением.
//!
//! # Оба бэкенда, одни программы
//!
//! Программы читают обе половины файла, как в `tests/multi.rs`: вторая копия
//! текста разъехалась бы с первой молча. Машина спрашивается наравне с
//! бэкендами - «обрывается» без «и машина тоже» проверяло бы реализацию, а не
//! спецификацию.

mod harness;

use adamas_codegen::ir::{Expr, Unique};
use adamas_codegen::llvm::Pipeline;

/// Общая шапка: единица, числа, списки, отметка.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

effect Log where
  note : Nat -> Unit
";

/// Отмена договорившей задачи: её ответ снимается с готовых.
///
/// `Task` объявлен обычным `data` намеренно - см. шапку модуля. `drain`
/// разбирает значение задачи, и разбор её и есть отмена (§5.2): имени
/// деструктора сигнатура рантайма не знает.
///
/// Без снятия ответа `await t` нашёл бы пятёрку в готовых и программа ответила
/// бы `Cons 9 (Cons 13 Nil)`. Со снятием ждать ему некого: круг пуст, список
/// ждущих нет - взаимная блокировка.
const CANCELLED_ANSWER: &str = "\
data Task where
  MkTask : Nat -> Task

effect Async where
  suspend : Unit
  spawn : ({Async, Log} Nat) -> Task
  await : (t : Task) -> Nat

withNursery : ({Async, Log} Nat) -> {Log} Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

quick : {Async, Log} Nat
quick =
  let a : Unit = note 9
  5

-- Разбор значения задачи: он и есть отмена.
drain : Task -> {Log} Nat
drain (MkTask n) = 8

-- Уступка даёт задаче договорить; отмена снимает её ответ; `await` по копии
-- уходит в круг ждать никого.
racing : {Async, Log} Nat
racing =
  let t : Task = spawn quick
  let s : Unit = suspend
  let d : Nat = drain t
  let got : Nat = await t
  plus d got

waited : {Log} Nat
waited = withNursery racing

main : List Nat
main = handle waited with
  return v -> Cons v Nil
  note n -> Cons n (resume MkUnit)
";

/// Тот же текст, но без отмены: он обязан **ответить**.
///
/// Стоит рядом не для полноты. Без него «обрывается» покрывало бы и программу,
/// которая обрывалась бы по любой другой причине - хоть по неверной раскладке
/// кадра, - и свидетель проверял бы, что питомник сломан, а не что строка
/// работает.
const KEPT_ANSWER: &str = "\
data Task where
  MkTask : Nat -> Task

effect Async where
  suspend : Unit
  spawn : ({Async, Log} Nat) -> Task
  await : (t : Task) -> Nat

withNursery : ({Async, Log} Nat) -> {Log} Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

quick : {Async, Log} Nat
quick =
  let a : Unit = note 9
  5

racing : {Async, Log} Nat
racing =
  let t : Task = spawn quick
  let s : Unit = suspend
  let got : Nat = await t
  plus 8 got

waited : {Log} Nat
waited = withNursery racing

main : List Nat
main = handle waited with
  return v -> Cons v Nil
  note n -> Cons n (resume MkUnit)
";

/// Уступка **из деструктора** брошенной задачи - к кругу, который жив.
///
/// Кругов здесь два, и это не украшение, а само утверждение. Внутренний
/// обрывается хендлером снаружи себя; его задача стоит запаркованной, держа
/// ресурс; раскрутка её сегмента зовёт деструктор, и деструктор **уступает**.
/// Запись `NURSERY` брошенного кадра в векторе деструктора подавлена, поэтому
/// поиск круга проходит мимо неё - и находит внешний, который жив.
///
/// *Отмена **одной** задачи сюда не годится, и это измерено, а не решено.*
/// `adamas_nursery_cancel` отдаёт сегмент через `adamas_segment_disown_base`, а
/// тот снимает у кадра саму **метку** `NURSERY`; условие подавления её больше не
/// видит, и ветка про питомник на этом пути недостижима. Написанная так
/// программа считает одно и то же с мутантом и без него - проверено.
///
/// Различающая сила - **четвёрка между семёркой и девяткой**: сосед внешнего
/// круга успевает пробежать, пока деструктор внутренней задачи стоит
/// запаркованным. Сними подавление - и `adamas_kont_cut` разрежет по кадру
/// брошенного круга, которого на этом стеке нет.
///
/// `{Async, Log}` у деструктора - не украшение: без `Async` уступки в нём не
/// написать, и программы этой не существует. Метка объявлена **раньше**
/// деструктора: ordered scoping (§4.8).
const YIELD_FROM_A_DESTRUCTOR: &str = "\
data Bool where
  False : Bool
  True : Bool

effect Fail where
  fail : Bool

effect Async where
  suspend : Unit
  spawnDetached : ({Async, Log} Unit) -> Unit

resource File where
  Open : File
  closeFile : (1 h : File) -> {Async, Log} Bool
  closeFile h =
    let a : Unit = note 7
    let s : Unit = suspend
    True

withNursery : ({Async, Fail, Log} Unit) -> {Fail, Log} Unit

-- Задача внутреннего круга: берёт ресурс, отмечается и уступает. Двойки не
-- будет - круг оборвут, пока она стоит в очереди.
child : File -> {Async, Log} Unit
child h =
  let a : Unit = note 1
  let s : Unit = suspend
  note 2

held : {Async, Log} Unit
held = child Open

inner : {Async, Fail, Log} Unit
inner =
  let u : Unit = spawnDetached held
  let s : Unit = suspend
  let n : Bool = fail
  MkUnit

nursed : {Fail, Log} Unit
nursed = withNursery inner

-- Хендлер обрыва стоит снаружи внутреннего круга и **внутри** внешнего.
aborted : {Log} Unit
aborted = handle nursed with
  return v -> v
  fail -> MkUnit

-- Сосед внешнего круга: его отметка и есть доказательство, что уступка
-- деструктора доехала до живого круга, а не до брошенного.
sibling : {Async, Log} Unit
sibling = note 4

outer : {Async, Fail, Log} Unit
outer =
  let u : Unit = spawnDetached sibling
  let a : Unit = aborted
  note 9

nested : {Fail, Log} Unit
nested = withNursery outer

quiet : {Log} Unit
quiet = handle nested with
  return v -> v
  fail -> MkUnit

main : List Nat
main = handle quiet with
  return v -> Nil
  note n -> Cons n (resume MkUnit)
";

/// Слово, которым рантайм называет взаимную блокировку.
const DEADLOCK: &str = "взаимная блокировка файберов";

/// Отмена договорившей снимает её ответ: `await` по копии упирается в круг.
///
/// Наблюдается это **тремя** вычислителями сразу, и парная программа без
/// отмены отвечает - без неё утверждение читалось бы как «питомник не работает».
#[test]
fn the_answer_of_a_cancelled_task_is_taken_off_the_ready_list() {
    let cancelled = format!("{SHAPE}{CANCELLED_ANSWER}");
    let kept = format!("{SHAPE}{KEPT_ANSWER}");

    // Парная программа: тот же круг, та же уступка, отмены нет - есть ответ.
    let answer = harness::machine_printed(&kept).expect("программа без отмены обязана отвечать");
    assert_eq!(
        answer,
        "Cons (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))) \
         (Cons (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ \
         (Succ Zero))))))))))))) Nil)",
        "парная программа посчитала не то"
    );
    let ran = harness::c_printed("nursery.kept", &kept);
    assert_eq!(
        ran.printed, answer,
        "C-бэкенд на парной программе разошёлся"
    );

    // Сама различающая: ответа нет ни у машины, ни у бэкенда.
    let why = harness::machine_printed(&cancelled)
        .expect_err("отмена договорившей обязана уводить `await` в пустой круг");
    assert!(
        why.contains("взаимная блокировка"),
        "машина оборвалась не тем: `{why}`"
    );
    let broken = harness::c_printed("nursery.cancelled", &cancelled);
    assert_eq!(
        broken.printed, "прогон оборвался",
        "C-бэкенд ответил там, где ответа нет: `{}`",
        broken.printed
    );
    assert!(
        broken.reason.contains(DEADLOCK),
        "C-бэкенд оборвался не тем: `{}`",
        broken.reason.trim_end()
    );
    eprintln!(
        "отмена договорившей: машина `{why}`, C `{}`; парная отвечает {answer}",
        broken.reason.trim_end()
    );
}

/// Он же на LLVM-пути: тот же текст, тот же обрыв, то же слово.
#[test]
fn the_llvm_path_deadlocks_on_the_same_program() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let cancelled = format!("{SHAPE}{CANCELLED_ANSWER}");
    let artefacts = harness::llvm_text("питомник-отмена", &cancelled)
        .expect("питомник обязан браться LLVM-эмиттером");
    let broken = harness::llvm_printed(
        "nursery.cancelled.llvm",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        broken.printed, "прогон оборвался",
        "LLVM ответил там, где ответа нет: `{}`",
        broken.printed
    );
    assert!(
        broken.reason.contains(DEADLOCK),
        "LLVM оборвался не тем: `{}`",
        broken.reason.trim_end()
    );

    // И парная - отвечает, тем же значением, что у машины.
    let kept = format!("{SHAPE}{KEPT_ANSWER}");
    harness::llvm_agreed(
        "питомник-без-отмены",
        &kept,
        &tools,
        &pipeline,
        "nursery.kept.llvm",
    )
    .expect("парная программа обязана браться LLVM-эмиттером");
}

/// Уступка из деструктора брошенной задачи доходит до живого круга.
///
/// Ответ здесь **есть**, и в этом всё дело: подавленная запись `NURSERY`
/// пропускается поиском, и уступка режет по кадру круга, который жив. Мутант
/// (снятый `ADAMAS_MARK_NURSERY` из условия подавления) режет по брошенному
/// кадру, и трамплин упирается в пол, которого на стеке нет.
#[test]
fn a_destructor_of_an_abandoned_task_may_yield() {
    let source = format!("{SHAPE}{YIELD_FROM_A_DESTRUCTOR}");
    let answer =
        harness::machine_printed(&source).expect("уступка из деструктора обязана доезжать");
    // Четвёрка **между** семёркой и девяткой: сосед внешнего круга пробежал,
    // пока деструктор внутренней задачи стоял запаркованным. Сравнивать
    // довольно с машиной, но порядок здесь и есть утверждение, поэтому он
    // назван числом, а не выведен из совпадения двух реализаций.
    assert_eq!(
        answer,
        "Cons (Succ Zero) (Cons (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))) \
         (Cons (Succ (Succ (Succ (Succ Zero)))) (Cons (Succ (Succ (Succ (Succ (Succ (Succ (Succ \
         (Succ (Succ Zero))))))))) Nil)))",
        "машина отметила не 1-7-4-9: уступка деструктора ушла не в тот круг"
    );
    let ran = harness::c_printed("nursery.yielding", &source);
    assert_eq!(
        ran.printed, answer,
        "C-бэкенд посчитал не то, что машина, на уступке из деструктора"
    );
    assert_eq!(ran.live, Some(0), "прогон оставил блоки живыми");
    eprintln!("уступка из деструктора: {answer}");
}

/// Питомничные фикстуры корпуса: те, в которых круг есть.
const NURSED: [&str; 11] = [
    "await-twice",
    "await-value",
    "cancel",
    "cancel-bystander",
    "nursery",
    "nursery-abort",
    "nursery-abort-order",
    "spawn-local",
    "task",
    "task-handoff",
    "task-typed",
];

/// Вывод уникальности трека B не судит тела задач, и это **измерено**.
///
/// Вопрос стоит так: атомарный счётчик (§5.1) обязан не сломать
/// [`Unique::Certain`], на котором стоит `crate::unique`. Сам счётчик его не
/// трогает - `rc == 0` остаётся `rc == 0`, и это проверено рантаймом
/// (`adamas-runtime/tests/atomic.rs`). Остаётся вторая половина: не судит ли
/// проход **параметр, который под настоящими потоками окажется разделённым**.
///
/// Разделённым его сделал бы `spawn`, а тело задачи есть замыкание - такие
/// функции проход кладёт в `escaping` и их параметры не судит вовсе. Считается
/// это по **всему** корпусу LLVM-пути, а не по одним питомничным, и вот почему:
/// на одиннадцати питомничных `Certain` не выдаётся **ни одного**, то есть
/// утверждение о них было бы пустым. Первая редакция этого свидетеля считала
/// только их и падала на собственной проверке непустоты - ровно то, ради чего
/// та проверка и стоит.
///
/// Мутант у утверждения есть и он в самом проходе: сними
/// `Expr::Closure => escaping.insert` - и счёт у целей замыканий перестанет
/// быть нулевым.
#[test]
fn the_uniqueness_pass_judges_no_body_of_a_task() {
    let mut judged = 0_usize;
    let mut boxed = 0_usize;
    let mut nursed = 0_usize;
    let mut fixtures: Vec<std::path::PathBuf> = std::fs::read_dir(harness::corpus())
        .expect("корпус обязан читаться")
        .map(|entry| entry.expect("запись корпуса обязана читаться").path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    fixtures.sort();

    for path in &fixtures {
        let name = path
            .file_stem()
            .expect("у фикстуры есть имя")
            .to_string_lossy()
            .into_owned();
        let text = std::fs::read_to_string(path).expect("фикстура обязана читаться");
        // Отвергнутые срезом пропускаются: судить их некому, и это не предмет.
        let Ok(program) = harness::llvm_program(&name, &text) else {
            continue;
        };
        let program = adamas_codegen::unique::infer(program);
        let mut targets = std::collections::BTreeSet::new();
        for function in &program.functions {
            harness::walk(&function.body, &mut |expr| {
                if let Expr::Closure { function: code, .. } = expr {
                    targets.insert(*code);
                }
            });
        }
        boxed += targets.len();
        for function in &program.functions {
            let certain = function
                .parameters
                .iter()
                .filter(|binding| binding.fact.unique == Unique::Certain)
                .count();
            assert!(
                certain == 0 || !targets.contains(&function.id),
                "{name}: `{}` стоит значением и всё же судима выводом уникальности",
                function.name
            );
            judged += certain;
            if NURSED.contains(&name.as_str()) {
                nursed += certain;
            }
        }
    }
    // Ноль у всех - ответ пустой: проход обязан судить **хоть что-то**, иначе
    // утверждение выше держалось бы на том, что он не работает вовсе.
    assert!(
        judged > 0,
        "вывод уникальности не дал ни одного `Certain` на корпусе"
    );
    assert_eq!(
        nursed, 0,
        "на питомничных фикстурах появился `Certain`: утверждение выше стало нетривиальным, \
         и его надо перечитать"
    );
    eprintln!(
        "вывод уникальности: {judged} `Certain` на корпусе, {boxed} функций значением и \
         ни одного `Certain` у них, {nursed} на одиннадцати питомничных"
    );
}

/// Он же на LLVM-пути.
#[test]
fn the_llvm_path_yields_from_a_destructor_too() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let source = format!("{SHAPE}{YIELD_FROM_A_DESTRUCTOR}");
    let (_, stderr) = harness::llvm_agreed(
        "уступка-из-деструктора",
        &source,
        &tools,
        &pipeline,
        "nursery.yielding.llvm",
    )
    .expect("уступка из деструктора обязана браться LLVM-эмиттером");
    let (_, live) = harness::blocks("уступка-из-деструктора", &stderr);
    assert_eq!(live, 0, "прогон LLVM оставил блоки живыми");
}

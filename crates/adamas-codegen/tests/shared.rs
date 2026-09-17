//! Разделяемая область под настоящими потоками (§3.6, §5.2).
//!
//! # Что здесь наблюдается сверх `threads.rs`
//!
//! Тот свидетель показывает, что круг питомника идёт на воркерах. Этот - что
//! воркеры **аллоцируют в одну область**, и различие это не риторическое:
//! обычная область копируется при лишней ссылке (`region.c`, `copied`), и
//! четыре задачи над ней получили бы четыре копии, каждая со своим нулевым
//! смещением. Ответ у копий при этом остался бы **правдоподобным**, пока
//! задача читает своё.
//!
//! Различает их поэтому программа, в которой **корень читает уложенное
//! задачей** ([`GATHER`]). Замени в ней `sharedNew` на `regionNew` - и прогон
//! обрывается: корневая копия пуста, читать по чужому хендлу не из чего. Это и
//! есть мутант трека, и он не выдуман - он есть обычная область дословно.
//!
//! # Чего здесь нет, и это названо
//!
//! [`GATHER`] **не программа корпуса**, и стать ею не может. Договор трёх
//! вычислителей сверяет ответ с машиной, а область машины есть **значение**:
//! `store` отдаёт новую область, прежняя остаётся прежней. Разделяемость есть
//! **тождество**. Программа, которая их различает, есть ровно программа, на
//! которой машина и рантайм обязаны разойтись, - и машина на ней не
//! обрывается, а **застревает**: печатает нередуцированный
//! `regionRead … sharedNew 0`. Это проверяется здесь же
//! ([`the_machine_has_no_answer_for_a_shared_area`]), чтобы утверждение
//! «корпусом не берётся» стояло числом, а не доводом.
//!
//! Корпусная половина при этом есть: `shared-workers` берётся всеми тремя
//! вычислителями, потому что задача читает **свою** ячейку. Она проверяет, что
//! укладка из нескольких воркеров работает и не течёт; она **не** проверяет,
//! что область одна.

mod harness;

/// Сколько раз гонять каждую программу.
///
/// То же число и по той же причине, что в `threads.rs`: планировщик разводит
/// файберы по-разному, и один зелёный прогон значит «в этот раз повезло».
const RUNS: usize = 24;

/// Сколько воркеров просить.
const THREADS: &str = "4";

/// Общая шапка: единица, укладка, разделяемая стратегия.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

type Layout = { size : UInt32, align : UInt32 }

class Flat a where
  layout : Layout

module type AllocStrategy where
  type Block
  new   : Unit -> Block
  store : {Flat a} => Block -> a -> Block
  here  : Block -> Ptr
  load  : {Flat a} => Block -> Ptr -> a
  free  : Block -> Ptr -> Block

module SharedArena : AllocStrategy where
  type Block = Block

  new : Unit -> Block
  new u = sharedNew

  store : {Flat a} => Block -> a -> Block
  store r x = regionAlloc r x

  here : Block -> Ptr
  here r = regionLast r

  load : {Flat a} => Block -> Ptr -> a
  load r p = regionRead r p

  free : Block -> Ptr -> Block
  free r p = r

data Sum where
  MkSum : Int64 -> Sum

data Cell where
  MkCell : Ptr -> Cell

data Task where
  MkTask : Cell -> Task

effect Async where
  suspend : Unit
  spawn : ({Async} Cell) -> Task
  await : (1 t : Task) -> Cell

withNursery : ({Async} Sum) -> Sum

unsum : Sum -> Int64
unsum (MkSum n) = n

unhandle : Cell -> Ptr
unhandle (MkCell p) = p
";

/// Корень читает то, что уложили задачи: область обязана быть **одна**.
///
/// Задача возвращает свой хендл, корень читает по нему из **своей** ссылки на
/// ту же область. У обычной области корневая ссылка - копия, сделанная при
/// первой же укладке задачи, и пустая: читать по чужому хендлу не из чего.
///
/// Слагаемые степенями двойки: столкнись два хендла, сумма назвала бы, какие.
/// Ответ от порядка файберов не зависит - `await` собирает их в написанном
/// порядке, а хендлы в ответ не попадают.
///
/// Уступки здесь нет нарочно. Хендл последней укладки у разделяемой области
/// принадлежит **воркеру**, а не файберу, и файбер, уступивший между `store` и
/// `here`, вправе спросить хендл не свой. Это названная граница, а не дефект
/// прогона, и свидетель ей - соседний `shared-workers`, где уступка стоит
/// **после** `here`.
const GATHER: &str = "\
worker : SharedArena.Block -> Int64 -> {Async} Cell
worker r n =
  let r1 : SharedArena.Block = SharedArena.store r n
  let at : Ptr = SharedArena.here r1
  MkCell at

gather : SharedArena.Block -> {Async} Sum
gather r =
  let t1 : Task = spawn (worker r 1)
  let t2 : Task = spawn (worker r 2)
  let t3 : Task = spawn (worker r 4)
  let t4 : Task = spawn (worker r 8)
  let c1 : Cell = await t1
  let c2 : Cell = await t2
  let c3 : Cell = await t3
  let c4 : Cell = await t4
  let v1 : Int64 = SharedArena.load r (unhandle c1)
  let v2 : Int64 = SharedArena.load r (unhandle c2)
  let v3 : Int64 = SharedArena.load r (unhandle c3)
  let v4 : Int64 = SharedArena.load r (unhandle c4)
  MkSum (addInt64 (addInt64 v1 v2) (addInt64 v3 v4))

main : Int64
main = unsum (withNursery (gather (SharedArena.new MkUnit)))
";

/// Текст программы, читающей чужие ячейки.
fn gather() -> String {
    format!("{SHAPE}{GATHER}")
}

/// Она же над **обычной** областью: мутант трека, и он дословно прежний код.
fn gather_unshared() -> String {
    gather().replace("new u = sharedNew", "new u = regionNew")
}

/// Корпусная программа: задачи укладывают в одну область и читают своё.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn corpus_program() -> String {
    let path = harness::corpus().join("shared-workers.adamas");
    std::fs::read_to_string(&path).expect("фикстура `shared-workers` обязана читаться")
}

/// Воркеры укладывают в одну область, ответ сходится с машиной, блоков ноль.
///
/// Наблюдаемых три, и третье несущее: без него тест был бы зелёным и у круга,
/// оставшегося однопоточным, - а тогда «работает из нескольких воркеров»
/// проверялось бы одним воркером.
#[test]
fn the_corpus_program_allocates_from_several_workers() {
    let source = corpus_program();
    let expected = harness::machine_printed(&source)
        .unwrap_or_else(|why| panic!("машина обязана отвечать, а сказала `{why}`"));
    let mut spread = 0;
    for run in 0..RUNS {
        let ran =
            harness::c_printed_with("shared.workers", &source, &[("ADAMAS_THREADS", THREADS)]);
        assert_eq!(
            ran.printed,
            expected,
            "прогон {run} на потоках ответил не то, что машина; stderr `{}`",
            ran.reason.trim_end()
        );
        assert_eq!(
            ran.live,
            Some(0),
            "прогон {run} оставил блоки живыми: `{}`",
            ran.reason.trim_end()
        );
        if ran.reason.contains("потоков выдавало") {
            spread += 1;
        }
    }
    assert!(
        spread > 0,
        "ни один прогон не аллоцировал на воркере: круг остался однопоточным, \
         и совпадение ответа ничего не говорит про несколько воркеров"
    );
    eprintln!(
        "`shared-workers` на {THREADS} потоках: {RUNS} прогонов, ответ {expected}, \
         {spread} с работой на воркере"
    );
}

/// Он же на LLVM-пути: тот же текст, те же потоки, тот же ответ.
///
/// Различий у двух бэкендов здесь нет ни одного - и область, и потоки живут в
/// рантайме, общем у обоих, - но сказать это и показать это разные вещи:
/// линковка у LLVM-пути своя, и `adamas_shared_new` объявляется отдельным
/// `declare`.
#[test]
fn the_llvm_path_allocates_from_several_workers_too() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = adamas_codegen::llvm::Pipeline::optimised();
    let source = corpus_program();
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    let artefacts = harness::llvm_text("разделяемая-корпус", &source)
        .expect("разделяемая область обязана браться эмиттером");
    let binary = harness::llvm_binary("shared.workers.llvm", &artefacts, &tools, &pipeline);

    let mut spread = 0;
    for run in 0..RUNS {
        let ran = std::process::Command::new(&binary)
            .env("ADAMAS_THREADS", THREADS)
            .output()
            .expect("бинарь обязан запускаться");
        let printed = String::from_utf8_lossy(&ran.stdout).trim_end().to_owned();
        let counted = String::from_utf8_lossy(&ran.stderr).into_owned();
        assert_eq!(
            printed,
            expected,
            "LLVM-путь: прогон {run} ответил не то; stderr `{}`",
            counted.trim_end()
        );
        let (_, live) = harness::blocks(
            "разделяемая-корпус",
            counted.lines().next().unwrap_or_default(),
        );
        assert_eq!(live, 0, "LLVM-путь: прогон {run} оставил блоки живыми");
        if counted.contains("потоков выдавало") {
            spread += 1;
        }
    }
    eprintln!(
        "LLVM-путь на {THREADS} потоках: {RUNS} прогонов, ответ {expected}, \
         {spread} с работой на воркере"
    );
}

/// Корень читает уложенное задачей - то есть область одна, а не четыре копии.
///
/// Обе половины обязательны. Честная обязана ответить 15 и не оставить блоков;
/// мутант - **обычная область дословно** - обязан оборваться, потому что
/// корневая копия пуста. Без мутанта утверждение «область одна» держалось бы
/// на том, что ответ правдоподобен: у четырёх копий он был бы таким же, читай
/// задача своё.
#[test]
fn the_root_reads_what_the_workers_placed() {
    let honest = gather();
    for run in 0..RUNS {
        let ran = harness::c_printed_with("shared.gather", &honest, &[("ADAMAS_THREADS", THREADS)]);
        assert_eq!(
            ran.printed.trim_end(),
            "15",
            "прогон {run}: корень прочитал не то, что уложили задачи; stderr `{}`",
            ran.reason.trim_end()
        );
        assert_eq!(
            ran.live,
            Some(0),
            "прогон {run} оставил блоки живыми: `{}`",
            ran.reason.trim_end()
        );
    }

    let broken = gather_unshared();
    assert_ne!(
        broken, honest,
        "мутант не встал: `sharedNew` в тексте не нашлась"
    );
    let ran = harness::c_printed_with(
        "shared.gather.plain",
        &broken,
        &[("ADAMAS_THREADS", THREADS)],
    );
    assert_ne!(
        ran.printed.trim_end(),
        "15",
        "обычная область ответила то же: копии при лишней ссылке не случилось, \
         и свидетель не различает разделяемую от обычной"
    );
    eprintln!(
        "корень над разделяемой: 15 на {RUNS} прогонах; над обычной: `{}` / `{}`",
        ran.printed.trim_end(),
        ran.reason.trim_end()
    );
}

/// Он же на LLVM-пути: два бэкенда обязаны сойтись **между собой**.
///
/// Машины в этом договоре нет по построению (см. шапку), поэтому сверяются
/// двое из трёх - и сверяются с числом, а не друг с другом наугад.
#[test]
fn the_llvm_path_reads_what_the_workers_placed_too() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = adamas_codegen::llvm::Pipeline::optimised();
    let source = gather();
    let artefacts = harness::llvm_text("разделяемая-сбор", &source)
        .expect("разделяемая область обязана браться эмиттером");
    let binary = harness::llvm_binary("shared.gather.llvm", &artefacts, &tools, &pipeline);

    for run in 0..RUNS {
        let ran = std::process::Command::new(&binary)
            .env("ADAMAS_THREADS", THREADS)
            .output()
            .expect("бинарь обязан запускаться");
        let printed = String::from_utf8_lossy(&ran.stdout).trim_end().to_owned();
        let counted = String::from_utf8_lossy(&ran.stderr).into_owned();
        assert_eq!(
            printed,
            "15",
            "LLVM-путь: прогон {run} прочитал не то; stderr `{}`",
            counted.trim_end()
        );
        let (_, live) = harness::blocks(
            "разделяемая-сбор",
            counted.lines().next().unwrap_or_default(),
        );
        assert_eq!(live, 0, "LLVM-путь: прогон {run} оставил блоки живыми");
    }
    eprintln!("LLVM-путь над разделяемой: 15 на {RUNS} прогонах, живых блоков ноль");
}

/// У машины ответа на эту программу нет, и это свойство модели.
///
/// Утверждение шапки - «корпусом такая программа не берётся» - проверяется
/// прогоном, а не доводом. Машина не обрывается: она **застревает**, печатая
/// нередуцированный `regionRead` над пустой областью. Область ядра есть
/// значение, `store` отдаёт новую, и корневая переменная остаётся той же
/// пустой, какой родилась.
///
/// Тест сторожит и обратное. Начни машина отвечать числом - значит область
/// ядра обзавелась тождеством, и тогда `GATHER` обязана переехать в корпус, а
/// не остаться здесь.
#[test]
fn the_machine_has_no_answer_for_a_shared_area() {
    let printed = harness::machine_printed(&gather());
    let stuck = match &printed {
        Ok(text) => text.clone(),
        Err(why) => why.clone(),
    };
    assert!(
        stuck.contains("regionRead") && stuck.contains("sharedNew"),
        "машина ответила `{stuck}`: у области ядра появилось тождество, и \
         `GATHER` пора в корпус"
    );
    eprintln!("машина о разделяемой области: застревает на `regionRead … sharedNew`");
}

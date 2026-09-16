//! Круг питомника на **настоящих потоках** (§5.2).
//!
//! # Что здесь наблюдается, и почему обычного прогона мало
//!
//! Многопоточный круг отвечает то же, что однопоточный, - в этом и вся его
//! ценность, - и оттого зелёный прогон сам по себе не значит ничего: он
//! одинаков и когда воркеры взяли работу, и когда её всю взял хозяин, и когда
//! потоки не завелись вовсе. Наблюдаемое поэтому **двойное**:
//!
//! 1. *Ответ.* Он обязан совпасть с машиной, и совпасть **на каждом** прогоне:
//!    гонка не воспроизводится по требованию, и один зелёный прогон значит «в
//!    этот раз повезло». Прогонов здесь [`RUNS`].
//! 2. *Что потоки работали.* Точка входа печатает `потоков выдавало N`, когда
//!    ряд счётчика блоков завёл больше одного потока, - то есть когда файбер
//!    **аллоцировал на воркере**. Строка эта у однопоточного прогона не
//!    печатается вовсе, и её отсутствие роняет тест.
//!
//! Различающая сила второго проверена снятием переменной: без `ADAMAS_THREADS`
//! та же программа даёт тот же ответ и **не** печатает строки. То есть первый
//! свидетель без второго проверял бы, что питомник не сломан, а не что он
//! поехал на потоках.
//!
//! # Счёт живых блоков на **каждом** прогоне - не украшение
//!
//! Он и нашёл единственный настоящий дефект трека, и нашёл его тем, что ответ
//! был **верен**. Вектор evidence файбера считался неатомарно: пометить один
//! `nursery->base` мало, потомки её не наследовали. Проявлялось это как
//! «живо 1» примерно раз в трёхстах прогонов, и только на занятой машине; под
//! шестью копиями стенда разом - как `malloc_consolidate(): unaligned fastbin
//! chunk`, то есть порча кучи.
//!
//! Санитайзер назвал место сразу, как только его позвали на **эту** программу:
//! 29 гонок из 40 прогонов, `adamas_evidence_dup` против `adamas_evidence_drop`
//! из двух воркеров. После наследования пометки - 0 из 40 и 0 живых из 1500
//! прогонов под шестью копиями.
//!
//! Мораль, которая стоила трека: санитайзер над **стендом** не покрывает
//! программу корпуса. Гонка была на пути, которого стенд не проходил.
//!
//! # Чего здесь нет
//!
//! *Программ со следом.* Порядок файберов под потоками не определён, и всякая
//! программа, печатающая отметки задач, отвечает иначе - это свойство модели, а
//! не дефект. Корпусная программа взята ровно та, чей ответ от порядка не
//! зависит: `await-value` считает два питомника и отвечает парой пятёрок.
//!
//! *Обрыва наружу круга.* Под кадром питомника у воркера пусто, и раскручивать
//! оттуда нечего; рантайм говорит об этом вслух. Свидетель этому - ниже.
//!
//! LLVM-путь при этом **проверяется наравне** с C-стороной, хотя различий у
//! них здесь нет ни одного: потоки живут целиком в рантайме, общем у двух
//! бэкендов. Проверяется потому, что линковка у него своя - обёртка
//! `adamas_promote_extern` видна только из спутника.

mod harness;

/// Сколько раз гонять каждую программу.
///
/// Не круглое: столько, чтобы прогон оставался быстрым (около трёх секунд), а
/// планировщик успел развести файберы по-разному. Гонка ловится этим
/// **вероятностно** - тем же способом, что и в `adamas-runtime/tests/atomic.rs`,
/// - и рядом поэтому стоит санитайзер (`adamas-runtime/tests/race.rs`).
const RUNS: usize = 24;

/// Сколько воркеров просить.
const THREADS: &str = "4";

/// Общая шапка: единица, числа, списки.
const SHAPE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a
";

/// Восемь задач **над одним списком**: тот самый захват, ради которого стоит
/// место вызова промоушена.
///
/// Форма выбрана двумя требованиями сразу, и ни одно не косметическое.
///
/// *Восемь, а не одна.* Корпусной `await-value` для наблюдаемого «файберы
/// разъехались» не годится, и это измерено: задача у него по одной на круг, и
/// хозяин успевает взять её сам прежде, чем воркер проснётся.
///
/// *Список **захвачен**, а не построен внутри.* `spawn (work xs)` кладёт `xs` в
/// захват замыкания, и оттого он достижим из восьми файберов и из самого
/// корневого разом. Без захвата промоушен нечему было бы метить: свою память
/// файбер считает сам, и снять её мутантом не получилось бы - `total (build 24)`
/// внутри задачи гонки не даёт ни с промоушеном, ни без него (проверено:
/// санитайзер молчит на обоих).
///
/// Ответ от порядка не зависит: у задач его нет вовсе, `await` собирает их в
/// написанном порядке. Это и есть условие, при котором многопоточный круг
/// сверяется с машиной.
const MANY: &str = "\
data Task where
  MkTask : Nat -> Task

effect Async where
  suspend : Unit
  spawn : ({Async} Nat) -> Task
  await : (1 t : Task) -> Nat

withNursery : ({Async} Nat) -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

-- Список длины `n`: он и будет тем, что уезжает в чужой поток.
build : Nat -> List Nat
build Zero = Nil
build (Succ k) = Cons 1 (build k)

-- Свёртка разбирает звенья, то есть трогает их счётчики.
total : List Nat -> Nat
total Nil = Zero
total (Cons x xs) = plus x (total xs)

-- Уступка посередине: файбер обязан пережить переезд между воркерами, и второй
-- проход по списку идёт уже на другом стеке.
work : List Nat -> {Async} Nat
work xs =
  let a : Nat = total xs
  let s : Unit = suspend
  let b : Nat = total xs
  plus a b

eight : {Async} Nat
eight =
  let xs : List Nat = build 24
  let t1 : Task = spawn (work xs)
  let t2 : Task = spawn (work xs)
  let t3 : Task = spawn (work xs)
  let t4 : Task = spawn (work xs)
  let t5 : Task = spawn (work xs)
  let t6 : Task = spawn (work xs)
  let t7 : Task = spawn (work xs)
  let t8 : Task = spawn (work xs)
  let mine : Nat = total xs
  let a1 : Nat = await t1
  let a2 : Nat = await t2
  let a3 : Nat = await t3
  let a4 : Nat = await t4
  let a5 : Nat = await t5
  let a6 : Nat = await t6
  let a7 : Nat = await t7
  let a8 : Nat = await t8
  plus mine (plus (plus (plus a1 a2) (plus a3 a4)) (plus (plus a5 a6) (plus a7 a8)))

main : Nat
main = withNursery eight
";

/// Нагрузка под цену промоушена: восемь задач гоняют **разделённый** список.
///
/// Форма взята у `workload-fbip` дословно - `Int64`, хвостовая свёртка, размеры
/// двумя строками, - потому что мерить надо RC-трафик, а не арифметику. Каждый
/// проход `total` разбирает `cells` звеньев, то есть дупает и дропает их: после
/// промоушена все эти пары атомарны, до него - нет. Это и есть то, что стоит
/// 4.2 раза (§5.2), и вот на чём оно видно.
///
/// Уступка стоит **между** проходами: без неё файбер не переезжает, и половина
/// многопоточности не задействована.
const GRIND: &str = "\
data Unit where
  MkUnit : Unit

-- Литеральный паттерн отвечает `Bool` (§4.3): без объявления `build 0` не
-- проверяется. Тот же довод и в `workload-fbip`.
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

data Sum where
  MkSum : Int64 -> Sum

-- Поле задачи **указательное**: туда встаёт невыразимое имя файбера, а плоский
-- `Int64` слотом для него не годится - рантайм отвергает такой тип на месте
-- («нужен один конструктор с одним полем»).
data Task where
  MkTask : Sum -> Task

-- Ответ операции обязан быть указательным: плоский `Int64` понижение отвергает
-- на месте («ответ операции: указательное значение, а не плоское `Int64`»), и
-- по тому же счёту его отвергает приостанавливающаяся функция. Число поэтому
-- ездит через задачу в обёртке `Sum`; арифметика внутри остаётся плоской.
effect Async where
  suspend : Unit
  spawn : ({Async} Sum) -> Task
  await : (1 t : Task) -> Sum

withNursery : ({Async} Sum) -> Sum

cells : Int64
cells = 4096

passes : Int64
passes = 96

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

total : List -> Int64 -> Int64
total Nil acc = acc
total (Cons x xs) acc = total xs (addInt64 acc x)

unsum : Sum -> Int64
unsum (MkSum n) = n

grind : Int64 -> List -> Int64 -> {Async} Sum
grind 0 xs acc = MkSum acc
grind n xs acc =
  let s : Unit = suspend
  grind (subInt64 n 1) xs (addInt64 acc (total xs 0))

work : List -> {Async} Sum
work xs = grind passes xs 0

eight : {Async} Sum
eight =
  let xs : List = build cells Nil
  let t1 : Task = spawn (work xs)
  let t2 : Task = spawn (work xs)
  let t3 : Task = spawn (work xs)
  let t4 : Task = spawn (work xs)
  let t5 : Task = spawn (work xs)
  let t6 : Task = spawn (work xs)
  let t7 : Task = spawn (work xs)
  let t8 : Task = spawn (work xs)
  let a1 : Sum = await t1
  let a2 : Sum = await t2
  let a3 : Sum = await t3
  let a4 : Sum = await t4
  let a5 : Sum = await t5
  let a6 : Sum = await t6
  let a7 : Sum = await t7
  let a8 : Sum = await t8
  MkSum (addInt64
    (addInt64 (addInt64 (unsum a1) (unsum a2)) (addInt64 (unsum a3) (unsum a4)))
    (addInt64 (addInt64 (unsum a5) (unsum a6)) (addInt64 (unsum a7) (unsum a8))))

main : Int64
main = unsum (withNursery eight)
";

/// Сколько прогонов под замер. Оценка - **пол** выборки: помеха ко времени
/// процесса только прибавляет, та же методика, что у таблицы разрыва.
const TIMED: usize = 7;

/// Ветвь, которой промоушен спрашивает «а уезжает ли вообще что-нибудь».
///
/// Снять её - значит звать промоушен **всегда**, в том числе на однопоточном
/// круге. Программа от этого остаётся верной (лишняя пометка безвредна), и
/// ровно это делает её годным вторым концом замера: обе стороны считают одно и
/// то же, различие ровно одно - платится промоушен или нет.
const GUARD: [&str; 2] = [
    "    if (nursery->hands != 0) {\n        adamas_share(body, nursery->promote);\n    }\n",
    "    if (nursery->hands != 0) {\n        adamas_share(value, nursery->promote);\n    }\n",
];

/// Те же строки без ветви.
const ALWAYS: [&str; 2] = [
    "    adamas_share(body, nursery->promote);\n",
    "    adamas_share(value, nursery->promote);\n",
];

/// Собирает порождённый C с `-O2` и отдаёт путь к бинарю.
///
/// `forced` - собрать рантайм с промоушеном **без ветви**: мера ниже сравнивает
/// два рантайма, а не два режима одного.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn optimised(stem: &str, text: &str, forced: bool) -> std::path::PathBuf {
    let dir = harness::scratch().join("timed");
    let _ = std::fs::create_dir_all(&dir);
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).expect("стенд обязан записываться");
    let sources = std::path::Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let units: Vec<std::path::PathBuf> = env!("ADAMAS_RUNTIME_UNITS")
        .split(',')
        .map(|unit| {
            let at = sources.join(unit);
            if !forced || unit != "fiber.c" {
                return at;
            }
            let mut fiber =
                std::fs::read_to_string(&at).expect("исходник рантайма обязан читаться");
            for (guard, always) in GUARD.iter().zip(ALWAYS) {
                assert!(
                    fiber.contains(guard),
                    "ветвь промоушена не нашлась в `fiber.c`: замер перестал измерять"
                );
                fiber = fiber.replace(guard, always);
            }
            let copy = dir.join("fiber.forced.c");
            std::fs::write(&copy, fiber).expect("копия рантайма обязана записываться");
            copy
        })
        .collect();
    let compiled = std::process::Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O2", "-fwrapv", "-ffp-contract=off", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(&units)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    assert!(
        compiled.status.success(),
        "стенд не собрался:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    binary
}

/// Пол выборки из [`TIMED`] прогонов, в миллисекундах, плюс напечатанный ответ.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn floor_ms(binary: &std::path::Path, threads: Option<&str>) -> (u128, String) {
    let mut best = u128::MAX;
    let mut printed = String::new();
    for _ in 0..TIMED {
        let mut started = std::process::Command::new(binary);
        if let Some(many) = threads {
            started.env("ADAMAS_THREADS", many);
        }
        let at = std::time::Instant::now();
        let ran = started.output().expect("стенд обязан запускаться");
        let took = at.elapsed().as_micros();
        best = best.min(took);
        String::from_utf8_lossy(&ran.stdout)
            .trim_end()
            .clone_into(&mut printed);
    }
    (best / 1000, printed)
}

/// **Цена места вызова промоушена**, измеренная, а не рассуждённая.
///
/// # Почему не нагрузкой из таблицы разрыва
///
/// Правило вопроса 175 требует мерить правку горячего пути нагрузкой оттуда, и
/// здесь оно **не применимо**, а не обойдено: ни одна из пяти программ таблицы
/// не заводит питомника вовсе, поэтому места вызова промоушена ни одна из них
/// не проходит. Проверено грепом по порождённому C: `adamas_nursery_` в них
/// ноль вхождений. Мерится поэтому нагрузка того же жанра - RC-трафик по
/// разделённому списку, форма взята у строки 3 (FBIP-цикл).
///
/// Прочие правки трека таблицу задевают, и там правило применено: см. отчёт.
///
/// # Что с чем сравнивается, и чем **не** годится очевидный второй конец
///
/// Очевидный второй конец - обезврежить обход ([`defused`]) и сравнить при
/// четырёх воркерах - **измеряет не то**, и это замерено, а не предположено:
/// 22 мс с промоушеном против 137 без него, то есть промоушен как будто
/// ускоряет в шесть раз. Причина в том, что обезвреженная половина считает
/// **другую программу**: без пометки счётчики разделённого списка правятся
/// голым `+=` из четырёх потоков, звенья гибнут не вовремя, и обход идёт по
/// тому, чего уже нет. Как свидетель гонки эта половина годна (санитайзер
/// выше), как второй конец замера - нет.
///
/// Годный второй конец - тот, где **обе** стороны верны. Берётся он так: круг
/// однопоточный в обоих случаях, а рантайм собирается дважды - со ветвью
/// `hands != 0` перед промоушеном и без неё. Лишняя пометка программу не
/// ломает, она только стоит; разница и есть цена места вызова.
///
/// Третьим числом печатается то, ради чего всё затевалось: та же программа на
/// четырёх воркерах против однопоточной.
///
/// # Что вышло
///
/// Четыре прогона: **1.440, 1.407, 1.404, 1.283** - цена промоушена на этой
/// нагрузке, и **0.400, 0.407, 0.442, 0.400** - что дают четыре воркера против
/// одного. Последний прогон шёл вперемежку с соседними тестами, оттого и
/// меньше; медиана 1.41. То есть налог 1.4 раза окупается ускорением 2.5 раза;
/// чистый выигрыш 20-24 мс против 50-60.
///
/// Записанные 4.2 раза (§5.2) - **потолок на микронагрузке**, где кроме пары
/// `dup`/`drop` не происходит ничего. На нагрузке, где счётчик - часть обхода,
/// а не весь он, выходит 1.41. Расхождение названо здесь, а не в отчёте, потому
/// что число 4.2 читается как цена промоушена и ею не является.
///
/// Утверждения о времени тест не делает: машина под прогоном не тихая. Он
/// печатает числа и проверяет, что **все три** стороны считают верно.
#[test]
fn the_promotion_at_spawn_costs_this_much() {
    // Ответ считан, а не спрошен у машины, и это не небрежность: три миллиона
    // обходов звена тому же тайл-уокеру не по силам - тем же доводом, каким
    // `workload-fbip` объясняет, почему стенд подставляет размеры сам. Согласие
    // с машиной несут свидетели выше, на корпусном размере.
    //
    // Сумма `1..cells` на `passes` проходов на восемь задач.
    let expected = (8_i64 * 96 * 4096 * 4097 / 2).to_string();
    let text = harness::compiled(GRIND).expect("нагрузка обязана браться C-эмиттером");
    let guarded = optimised("grind.guarded", &text, false);
    let forced = optimised("grind.forced", &text, true);

    let (alone, answer) = floor_ms(&guarded, None);
    assert_eq!(answer, expected, "однопоточный круг посчитал не то");
    let (always, answer) = floor_ms(&forced, None);
    assert_eq!(
        answer, expected,
        "однопоточный круг с промоушеном посчитал не то"
    );
    let (spread, answer) = floor_ms(&guarded, Some(THREADS));
    assert_eq!(answer, expected, "круг на потоках посчитал не то");

    #[allow(clippy::cast_precision_loss, reason = "миллисекунды, не деньги")]
    let ratio = always as f64 / alone.max(1) as f64;
    #[allow(clippy::cast_precision_loss, reason = "миллисекунды, не деньги")]
    let gain = spread as f64 / alone.max(1) as f64;
    eprintln!(
        "цена промоушена: {always} мс с ним против {alone} без, оба однопоточные и оба верны, \
         то есть {ratio:.3} раза; та же программа на {THREADS} воркерах {spread} мс, \
         то есть {gain:.3} от однопоточной; пол {TIMED} прогонов"
    );
}

/// Обрыв наружу круга из мигрировавшего файбера: рантайм говорит об этом вслух.
///
/// Задача производит операцию, чей хендлер стоит **снаружи** `withNursery`, и
/// ветка его абортивна. Раскрутка проходит через кадр питомника задачи - а под
/// ним у воркера пусто, потому что стек `withNursery` остался у хозяина.
/// Продолжать обрыв некуда, и рантайм это называет, а не портит стек.
///
/// Задач восемь по той же причине, что и в [`MANY`]: одну хозяин забирает себе
/// прежде, чем воркер проснётся, и граница не задевается.
const ABORTING: &str = "\
data Bool where
  False : Bool
  True : Bool

effect Fail where
  fail : Bool

effect Async where
  suspend : Unit
  spawnDetached : ({Async, Fail} Unit) -> Unit

withNursery : ({Async, Fail} Unit) -> {Fail} Unit

child : {Async, Fail} Unit
child =
  let s : Unit = suspend
  let n : Bool = fail
  MkUnit

inner : {Async, Fail} Unit
inner =
  let a : Unit = spawnDetached child
  let b : Unit = spawnDetached child
  let c : Unit = spawnDetached child
  let d : Unit = spawnDetached child
  let e : Unit = spawnDetached child
  let f : Unit = spawnDetached child
  let g : Unit = spawnDetached child
  let h : Unit = spawnDetached child
  let s : Unit = suspend
  MkUnit

nursed : {Fail} Unit
nursed = withNursery inner

main : List Nat
main = handle nursed with
  return v -> Nil
  fail -> Nil
";

/// Корпусная программа, чей ответ от порядка файберов не зависит.
fn corpus_program() -> String {
    let path = harness::corpus().join("await-value.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|_| panic!("фикстура {} обязана читаться", path.display()))
}

/// Гоняет программу `RUNS` раз и сверяет каждый ответ с машиной.
///
/// Отдаёт, на скольких прогонах точка входа сказала «потоков выдавало».
fn agreeing(name: &str, source: &str) -> usize {
    let expected = harness::machine_printed(source)
        .unwrap_or_else(|why| panic!("{name}: машина обязана отвечать, а сказала `{why}`"));
    let mut spread = 0;
    for run in 0..RUNS {
        let ran = harness::c_printed_with(name, source, &[("ADAMAS_THREADS", THREADS)]);
        assert_eq!(
            ran.printed,
            expected,
            "{name}: прогон {run} на потоках ответил не то, что машина; stderr `{}`",
            ran.reason.trim_end()
        );
        assert_eq!(
            ran.live,
            Some(0),
            "{name}: прогон {run} оставил блоки живыми: `{}`",
            ran.reason.trim_end()
        );
        if ran.reason.contains("потоков выдавало") {
            spread += 1;
        }
    }
    spread
}

/// Программа корпуса считается на нескольких потоках и отвечает то же.
///
/// Наблюдаемых два, и второе - несущее: без него тест был бы зелёным и у
/// круга, оставшегося однопоточным.
#[test]
fn a_corpus_program_computes_on_several_threads() {
    let source = corpus_program();
    let spread = agreeing("threads.await-value", &source);
    eprintln!(
        "`await-value` на {THREADS} потоках: {RUNS} прогонов, ответ тот же, {spread} с работой на воркере"
    );
}

/// Он же на LLVM-пути: тот же текст, те же потоки, тот же ответ.
///
/// Стоит здесь не для полноты. Различий у двух бэкендов в этом месте нет ни
/// одного - потоки живут целиком в рантайме, общем у обоих, - но сказать это и
/// показать это разные вещи, а линковка у LLVM-пути своя: `promote.c` печатает
/// понижение, и обёртка `adamas_promote_extern` видна только из спутника.
#[test]
fn the_llvm_path_computes_on_several_threads_too() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = adamas_codegen::llvm::Pipeline::optimised();
    let source = corpus_program();
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    let artefacts =
        harness::llvm_text("потоки-корпус", &source).expect("питомник обязан браться эмиттером");
    let binary = harness::llvm_binary("threads.await-value.llvm", &artefacts, &tools, &pipeline);

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
            "LLVM-путь: прогон {run} на потоках ответил не то; stderr `{}`",
            counted.trim_end()
        );
        let (_, live) =
            harness::blocks("потоки-корпус", counted.lines().next().unwrap_or_default());
        assert_eq!(live, 0, "LLVM-путь: прогон {run} оставил блоки живыми");
        if counted.contains("потоков выдавало") {
            spread += 1;
        }
    }
    eprintln!(
        "LLVM-путь на {THREADS} потоках: {RUNS} прогонов, ответ тот же, {spread} с работой на воркере"
    );
}

/// Восемь задач: файберы **обязаны** разъехаться, и это видно числом.
#[test]
fn eight_tasks_spread_across_the_workers() {
    let source = format!("{SHAPE}{MANY}");
    let spread = agreeing("threads.many", &source);
    assert!(
        spread > 0,
        "ни один прогон не аллоцировал на воркере: круг остался однопоточным, \
         и совпадение ответа ничего не говорит"
    );
    eprintln!(
        "восемь задач на {THREADS} потоках: {spread} прогонов из {RUNS} с работой на воркере"
    );
}

/// Та же программа без переменной: ответ тот же, строки про потоки нет.
///
/// Это **вторая половина** второго наблюдаемого. Без неё «потоков выдавало»
/// могло бы печататься всегда, и число выше ничего бы не различало.
#[test]
fn without_the_variable_the_round_stays_single_threaded() {
    let source = format!("{SHAPE}{MANY}");
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    let ran = harness::c_printed("threads.many.alone", &source);
    assert_eq!(ran.printed, expected, "однопоточный круг ответил не то");
    assert_eq!(
        ran.live,
        Some(0),
        "однопоточный прогон оставил блоки живыми"
    );
    assert!(
        !ran.reason.contains("потоков выдавало"),
        "без `ADAMAS_THREADS` круг завёл воркеров: `{}`",
        ran.reason.trim_end()
    );
    eprintln!(
        "без переменной: тот же ответ, воркеров нет, {}",
        ran.reason.trim_end()
    );
}

/// Обход промоушена, обезвреженный дословно.
///
/// Мутант не выдуман: до этого трека места вызова у промоушена не было вовсе, и
/// значение уезжало в чужой поток локальным. Обезвреживается здесь **обход
/// детей**, а не сам `adamas_share`: так пометка встаёт на теле задачи и до
/// захвата не доходит - ровно то, чем был бы промоушен без транзитивности.
///
/// Правится порождённый C, а не рантайм: рантайм собирается санитайзером тут же
/// и один на обе половины, а `promote.c` печатает понижение - его и правим.
fn defused(text: &str) -> String {
    const HONEST: &str = "static void adamas_share_value(adamas_value value) {\n\
                          \x20   adamas_share(value, adamas_promote_value);\n}";
    const BROKEN: &str = "static void adamas_share_value(adamas_value value) { (void)value; }";
    assert!(
        text.contains(HONEST),
        "обход промоушена не нашёлся в порождённом C: мутант перестал быть мутантом"
    );
    text.replace(HONEST, BROKEN)
}

/// Что сказал прогон под санитайзером.
struct Watched {
    /// Назвал ли санитайзер гонку.
    raced: bool,
    /// Что стенд напечатал в stdout.
    printed: String,
}

/// Собирает порождённый C санитайзером **вместе с рантаймом** и гоняет его.
///
/// Рантайм пересобирается, а не берётся готовым: `TSan` видит только то, что
/// инструментировано, и счётчик, собранный без него, оказался бы невидим. Тот
/// же довод и тот же приём, что в `adamas-runtime/tests/race.rs`.
///
/// `None` - санитайзер у этого компилятора недоступен.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn watched(stem: &str, text: &str, runtime: Option<(&str, &str)>) -> Option<Watched> {
    let dir = harness::scratch().join("tsan");
    let _ = std::fs::create_dir_all(&dir);
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).expect("стенд обязан записываться");
    let sources = std::path::Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let units: Vec<std::path::PathBuf> = env!("ADAMAS_RUNTIME_UNITS")
        .split(',')
        .map(|unit| {
            let at = sources.join(unit);
            let Some((from, to)) = runtime else {
                return at;
            };
            let read = std::fs::read_to_string(&at).expect("исходник рантайма обязан читаться");
            if !read.contains(from) {
                return at;
            }
            let copy = dir.join(format!("{stem}.{unit}"));
            std::fs::write(&copy, read.replace(from, to)).expect("копия обязана записываться");
            copy
        })
        .collect();
    if let Some((from, _)) = runtime {
        assert!(
            units.iter().any(|at| at.starts_with(&dir)),
            "правка рантайма не нашла места: `{from}` перестало быть мутантом"
        );
    }
    let compiled = std::process::Command::new(env!("ADAMAS_CC"))
        .args([
            "-std=c11",
            "-O1",
            "-g",
            "-fsanitize=thread",
            "-pthread",
            "-Wno-unused",
        ])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(&units)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    if !compiled.status.success() {
        eprintln!(
            "ThreadSanitizer недоступен у `ADAMAS_CC`, многопоточный круг этим прогоном не \
             проверялся:\n{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        return None;
    }
    // `halt_on_error` - не украшение, а условие завершимости, и это измерено:
    // ломаная половина считает **испорченный** список, и однажды она провисела
    // больше десяти минут, не договорив. Санитайзеру довольно первой найденной
    // гонки; честной половине останавливаться не на чем, и она идёт до конца.
    let mut child = std::process::Command::new(&binary)
        .env("ADAMAS_THREADS", THREADS)
        .env("TSAN_OPTIONS", "halt_on_error=1")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("стенд обязан запускаться");
    // Второй предел, на случай если санитайзер до гонки не доберётся: без него
    // зависший стенд вешал бы прогон вместо того, чтобы отличаться.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
    while child
        .try_wait()
        .expect("ожидание обязано работать")
        .is_none()
    {
        if std::time::Instant::now() >= deadline {
            let _ = child.kill();
            break;
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    let ran = child
        .wait_with_output()
        .expect("вывод стенда обязан читаться");
    Some(Watched {
        raced: String::from_utf8_lossy(&ran.stderr).contains("data race"),
        printed: String::from_utf8_lossy(&ran.stdout).trim_end().to_owned(),
    })
}

/// Санитайзер молчит на промоушене и кричит без него.
///
/// Обе половины обязательны, и это правило волны: без первой утверждение
/// «атомарно» держалось бы на том, что инструмент не запустился; без второй - на
/// том, что он ничего не умеет ловить.
///
/// Ловится здесь **то самое**, ради чего трек и заведён: захваченный список
/// достижим из восьми файберов на четырёх потоках, и счётчики его звеньев
/// правятся всеми разом. С промоушеном они атомарны, без него - голым `+=`.
#[test]
fn the_sanitizer_names_the_race_the_promotion_at_spawn_removes() {
    let source = format!("{SHAPE}{MANY}");
    let text = harness::compiled(&source).expect("программа обязана браться C-эмиттером");

    let Some(broken) = watched("threads.broken", &defused(&text), None) else {
        return;
    };
    assert!(
        broken.raced,
        "санитайзер не назвал гонку там, где промоушен до захвата не доходит: \
         инструмент не ловит ничего, и молчание на честной половине ничего не значит"
    );

    let honest =
        watched("threads.honest", &text, None).expect("честная половина обязана собираться");
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на круге с промоушеном: место вызова не закрывает того, \
         ради чего поставлено"
    );
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    assert_eq!(
        honest.printed, expected,
        "честная половина под санитайзером посчитала не то"
    );
    eprintln!("санитайзер: без промоушена - гонка, с промоушеном - тишина, ответ {expected}");
}

/// Санитайзер над **программой корпуса**, а не над стендом.
///
/// Заведён находкой, а не полнотой, и находка эта - единственный настоящий
/// дефект трека. Счётчик вектора evidence правился голым `+=`: пометить один
/// `nursery->base` оказалось мало, потомки её не наследовали, а вектор файбера
/// как раз потомок - его дупает `frame_alloc` и дропает `frame_free` **на
/// разных воркерах**. Стенд соседнего теста этого пути не проходит вовсе, и
/// санитайзер над ним молчал.
///
/// Видно это было только числом живых блоков: «живо 1» примерно раз в трёхстах
/// прогонах, а под шестью копиями разом - `malloc_consolidate(): unaligned
/// fastbin chunk`. Ответ при этом каждый раз был верен.
///
/// Мутант - снятое наследование, то есть рантайм дословно до правки: 29 гонок
/// из 40 прогонов. С наследованием - 0 из 40.
#[test]
fn the_sanitizer_is_silent_on_a_corpus_program_too() {
    const INHERIT: &str = "    inherit_shared(extended, parent);\n";
    let source = corpus_program();
    let text = harness::compiled(&source).expect("фикстура обязана браться C-эмиттером");

    let Some(broken) = watched("threads.corpus.broken", &text, Some((INHERIT, ""))) else {
        return;
    };
    assert!(
        broken.raced,
        "санитайзер не назвал гонку на счётчике вектора файбера без наследования пометки: \
         инструмент не ловит ничего, и молчание на честной половине ничего не значит"
    );

    let honest =
        watched("threads.corpus.honest", &text, None).expect("честная половина обязана собираться");
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на корпусной программе: счётчик чего-то остался локальным"
    );
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    assert_eq!(
        honest.printed, expected,
        "честная половина под санитайзером посчитала не то"
    );
    eprintln!("санитайзер над корпусной: без наследования - гонка, с ним - тишина");
}

/// Обрыв наружу круга из мигрировавшего файбера **не выражается**, и это сказано.
///
/// Граница названа, а не обойдена: под кадром питомника у воркера пусто.
/// Однопоточный круг ту же программу считает - парный прогон ниже, - и без него
/// утверждение читалось бы как «питомник сломан».
#[test]
fn an_abort_out_of_a_migrated_fiber_is_named_not_silent() {
    let source = format!("{SHAPE}{ABORTING}");
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");

    // Парная половина: тот же текст без потоков отвечает.
    let alone = harness::c_printed("threads.aborting.alone", &source);
    assert_eq!(alone.printed, expected, "однопоточный круг ответил не то");

    // Многопоточная: либо тот же ответ (обрыв достался хозяину), либо
    // **названный** отказ. Молчаливой порчи стека нет ни в одном исходе.
    let mut named = 0;
    for _ in 0..RUNS {
        let ran =
            harness::c_printed_with("threads.aborting", &source, &[("ADAMAS_THREADS", THREADS)]);
        if ran.printed == expected {
            continue;
        }
        assert_eq!(
            ran.printed, "прогон оборвался",
            "обрыв из мигрировавшего файбера дал третий исход: `{}`",
            ran.printed
        );
        assert!(
            ran.reason.contains("не выражается"),
            "обрыв оборвался не тем: `{}`",
            ran.reason.trim_end()
        );
        named += 1;
    }
    eprintln!("обрыв наружу круга: {named} прогонов из {RUNS} назвали границу вслух");
}

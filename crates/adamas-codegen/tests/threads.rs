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
//! *LLVM-пути.* Различий у него здесь нет ни одного: обе стороны зовут те же
//! `adamas_nursery_*`, а потоки живут целиком в рантайме, общем у двух
//! бэкендов. Проверяется поэтому C-сторона, и сказано это здесь, чтобы молчание
//! не читалось как «не поехало».

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
fn watched(stem: &str, text: &str) -> Option<Watched> {
    let dir = harness::scratch().join("tsan");
    let _ = std::fs::create_dir_all(&dir);
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).expect("стенд обязан записываться");
    let sources = std::path::Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
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
        .args(
            env!("ADAMAS_RUNTIME_UNITS")
                .split(',')
                .map(|unit| sources.join(unit)),
        )
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
    let ran = std::process::Command::new(&binary)
        .env("ADAMAS_THREADS", THREADS)
        .output()
        .expect("стенд обязан запускаться");
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

    let Some(broken) = watched("threads.broken", &defused(&text)) else {
        return;
    };
    assert!(
        broken.raced,
        "санитайзер не назвал гонку там, где промоушен до захвата не доходит: \
         инструмент не ловит ничего, и молчание на честной половине ничего не значит"
    );

    let honest = watched("threads.honest", &text).expect("честная половина обязана собираться");
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

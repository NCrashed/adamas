//! Стенд границы замыкания (§4.11, §5.3, §10 вопрос 189; трек B волны 3 Фазы 8).
//!
//! # Что он мерит
//!
//! Правка трека сняла отказ: плоский массив проходит через замыкание обеими
//! позициями - аргументом и захватом. Сняв отказ, она обязана назвать цену, и
//! цены здесь две, потому что вопросов два.
//!
//! *Первый - что стало с горячим путём.* Ответ на него **не** наносекунда, а
//! байты: порождённый C у всех 114 прежних фикстур корпуса совпал до байта
//! (прогон 2026-09-21, `adamas build --backend c` по каждой фикстуре до и
//! после правки; различие ровно одно - новая фикстура, отказывавшая до).
//! Правка трогает **проверку** представления, а не печать, и код существующих
//! замыканий ею не двигается по построению. Наносекунда здесь стоит рядом
//! основанием пары: `apply-word` есть тот самый горячий путь, и он тут для
//! того, чтобы разность с ним было от чего считать.
//!
//! *Второй - чего стоит новая возможность и чего стоила бы отвергнутая.*
//! Развилка (б) вопроса 189 - «массив кладётся в коробку на входе в замыкание
//! и достаётся на выходе». Компилятор её не делает, поэтому написана она в
//! самой нагрузке: конструктор с одним полем и разбор, то есть ровно то, во
//! что (б) боксировала бы. Разность пары и есть её цена.
//!
//! # Методика
//!
//! Та же, что у `benches/crossing.rs`, и намеренно: нагрузки ходят **парами**,
//! внутри пары различается одна вещь, всё прочее совпадает буква в букву - та
//! же рекуррентность `acc := 3·acc + v`, тот же цикл, то же чужое число
//! витков. Замыкание заводится **до** цикла: мерится применение, а не сборка
//! среды.
//!
//! Число витков приходит из окружения через чужой вызов (`adamas_bench_calls`,
//! `benches/crossing/probe.c`), а не литералом: у прозрачного числа компилятор
//! вправе посчитать цикл на сборке. Спутник взят у стенда пересечения, а не
//! скопирован: символ тот же, и вторая копия разъехалась бы молча.
//!
//! Наносекунда на виток - разность с полом, то есть с тем же бинарём при нуле
//! витков; оценка обеих величин - пол выборки (`harness::least`), как во всех
//! стендах крейта.
//!
//! # Что измерено (2026-09-21, три прогона)
//!
//! Ячейки кучи - величина точная и от шума не зависящая, поэтому стоят первыми.
//! Витков 20 000 000.
//!
//! | Нагрузка | Ячеек всего | На виток |
//! |---|---|---|
//! | `apply-word` | 80 000 005 | 4 |
//! | `apply-array` | 60 000 006 | **3** |
//! | `apply-boxed` | 80 000 006 | 4 |
//! | `capture-array` | 40 000 006 | 2 |
//! | `capture-boxed` | 40 000 007 | 2 |
//!
//! Взятая развилка не стоит **ни одной** ячейки: массив едет указателем, как и
//! ехал. Развилка (б) в аргументе возвращает ровно ячейку на пересечение - ту,
//! которую трек A волны 1 отверг замером. В среде она стоит **одной ячейки на
//! всю программу**: коробка там собирается раз, и седьмая цифра у
//! `capture-boxed` - это она.
//!
//! Побочно и неожиданно: **слово аргументом дороже массива** - четыре ячейки
//! против трёх. Это решение 158 («граница боксирует») в работе: плоский скаляр
//! на пересечении заворачивается, а массив нет.
//!
//! Наносекунды. Три прогона; второй шёл на занятой машине, и уровень у него
//! выше на треть у **всех** точек разом - читать поэтому надо разности, а не
//! уровни.
//!
//! | Нагрузка | C | LLVM |
//! |---|---|---|
//! | `apply-word` | 49.46 / 67.90 / 48.99 | 45.38 / 64.27 / 44.14 |
//! | `apply-array` | 52.17 / 68.53 / 50.19 | 38.93 / 54.71 / 38.33 |
//! | `apply-boxed` | 55.51 / 74.99 / 55.14 | 48.18 / 63.96 / 47.64 |
//! | `capture-array` | 32.89 / 44.98 / 32.97 | 22.71 / 31.12 / 22.22 |
//! | `capture-boxed` | 31.62 / 43.50 / 31.33 | 23.70 / 32.82 / 23.64 |
//!
//! | Пара | C | LLVM |
//! |---|---|---|
//! | коробка (б) против массива, аргумент | **3.34 / 6.47 / 4.95** | **9.25 / 9.25 / 9.31** |
//! | коробка (б) против массива, среда | −1.28 / −1.48 / −1.64 | 1.00 / 1.70 / 1.43 |
//! | массив против слова, аргумент | 2.71 / 0.63 / 1.20 | −6.44 / −9.56 / −5.81 |
//!
//! Читается это так.
//!
//! - **(б) в аргументе стоит наносекунд, и стоит их у обоих понижений.** У
//!   LLVM разность воспроизводится до сотых (9.25 / 9.25 / 9.31), у C гуляет
//!   вчетверо шире, но знака не меняет ни разу. Это цена ячейки на пересечение
//!   и ничего сверх: работа у пары одна и та же.
//! - **(б) в среде не стоит ничего.** Разность меняет знак между понижениями и
//!   лежит внутри разброса: коробка там собирается один раз, а разбор её -
//!   загрузка поля рядом с той же загрузкой ячейки.
//! - **Массив в аргументе дешевле слова у LLVM и вровень у C.** Знак
//!   устойчивый, и объясняется он строкой ячеек: у слова четыре, у массива три.
//!   То есть буфер через границу замыкания сегодня едет **дешевле**, чем
//!   `Int64`.
//!
//! Таблица заполняется прогоном (`cargo bench -p adamas-codegen --bench
//! closure`), и числа из него переписываются сюда руками - как во всех стендах
//! крейта.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

mod harness;

use std::path::{Path, PathBuf};
use std::process::Command;

use criterion::{Criterion, SamplingMode, criterion_group};

use adamas_codegen::llvm::{Pipeline, Toolchain};

use harness::{
    RELEASE, blocks, by_floor, elaborated, entry, least, measuring, runtime, runtime_bitcode,
    scratch,
};

const STAND: &str = "bench-closure";

/// Переменная, которой стенд говорит программе число витков.
const CALLS_VARIABLE: &str = "ADAMAS_BENCH_CALLS";

/// Внешних витков в замере. Всего их [`BLOCK`] раз столько.
const CALLS: u64 = 20_000;

/// Витков во внутреннем цикле - то же число, что литерал `block` в нагрузках.
///
/// Цикл двойной, и **был** вынужден: применение замыкания печатало
/// `adamas_kont` на кадре, у которого берётся адрес, и сишный компилятор
/// хвостовой вызов из-за этого не сворачивал - 100 000 витков проходили,
/// 200 000 роняли процесс сигналом 11. Трек C волны 4 Фазы 8 снял это
/// приставкой `musttail` на самохвостовом вызове (§6, §10 вопрос 192): та же
/// нагрузка берёт теперь 10⁸ витков одним циклом при стеке 2 MiB.
///
/// Двойным цикл остаётся **ради сравнимости**: числа волны 3 мерены на нём, и
/// сменив форму, стенд потерял бы базис. Цена формы названа и она ноль -
/// внешний виток один на тысячу внутренних.
///
/// Число написано в двух местах - здесь и литералом `block` в каждой
/// нагрузке, - и разъехавшись, они дали бы нс/виток, делённые не на то.
/// Сторожит совпадение [`the_block_matches_the_loads`].
const BLOCK: u64 = 1_000;

/// Прогонов на точку вне criterion: оценка полом требует выборки.
const RUNS: u64 = 5;

/// Нагрузки: имя и исходник.
const LOADS: [(&str, &str); 5] = [
    ("apply-word", include_str!("closure/apply-word.adamas")),
    ("apply-array", include_str!("closure/apply-array.adamas")),
    ("apply-boxed", include_str!("closure/apply-boxed.adamas")),
    (
        "capture-array",
        include_str!("closure/capture-array.adamas"),
    ),
    (
        "capture-boxed",
        include_str!("closure/capture-boxed.adamas"),
    ),
];

/// Пары «дороже - дешевле»: из их разности и читается цена.
///
/// Первая мерит, чего стоит буфер в аргументе замыкания против слова там же.
/// Вторая и третья мерят **отвергнутую** развилку (б) в обеих позициях: в
/// аргументе она боксирует на каждое пересечение, в среде - один раз, но
/// разворачивает на каждом применении.
const PAIRS: [(&str, &str); 3] = [
    ("apply-array", "apply-word"),
    ("apply-boxed", "apply-array"),
    ("capture-boxed", "capture-array"),
];

/// Ответы внутри пары обязаны совпадать: разойдись они - мерили бы не границу.
///
/// Между парами они тоже совпадают, и это не случайность: рекуррентность одна
/// на все пять нагрузок. Сверяются поэтому все пятеро разом.
fn agreeing(answers: &[(String, String)]) {
    let (first, want) = answers[0].clone();
    for (who, got) in &answers[1..] {
        assert_eq!(got, &want, "{who} ответил не то, что {first}");
    }
}

/// Зовёт компилятор и роняет стенд его же выводом.
fn run(command: &mut Command, what: &str) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{what}: не собралось\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Чужая единица со счётчиком витков - та же, что у стенда пересечения.
///
/// Копии нет намеренно: символ один и тот же, и разъехавшись, копия дала бы
/// двум стендам разное число витков при одинаковой переменной окружения.
fn probe(dir: &Path) -> PathBuf {
    let object = dir.join("probe.o");
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(["-std=c11", "-O2", "-w"])
            .arg("-c")
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/crossing/probe.c"))
            .arg("-o")
            .arg(&object),
        "probe.c",
    );
    object
}

/// Порождённый C, собранный со спутником.
fn in_c(dir: &Path, name: &str, source: &str) -> PathBuf {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = entry(&signature);
    let made = adamas_elab::mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана проходить");
    let text = adamas_codegen::compile(&signature, &made.term).expect("понижение обязано брать");
    let path = dir.join(format!("c-{name}.c"));
    let binary = dir.join(format!("c-{name}"));
    std::fs::write(&path, &text).unwrap();
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(RELEASE)
            .args(["-fwrapv", "-ffp-contract=off", "-fno-builtin", "-w"])
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(&path)
            .args(runtime(dir))
            .arg(probe(dir))
            .arg("-o")
            .arg(&binary),
        &format!("c-{name}"),
    );
    binary
}

/// Он же понижением в текстовый `.ll`.
fn in_llvm(dir: &Path, tools: &Toolchain, name: &str, source: &str) -> PathBuf {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = entry(&signature);
    let made = adamas_elab::mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана проходить");
    let artefacts =
        adamas_codegen::compile_llvm(&signature, &made.term).expect("понижение обязано брать");

    let stem = format!("ll-{name}");
    let text = dir.join(format!("{stem}.ll"));
    std::fs::write(&text, &artefacts.ll).unwrap();
    let object = Pipeline::whole_program(&runtime_bitcode(tools, dir))
        .run(tools, &text, &stem)
        .unwrap_or_else(|error| panic!("{stem}: конвейер LLVM отказал: {error}"));

    let support = dir.join(format!("{stem}.support.c"));
    let compiled = dir.join(format!("{stem}.support.o"));
    std::fs::write(&support, &artefacts.support).unwrap();
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(RELEASE)
            .args(["-w", "-c"])
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(&support)
            .arg("-o")
            .arg(&compiled),
        &format!("спутник {stem}"),
    );

    let binary = dir.join(&stem);
    run(
        Command::new(env!("ADAMAS_CC"))
            .arg(&object)
            .arg(&compiled)
            .arg(probe(dir))
            .args(RELEASE)
            .arg("-o")
            .arg(&binary),
        &format!("линковка {stem}"),
    );
    binary
}

/// Прогон с названным числом витков: ответ, «выдано», «живо».
fn ran(binary: &Path, calls: u64) -> (String, usize, usize) {
    let output = Command::new(binary)
        .env(CALLS_VARIABLE, calls.to_string())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}: прогон оборвался: {}",
        binary.display(),
        output.status
    );
    let stderr = String::from_utf8(output.stderr).unwrap();
    let (allocated, live) = blocks(&stderr);
    let answer = String::from_utf8(output.stdout).unwrap();
    (answer.trim_end().to_owned(), allocated, live)
}

/// Собранная нагрузка и то, что о ней известно до замера.
struct Load {
    name: &'static str,
    side: &'static str,
    binary: PathBuf,
    allocated: usize,
}

/// Стенд целиком: все нагрузки обоих понижений, сверенные до замера.
struct Stand {
    calls: u64,
    loads: Vec<Load>,
}

fn stand() -> Stand {
    the_block_matches_the_loads();
    let dir = scratch(STAND);
    let calls = if measuring() { CALLS } else { 1 };

    let mut loads = Vec::new();
    let mut answers: Vec<(String, String)> = Vec::new();
    for (name, source) in LOADS {
        let binary = in_c(&dir, name, source);
        let (answer, allocated, live) = ran(&binary, calls);
        assert_eq!(live, 0, "{name}/c: прогон оставил блоки живыми");
        answers.push((format!("{name}/c"), answer));
        loads.push(Load {
            name,
            side: "c",
            binary,
            allocated,
        });
    }
    if let Some(tools) = harness::llvm_tools() {
        for (name, source) in LOADS {
            let binary = in_llvm(&dir, &tools, name, source);
            let (answer, allocated, live) = ran(&binary, calls);
            assert_eq!(live, 0, "{name}/llvm: прогон оставил блоки живыми");
            answers.push((format!("{name}/llvm"), answer));
            loads.push(Load {
                name,
                side: "llvm",
                binary,
                allocated,
            });
        }
    }
    agreeing(&answers);

    Stand { calls, loads }
}

/// Наносекунда на виток: разность с полом, делённая на число витков.
///
/// Витков `calls * BLOCK`: внешний цикл крутит внутренний, и мерится
/// применение замыкания, которое стоит во внутреннем.
fn per_turn(binary: &Path, calls: u64) -> f64 {
    let full = least(RUNS, || drop(ran(binary, calls)));
    let floor = least(RUNS, || drop(ran(binary, 0)));
    let span = full.saturating_sub(floor);
    #[allow(
        clippy::cast_precision_loss,
        reason = "число витков до 2^53 не доходит"
    )]
    let turns = (calls * BLOCK) as f64;
    span.as_secs_f64() * 1e9 / turns
}

/// Литерал `block` в нагрузках обязан совпасть с [`BLOCK`].
///
/// Написан он в двух местах по необходимости: в программе на Adamas
/// константы из Rust не подставить, а делить стенд обязан на то же число.
/// Разъедься они - нс/виток соврал бы ровно во столько раз, и молча.
fn the_block_matches_the_loads() {
    let written = format!("block = {BLOCK}");
    for (name, source) in LOADS {
        assert!(
            source.contains(&written),
            "{name}: `{written}` в нагрузке не написано - делитель стенда разошёлся с циклом"
        );
    }
}

/// Таблица стенда и цены, посчитанные из неё.
fn table(it: &Stand) {
    eprintln!("нагрузка        понижение   ячеек всего   нс/виток");
    let mut measured: Vec<(&str, &str, f64)> = Vec::new();
    for load in &it.loads {
        let nanoseconds = per_turn(&load.binary, it.calls);
        eprintln!(
            "{:<15} {:<11} {:>11}   {nanoseconds:>8.3}",
            load.name, load.side, load.allocated
        );
        measured.push((load.name, load.side, nanoseconds));
    }
    for side in ["c", "llvm"] {
        let at = |what: &str| {
            measured
                .iter()
                .find(|(name, which, _)| *name == what && *which == side)
                .map(|(_, _, it)| *it)
        };
        for (dearer, cheaper) in PAIRS {
            if let (Some(more), Some(less)) = (at(dearer), at(cheaper)) {
                eprintln!(
                    "{side}/{dearer} против {cheaper}: {:.3} нс сверх витка",
                    more - less
                );
            }
        }
    }
}

fn closure(criterion: &mut Criterion) {
    let it = stand();
    let mut group = criterion.benchmark_group("closure");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    for load in &it.loads {
        let binary = load.binary.clone();
        let calls = it.calls;
        group.bench_function(format!("{}/{}", load.name, load.side), |bencher| {
            by_floor(bencher, || drop(ran(&binary, calls)));
        });
    }
    group.finish();
    if measuring() {
        table(&it);
    }
}

criterion_group!(benches, closure);

fn main() {
    benches();
    Criterion::default().configure_from_args().final_summary();
}

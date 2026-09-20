//! Стенд пересечения границы **через настоящий узел** (§5.3, §6, трек D волны 1
//! Фазы 8).
//!
//! # Чем он отличается от `benches/foreign.rs`
//!
//! Трек A измерил цену **уклада**: четыре представления чужого указателя,
//! написанные руками на C и на `.ll`, и разность между ними. Узла IR под
//! внешний вызов тогда не было вовсе, поэтому граница его доказанного названа
//! прямо: «уклады не проходили через `emit_c.rs` и `emit_llvm.rs`». Здесь она
//! закрывается - нагрузка есть программа на Adamas, и пересечение печатает
//! эмиттер из `Expr::Foreign`.
//!
//! Мерится поэтому другая величина: не «сколько стоит представление», а
//! «сколько стоит вызов». Первая, по треку A, неотличима от нуля; вторая и есть
//! строка §6 «Direct C FFI overhead».
//!
//! # Методика
//!
//! Программы ходят **парами**, и внутри пары они отличаются одной строкой -
//! телом витка. Там чужая функция, здесь своя арифметика с теми же
//! константами; всё прочее совпадает буква в букву - та же метка, тот же
//! хендлер, то же чужое число витков. Разность двух прогонов, делённая на число
//! витков, есть цена пересечения и ничего сверх.
//!
//! Пар две, и вторая заведена **замером первой**. У тела с умножением цепочка
//! зависимости по данным в три такта, и вызов прячется в её тени целиком:
//! разность там ноль, и ноль этот - свойство тела, а не границы. Лёгкая пара
//! (поворот на бит, один такт) прятать вызов не умеет, и цена его видна.
//!
//! # Что измерено (2026-09-20, три прогона)
//!
//! | Пара | Понижение | нс/виток снаружи | нс/виток внутри | разность |
//! |---|---|---|---|---|
//! | тяжёлая | C | 1.015 / 1.086 / 1.037 | 0.985 / 0.999 / 1.040 | **0.03 / 0.09 / −0.00** |
//! | тяжёлая | LLVM | 1.001 / 1.056 / 1.047 | 0.974 / 1.027 / 1.070 | **0.03 / 0.03 / −0.02** |
//! | лёгкая | C | 0.900 / 0.964 / 0.927 | 0.625 / 0.677 / 0.673 | **0.28 / 0.29 / 0.25** |
//! | лёгкая | LLVM | 0.524 / 0.569 / 0.534 | 0.439 / 0.456 / 0.463 | **0.09 / 0.11 / 0.07** |
//!
//! Читается это так. Пересечение **само по себе** стоит 0.28 нс у C-понижения и
//! 0.09 нс у LLVM-понижения - меньше такта в обоих случаях. На теле с
//! зависимостью по данным оно не стоит **ничего**: разность меняет знак между
//! прогонами, то есть лежит внутри разброса.
//!
//! # Цена займа, третья пара (2026-09-20, трек A волны 2, три прогона)
//!
//! Третья пара мерит не пересечение, а **заём буфера** (§5.3): обе её половины
//! ходят за границу, зовут один и тот же символ той же арностью и с тем же
//! телом, и различаются ровно тем, откуда берётся первое слово - из адреса
//! нагрузки нашего массива либо из константы.
//!
//! | Понижение | нс/виток с займом | нс/виток словом | разность |
//! |---|---|---|---|
//! | C | 2.015 / 1.961 / 1.990 | 0.950 / 0.899 / 0.923 | **1.065 / 1.062 / 1.067** |
//! | LLVM | 0.978 / 0.978 / 0.978 | 0.529 / 0.463 / 0.489 | **0.449 / 0.515 / 0.489** |
//!
//! Заём, стало быть, стоит **дороже самого пересечения** - вчетверо у C, впятеро
//! у LLVM, - и это не изъян, а состав: в разность входят вызов
//! `adamas_array_data` и **пара `dup`/`drop`**, которой массив держится живым до
//! возврата. Пара эта - цена случая, где массив нужен и после займа; у массива,
//! чьё последнее употребление и есть заём, её нет вовсе (`tests/ownership.rs`
//! показывает на одну лишнюю ссылку при пяти займах). Здесь взят дорогой
//! случай нарочно: виток называет массив дважды, поэтому мерится верхняя
//! граница, а не удобная.
//!
//! Ячеек при этом выдано **пять против четырёх**: массив заводится один раз на
//! прогон, а не на виток. Заём кучи не трогает вовсе - это вычисление адреса.
//!
//! Число трека A (~0.7 нс) больше не потому, что стенды разошлись, а потому,
//! что мерили разное: его точка разложения за границу не ходила **и работы не
//! делала**, поэтому в 0.7 нс вошла и сама арифметика чужой функции. Здесь
//! работа стоит по обе стороны одна и та же, и остаётся ровно граница.
//!
//! *Число витков приходит из окружения через чужой вызов*
//! (`adamas_bench_calls`), а не литералом в программе: у точки разложения тело
//! витка прозрачно, и литерал дал бы компилятору право посчитать её целиком на
//! сборке. Цена - одно лишнее пересечение на прогон.
//!
//! *Чужая единица трансляции собирается без `-flto`*: настоящая библиотека
//! лежит отдельным объектом. Тот же выбор и тот же довод, что у трека A.
//!
//! *Наносекунда на виток - разность с полом.* Пол есть тот же бинарь с нулём
//! витков, то есть цена запуска процесса; оценка обеих величин - пол выборки
//! (`harness::least`), как во всех стендах крейта.
//!
//! *Ответы внутри пары сверяются до первой наносекунды.* Обе программы пары
//! считают одну и ту же рекуррентность обоими понижениями, и разойдись они -
//! мерить было бы нечего. Между парами ответы разные по построению.

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

const STAND: &str = "bench-crossing";

/// Переменная, которой стенд говорит программе число витков.
const CALLS_VARIABLE: &str = "ADAMAS_BENCH_CALLS";

/// Витков в замере.
///
/// Двадцать миллионов - столько же, сколько у трека A: пересечение стоит
/// единицы наносекунд, и при меньшем числе разность с полом тонула бы в цене
/// запуска процесса.
const CALLS: u64 = 20_000_000;

/// Прогонов на точку вне criterion: оценка полом требует выборки.
const RUNS: u64 = 5;

/// Нагрузки: имя и исходник.
///
/// Пар две, и вторая нужна ровно потому, что первая отвечает нулём. У тела с
/// умножением цепочка зависимости по данным в три такта, и вызов прячется в её
/// тени целиком; у тела с поворотом она однотактная, и цена вызова видна.
/// Первая пара говорит, чего пересечение стоит **на настоящем теле**, вторая -
/// чего оно стоит само по себе.
const LOADS: [(&str, &str); 6] = [
    ("outward", include_str!("crossing/outward.adamas")),
    ("inward", include_str!("crossing/inward.adamas")),
    ("outward-lean", include_str!("crossing/outward-lean.adamas")),
    ("inward-lean", include_str!("crossing/inward-lean.adamas")),
    ("outward-lend", include_str!("crossing/outward-lend.adamas")),
    ("outward-word", include_str!("crossing/outward-word.adamas")),
];

/// Пары «за границу - на месте»: из их разности и считается строка §6.
///
/// Третья пара мерит другое и потому обе её половины ходят **за границу**:
/// разность там есть цена **займа** (адрес нагрузки плюс пара счётчика), а не
/// цена пересечения. Символ у обеих половин один и тот же, арность та же,
/// тело то же - различается только то, откуда берётся первое слово.
const PAIRS: [(&str, &str); 3] = [
    ("outward", "inward"),
    ("outward-lean", "inward-lean"),
    ("outward-lend", "outward-word"),
];

/// Зовёт компилятор и роняет стенд его же выводом.
fn run(command: &mut Command, what: &str) {
    let output = command.output().unwrap();
    assert!(
        output.status.success(),
        "{what}: не собралось\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Чужая библиотека объектником **без** межмодульной оптимизации.
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

/// Порождённый C, собранный с чужой библиотекой.
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
///
/// Конвейер - [`Pipeline::whole_program`], то есть рантайм приезжает битовым
/// кодом до `opt -O2`: этим LLVM-сторона уравнивается с C-стороной, у которой
/// то же делает `-flto`. Чужая библиотека остаётся отдельным объектом у обеих.
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

/// Стенд целиком: обе нагрузки обоих понижений, сверенные до замера.
struct Stand {
    calls: u64,
    loads: Vec<Load>,
}

fn stand() -> Stand {
    let dir = scratch(STAND);
    let calls = if measuring() { CALLS } else { 1_000 };

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

    // Внутри пары обе нагрузки считают **одну** рекуррентность, и оба
    // понижения считают её одинаково. Разойдись что-нибудь - разность мерила бы
    // не границу, а разные программы. Между парами ответы разные по построению,
    // и сверять их нечем.
    let at = |what: &str| -> Vec<(String, String)> {
        answers
            .iter()
            .filter(|(who, _)| who.starts_with(&format!("{what}/")))
            .cloned()
            .collect()
    };
    for (outward, inward) in PAIRS {
        let found: Vec<(String, String)> = at(outward).into_iter().chain(at(inward)).collect();
        let (first, want) = found[0].clone();
        for (who, got) in &found[1..] {
            assert_eq!(got, &want, "{who} ответил не то, что {first}");
        }
    }

    Stand { calls, loads }
}

/// Наносекунда на виток: разность с полом, делённая на число витков.
fn per_turn(binary: &Path, calls: u64) -> f64 {
    let full = least(RUNS, || drop(ran(binary, calls)));
    let floor = least(RUNS, || drop(ran(binary, 0)));
    let span = full.saturating_sub(floor);
    #[allow(
        clippy::cast_precision_loss,
        reason = "число витков до 2^53 не доходит"
    )]
    let calls = calls as f64;
    span.as_secs_f64() * 1e9 / calls
}

/// Таблица стенда и строка §6, посчитанная из неё.
fn table(it: &Stand) {
    eprintln!("нагрузка       понижение   ячеек всего   нс/виток");
    let mut measured: Vec<(&str, &str, f64)> = Vec::new();
    for load in &it.loads {
        let nanoseconds = per_turn(&load.binary, it.calls);
        eprintln!(
            "{:<14} {:<11} {:>11}   {nanoseconds:>8.3}",
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
        for (outward, inward) in PAIRS {
            if let (Some(crossed), Some(kept)) = (at(outward), at(inward)) {
                eprintln!(
                    "{side}/{outward}: пересечение стоит {:.3} нс сверх витка",
                    crossed - kept
                );
            }
        }
    }
}

fn crossing(criterion: &mut Criterion) {
    let it = stand();
    let mut group = criterion.benchmark_group("crossing");
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

criterion_group!(benches, crossing);

fn main() {
    benches();
    Criterion::default().configure_from_args().final_summary();
}

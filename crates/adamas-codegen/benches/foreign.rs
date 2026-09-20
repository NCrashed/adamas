//! Стенд границы Adamas↔C: чего стоит уклад чужого указателя (трек A волны 1
//! Фазы 8, §5.3).
//!
//! Мерит он одно - **представление**, а не FFI целиком: тривиальная сишная
//! функция зовётся в цикле, и между вызовами лежит ровно то, чем уклад
//! отличается от соседа. Сама чужая функция у всех укладов одна и та же
//! (`boundary/probe.c`), поэтому разность двух столбцов есть цена уклада, а не
//! цена вызова.
//!
//! # Уклады
//!
//! Четыре, хотя развилок в плане три: (а) распадается надвое, и цена у половин
//! разная в разы.
//!
//! | Имя | Развилка | Что делает |
//! |---|---|---|
//! | `boxed` | (а) | однополевой объект под RC **на каждое пересечение** |
//! | `held` | (а) | коробка одна на прогон - идиома `resource` |
//! | `imm` | (б) | сдвинутое непосредственное `(p << 1) \| 1` |
//! | `flat` | (в) | плоское слово, `adamas_value` не становящееся |
//!
//! # Методика
//!
//! Общая с `native.rs`, разделом «Методика», и здесь только то, чем стенд от
//! него отличается.
//!
//! *Число вызовов приходит аргументом процесса.* Константа дала бы компилятору
//! право развернуть цикл и посчитать его целиком, и стенд померил бы
//! свёртывание.
//!
//! *Чужая единица трансляции собирается **без** `-flto`* - потому что
//! настоящая чужая библиотека лежит отдельным объектом. Ожидание «иначе
//! померили бы инлайнинг» проверено и не подтвердилось: с `-flto` у той же
//! единицы числа те же внутри разброса (`boundary/probe.c`, шапка). Флаг снят
//! ради верности модели, а не ради числа.
//!
//! *Наносекунда на вызов - разность с полом.* Пол есть тот же бинарь с нулём
//! вызовов, то есть цена запуска процесса; вычитается она, а не берётся на
//! глаз. Оценка обеих величин - **пол выборки** (`harness::least`), как и во
//! всех стендах этого крейта.
//!
//! *Ячейки считает рантайм, а не стенд.* Чужая библиотека берёт свою память
//! `malloc`'ом мимо счётчика (`boundary/probe.c`), поэтому «блоков выдано» -
//! ровно те ячейки, что выдал уклад.
//!
//! Свидетель ответа и счётчиков живёт отдельно
//! (`crates/adamas-codegen/tests/foreign.rs`) и там же держит таблицу мутантов;
//! стенд сверяет обе величины до всякого замера, потому что мерить разошедшиеся
//! стороны нечего.

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

use harness::{RELEASE, blocks, by_floor, least, measuring, runtime, runtime_bitcode, scratch};

const STAND: &str = "bench-foreign";

/// Пересечений границы в замере.
///
/// Двадцать миллионов: у самого дешёвого уклада вызов стоит доли наносекунды, и
/// при меньшем числе разность с полом тонула бы в цене запуска процесса
/// (порядка полутора миллисекунд).
const CALLS: u64 = 20_000_000;

/// Прогонов на точку вне criterion: оценка полом требует выборки.
const RUNS: u64 = 5;

/// Уклады: имя, номер для `-DSHAPE=` и есть ли у него текстовый `.ll`.
///
/// `held` - половина развилки (а), и отдельного `.ll` ему не писано: выразимость
/// (а) предъявляет `boxed`, а отличается `held` от него местом одной строки.
const SHAPES: [(&str, u32, bool); 4] = [
    ("boxed", 1, true),
    ("held", 2, false),
    ("imm", 3, true),
    ("flat", 4, true),
];

/// Точка разложения: тот же цикл, за границу не ходящий.
///
/// Не уклад и в сверку ответов не входит - ответ у неё другой по построению.
/// Нужна она одному: разность с самым дешёвым укладом называет, какая доля
/// наносекунды принадлежит непрозрачному вызову, а какая представлению. Без
/// неё «0.9 нс на пересечение» читалось бы как цена уклада, хотя укладу из них
/// не принадлежит почти ничего.
const DECOMPOSITION: (&str, u32) = ("none", 5);

/// Исходники стенда.
fn boundary() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/boundary")
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

/// Чужая библиотека объектником **без** межмодульной оптимизации.
///
/// Без `-flto` не по недосмотру: прозрачная чужая функция свернулась бы в тело
/// цикла, и стенд померил бы инлайнинг вместо границы.
fn probe(dir: &Path) -> PathBuf {
    let object = dir.join("probe.o");
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(["-std=c11", "-O2", "-w"])
            .arg("-c")
            .arg(boundary().join("probe.c"))
            .arg("-o")
            .arg(&object),
        "probe.c",
    );
    object
}

/// Точка входа: общая обоим понижениям, собирается строкой замера.
fn entry(dir: &Path) -> PathBuf {
    let object = dir.join("main.o");
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(RELEASE)
            .args(["-fwrapv", "-ffp-contract=off", "-w"])
            .arg("-c")
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(boundary().join("main.c"))
            .arg("-o")
            .arg(&object),
        "main.c",
    );
    object
}

/// Линкует уклад с чужой библиотекой, точкой входа и, если просят, рантаймом.
///
/// Рантайм прикладывается объектниками только там, где конвейер не принёс его
/// битовым кодом: приложи дважды - и компоновщик отвергнет программу
/// дублирующимися определениями.
fn linked(dir: &Path, stem: &str, object: &Path, with_runtime: bool) -> PathBuf {
    let binary = dir.join(stem);
    let mut link = Command::new(env!("ADAMAS_CC"));
    link.arg(object).arg(entry(dir)).arg(probe(dir));
    if with_runtime {
        link.args(runtime(dir));
    }
    run(
        link.args(RELEASE).arg("-o").arg(&binary),
        &format!("линковка {stem}"),
    );
    binary
}

/// Уклад, понижённый в C.
fn in_c(dir: &Path, name: &str, shape: u32) -> PathBuf {
    let object = dir.join(format!("c-{name}.o"));
    run(
        Command::new(env!("ADAMAS_CC"))
            .args(RELEASE)
            .args(["-fwrapv", "-ffp-contract=off", "-w"])
            .arg(format!("-DSHAPE={shape}"))
            .arg("-c")
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(boundary().join("entry.c"))
            .arg("-o")
            .arg(&object),
        name,
    );
    linked(dir, &format!("c-{name}"), &object, true)
}

/// Уклад, понижённый в текстовый `.ll`.
///
/// Конвейер - [`Pipeline::whole_program`], то есть рантайм приезжает **битовым
/// кодом до** `opt -O2`. Этим LLVM-сторона уравнивается с C-стороной, у которой
/// то же делает `-flto`: без уравнивания столбец мерил бы межмодульную
/// оптимизацию, а не бэкенд (замер трека A Фазы 7).
fn in_llvm(dir: &Path, tools: &Toolchain, name: &str) -> PathBuf {
    let stem = format!("ll-{name}");
    let text = dir.join(format!("{stem}.ll"));
    std::fs::copy(boundary().join(format!("{name}.ll")), &text).unwrap();
    let object = Pipeline::whole_program(&runtime_bitcode(tools, dir))
        .run(tools, &text, &stem)
        .unwrap_or_else(|error| panic!("{stem}: конвейер LLVM отказал: {error}"));
    linked(dir, &stem, &object, false)
}

/// Прогон уклада: ответ, «выдано», «живо».
fn ran(binary: &Path, calls: u64) -> (String, usize, usize) {
    let output = Command::new(binary)
        .arg(calls.to_string())
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

/// Собранный уклад и то, что о нём известно до замера.
struct Shape {
    name: &'static str,
    side: &'static str,
    binary: PathBuf,
    allocated: usize,
}

impl Shape {
    fn measured(
        name: &'static str,
        side: &'static str,
        binary: PathBuf,
        calls: u64,
    ) -> (Self, String) {
        let (answer, allocated, live) = ran(&binary, calls);
        assert_eq!(live, 0, "{name}/{side}: прогон оставил блоки живыми");
        (
            Self {
                name,
                side,
                binary,
                allocated,
            },
            answer,
        )
    }
}

/// Стенд целиком: уклады обоих понижений, сверенные до замера.
struct Stand {
    calls: u64,
    c: Vec<Shape>,
    llvm: Vec<Shape>,
}

/// Собирает и сверяет. Мерить разошедшиеся стороны нечего, поэтому сверка идёт
/// **до** первой наносекунды.
fn stand() -> Stand {
    let dir = scratch(STAND);
    let calls = if measuring() { CALLS } else { 1_000 };

    let mut c = Vec::new();
    let mut answers = Vec::new();
    for (name, shape, _) in SHAPES {
        let (built, answer) = Shape::measured(name, "c", in_c(&dir, name, shape), calls);
        answers.push((name, answer));
        c.push(built);
    }
    let (first, want) = answers[0].clone();
    for (name, got) in &answers[1..] {
        assert_eq!(got, &want, "{name} ответил не то, что {first}");
    }

    // Точка разложения идёт **после** сверки и в неё не входит: ответ у неё
    // другой по построению, и включи её в сверку - стенд отверг бы сам себя.
    let (name, shape) = DECOMPOSITION;
    let (floor, floor_answer) = Shape::measured(name, "c", in_c(&dir, name, shape), calls);
    assert_ne!(
        floor_answer, want,
        "точка разложения ответила как уклад: за границу она ходить не должна"
    );
    assert_eq!(floor.allocated, 0, "точка разложения выдала ячейку");
    c.push(floor);

    let mut llvm = Vec::new();
    if let Some(tools) = harness::llvm_tools() {
        for (name, _, lowered) in SHAPES {
            if !lowered {
                continue;
            }
            let (built, answer) = Shape::measured(name, "llvm", in_llvm(&dir, &tools, name), calls);
            assert_eq!(answer, want, "{name}: понижения ответили разное");
            let same = c.iter().find(|it| it.name == name).unwrap();
            assert_eq!(
                built.allocated, same.allocated,
                "{name}: понижения выдали разное число ячеек"
            );
            llvm.push(built);
        }
    }

    Stand { calls, c, llvm }
}

/// Наносекунда на пересечение: разность с полом, делённая на число вызовов.
fn per_call(binary: &Path, calls: u64) -> f64 {
    let full = least(RUNS, || drop(ran(binary, calls)));
    let floor = least(RUNS, || drop(ran(binary, 0)));
    let span = full.saturating_sub(floor);
    #[allow(
        clippy::cast_precision_loss,
        reason = "число вызовов до 2^53 не доходит"
    )]
    let calls = calls as f64;
    span.as_secs_f64() * 1e9 / calls
}

/// Таблица трека: ячеек на пересечение и наносекунд на него же.
///
/// Ячейки печатаются и долей, и числом. Доля - та величина, ради которой стенд
/// заведён; число рядом с ней потому, что у уклада `resource` доля есть
/// 1/20 000 000 и в четырёх знаках выглядит нулём, а ноль здесь значит совсем
/// другое.
fn table(it: &Stand) {
    eprintln!("уклад        понижение   ячеек/вызов   ячеек всего   нс/вызов");
    for shape in it.c.iter().chain(&it.llvm) {
        #[allow(
            clippy::cast_precision_loss,
            reason = "счёт ячеек и вызовов до 2^53 не доходит"
        )]
        let cells = shape.allocated as f64 / it.calls as f64;
        eprintln!(
            "{:<12} {:<11} {cells:>11.4}   {:>11}   {:>8.3}",
            shape.name,
            shape.side,
            shape.allocated,
            per_call(&shape.binary, it.calls)
        );
    }
}

fn foreign(criterion: &mut Criterion) {
    let it = stand();
    let mut group = criterion.benchmark_group("foreign");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);
    for shape in it.c.iter().chain(&it.llvm) {
        let binary = shape.binary.clone();
        let calls = it.calls;
        group.bench_function(format!("{}/{}", shape.name, shape.side), |bencher| {
            by_floor(bencher, || drop(ran(&binary, calls)));
        });
    }
    group.finish();
    if measuring() {
        table(&it);
    }
}

criterion_group!(benches, foreign);

fn main() {
    benches();
    Criterion::default().configure_from_args().final_summary();
}

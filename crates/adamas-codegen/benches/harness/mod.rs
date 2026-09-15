//! Общее двум стендам: сборка порождённого C, запуск процессом, пол выборки.
//!
//! Живёт отдельно по той же причине, по какой отдельно живёт
//! `tests/harness/mod.rs`: бенчмарк - свой крейт, а сборка рантайма, строка
//! release и оценка полом нужны обоим. Вторая копия здесь была бы не
//! неудобством, а разъездом: строка сборки [`RELEASE`] стоила **99%** разрыва
//! с соседом (замер 2026-09-13), и стенд, разошедшийся с ней на один флаг,
//! отвечал бы числом, которое ни с чем не сравнивается. Прецедент свежий -
//! список единиц трансляции рантайма лежал в четырёх местах копиями, и новый
//! слой дал «undefined reference» в двух из них.
//!
//! **Методика живёт не здесь**, а в шапке `native.rs`, разделом «Методика».
//! Здесь только её механика; читать надо там.

// Модуль компилируется в каждый стенд целиком, а нужен каждому не весь:
// `paired`-протокол берёт только `native`, соседа-процесс - оба, но с разным
// запросом.
#![allow(dead_code, reason = "общий модуль двух стендов")]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::{Owned, Warnings};

// --- элаборация ----------------------------------------------------------

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
pub(crate) fn elaborated(source: &str) -> (Signature, Metas, Instances) {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect("исходник обязан проходить проверку");
    (signature, metas, instances)
}

/// Тело `main` с подставленными аргументами уровня и row — то, что вычисляет
/// `adamas eval`.
pub(crate) fn entry(signature: &Signature) -> Term {
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

// --- порождённый C -------------------------------------------------------

/// Место под порождённый C и его сборку — своё у каждого стенда.
pub(crate) fn scratch(stand: &str) -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join(stand);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Строка сборки release: уровень оптимизации и межмодульная оптимизация.
///
/// `-O2`, а не `-O1` тестового харнесса: замер говорит о том, что получит
/// пользователь release-сборкой, и уровень оптимизации — часть окружения,
/// которое число обязано нести рядом с собой.
///
/// `-flto` здесь по той же причине и ещё по одной. Порождённый C и рантайм —
/// разные единицы трансляции, а горячий путь состоит из вызовов в рантайм:
/// `adamas_tag`, `adamas_field`, `adamas_dup`, `adamas_drop`. Каждый из них —
/// несколько инструкций, и без межмодульной оптимизации вызов дороже тела.
/// `adamas.h` называет это прямо: «Функции не `static inline`: горячий путь
/// ждёт LTO». Сосед на Rust собирается профилем `release` этого репозитория, а
/// он — `lto = "thin"`; без флага здесь сравнивались бы не два понижения, а
/// собранное межмодульно с собранным по отдельности. Измерено 2026-09-13:
/// флаг снимает **99% разрыва** с соседом (пофазно в процессе на глубине 18:
/// 42.3 мс против 17.7 при 17.6 у соседа).
pub(crate) const RELEASE: [&str; 3] = ["-std=c11", "-O2", "-flto"];

/// Объектные файлы рантайма: собираются однажды на весь прогон.
pub(crate) fn runtime(dir: &Path) -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        // Список приходит от самого рантайма (`build.rs`), а не написан здесь.
        env!("ADAMAS_RUNTIME_UNITS")
            .split(',')
            .map(|name| {
                let object = dir.join(format!("{name}.o"));
                let status = Command::new(env!("ADAMAS_CC"))
                    .args(RELEASE)
                    .arg("-c")
                    .arg("-I")
                    .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                    .arg(sources.join(name))
                    .arg("-o")
                    .arg(&object)
                    .status();
                assert!(
                    status.is_ok_and(|status| status.success()),
                    "рантайм не собрался: {name}"
                );
                object
            })
            .collect()
    })
}

/// Собирает порождённый C в исполняемый файл.
pub(crate) fn built(dir: &Path, name: &str, text: &str) -> PathBuf {
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();
    compiled(dir, &source, &binary);
    binary
}

/// Вызов компилятора C — отдельно, потому что он же и мерится.
pub(crate) fn compiled(dir: &Path, source: &Path, binary: &Path) {
    let output = Command::new(env!("ADAMAS_CC"))
        .args(RELEASE)
        .args(["-fwrapv", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(source)
        .args(runtime(dir))
        .arg("-o")
        .arg(binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "порождённый C не собрался:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Прогон собранной программы: ответ на stdout, счётчики блоков на stderr.
pub(crate) fn ran(binary: &Path) -> (String, String) {
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "прогон оборвался: {}",
        output.status
    );
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// Сколько блоков прогон выдал и сколько оставил живыми.
///
/// Читается из строки счётчиков, которую печатает точка входа. Для FBIP это
/// не украшение отчёта, а свидетель: проход, переписывающий ячейку на месте,
/// от прохода, роняющего её и берущего новую, отличается **здесь**, а не во
/// времени.
pub(crate) fn blocks(stderr: &str) -> (usize, usize) {
    let numbers: Vec<usize> = stderr
        .split_whitespace()
        .filter_map(|word| word.trim_end_matches(',').parse().ok())
        .collect();
    assert_eq!(
        numbers.len(),
        2,
        "счётчики блоков не прочитались из `{}`",
        stderr.trim_end()
    );
    (numbers[0], numbers[1])
}

// --- сосед процессом -----------------------------------------------------

/// Переменная, которой стенд зовёт сам себя дочерним процессом.
///
/// Сосед мерится **тем же протоколом**, что и порождённый C: свежий процесс,
/// свежая куча, ответ на stdout. Иначе его цену задаёт не алгоритм, а то,
/// сколько успел выделить и освободить сам стенд — см. «Методика» в шапке
/// `native.rs`.
pub(crate) const NEIGHBOUR: &str = "ADAMAS_BENCH_NEIGHBOUR";

/// Прогон соседа отдельным процессом: ответ на stdout, свидетель на stderr.
pub(crate) fn ran_neighbour(request: &str) -> (String, String) {
    let executable = std::env::current_exe().expect("стенд знает путь к себе");
    let output = Command::new(executable)
        .env(NEIGHBOUR, request)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "прогон соседа оборвался: {}",
        output.status
    );
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

// --- оценка: пол выборки, а не её среднее --------------------------------

/// Наименьшее время из `runs` запусков.
///
/// Помеха может к времени процесса только **прибавить**: сосед по
/// гиперпотоку, прерывание, вытеснение. Поэтому наименьшее из повторов —
/// оценка того, чего программа стоит без помехи, а среднее — оценка того,
/// сколько помехи досталось окну замера. Измерено 2026-09-13 на `boxed/18`,
/// двенадцать блоков по сорок запусков: минимумы блоков легли в 19.94–20.23
/// (размах 0.29 мс), медианы — в 20.56–21.54 (0.98 мс), максимумы — в
/// 22.30–26.05 (3.75 мс). Хвост шире пола на порядок, и criterion по
/// умолчанию читает именно хвост.
pub(crate) fn least(runs: u64, mut run: impl FnMut()) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..runs {
        let start = Instant::now();
        run();
        best = best.min(start.elapsed());
    }
    best
}

/// Сколько запусков берётся под один пол, сколько бы ни просил criterion.
///
/// На разогреве criterion зовёт замер с одним-двумя повторами, а пол по
/// одному повтору — не пол. Число возвращается помноженным на `iters`, так
/// что планирование criterion остаётся верным: он делит обратно и получает
/// цену одного запуска.
pub(crate) const FLOOR_RUNS: u64 = 8;

/// Точка замера процесса: criterion получает пол, а не среднее.
pub(crate) fn by_floor(bencher: &mut criterion::Bencher<'_>, mut run: impl FnMut()) {
    bencher.iter_custom(|iters| {
        least(iters.max(FLOOR_RUNS), &mut run) * u32::try_from(iters).unwrap_or(u32::MAX)
    });
}

/// Идёт ли настоящий замер, а не проверка собираемости.
///
/// `cargo bench -- --test` в CI и `cargo test --all-targets` локально зовут
/// каждую точку по разу; долгий замер требует тихой машины, а ни разделяемый
/// раннер CI, ни машина под `cargo test` тихими не являются. В этом режиме
/// работа берётся минимальная, пороги не проверяются: проверяется, что код
/// проходит.
///
/// Правило — то же, каким его читает сам criterion: замер идёт, когда есть
/// `--bench` и нет `--test`. Под `cargo test` флага `--bench` не бывает.
pub(crate) fn measuring() -> bool {
    let mut bench = false;
    let mut test = false;
    for argument in std::env::args() {
        bench |= argument == "--bench";
        test |= argument == "--test";
    }
    bench && !test
}

/// Медиана выборки; портит порядок.
pub(crate) fn middle(sample: &mut [f64]) -> f64 {
    sample.sort_unstable_by(f64::total_cmp);
    sample[sample.len() / 2]
}

/// Размах выборки.
pub(crate) fn span(sample: &[f64]) -> f64 {
    let low = sample.iter().copied().fold(f64::MAX, f64::min);
    sample.iter().copied().fold(f64::MIN, f64::max) - low
}

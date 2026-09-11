//! Первый бенчмарк понижения: во что обходится порождённая программа.
//!
//! У понижения замеров не было вовсе (§13, итог 2026-09-11: «native
//! performance не мерил никто»), и §6 оставался непроверенным целиком. Здесь
//! меряется одна его строка — **«символьно-тяжёлый код: паритет с Rust или
//! лучше»**. Взята она потому, что достижима сегодняшним срезом: §6 сам
//! называет символьный workload «цепочками функциональных преобразований над
//! деревьями и списками», а дерево, обход и свёртка — это чистый фрагмент,
//! который понижение берёт.
//!
//! Прочие строки §6 сегодня не меряются, и вот чем:
//!
//! - **Горячие циклы с unboxed numerics** и **zero-alloc циклы с регионами**
//!   требуют цикла, а цикла в языке нет: [`PrimOp`](adamas_core::prim::PrimOp)
//!   знает только `Add`, `Sub`, `Mul`, литеральный паттерн элаборация
//!   отвергает (`Missing::Literal`), и условия выхода из рекурсии по примитиву
//!   не из чего собрать. Счётчик цикла поэтому обязан быть индуктивным, то
//!   есть боксированным, и «unboxed hot loop» не выражается. Мерить нечего до
//!   сравнений и литеральных паттернов.
//! - **`@noalloc`, SIMD, mempool, FFI** — механизмов в понижении нет.
//! - **Плоские контейнеры** есть (§4.11), но хеш-таблицы, против которых
//!   меряется строка, — библиотека, которой нет.
//! - **Бизнес-код с эффектами (1.5–2x Rust)** — вторая форма понижения, трек B
//!   волны 4; шов под неё готов здесь ([`Shape::TailResumptive`]).
//! - **Старт компилятора** мерен у драйвера (`adamas-cli/benches/startup.rs`).
//! - **Время release-сборки** §6 сознательно не ограничивает; она всё равно
//!   мерена ниже как `codegen/cc`, потому что без неё не прочитать, чего стоит
//!   весь путь.
//!
//! # Алгоритм и почему он
//!
//! Двоичное дерево глубины `d`: `grow` строит, `scaled` умножает каждый лист,
//! `total` складывает. Три прохода по 2^d листьям, рекурсия глубиной `d` —
//! стека не хватить не может ни у порождённого C, ни у соседа. Листья
//! **различны** (счётчик по битам пути), поэтому перепутанные поддеревья
//! меняют ответ, а не оставляют его тем же.
//!
//! Счётчик глубины — индуктивный `Nat` длиной `d` (единицы), и его цена в
//! замере не участвует: работа экспоненциальна по `d`, а счётчик линеен.
//!
//! # Кто с кем сравнивается
//!
//! Четверо считают **одно и то же число**, и это проверяется до всякого
//! замера ([`checked`]):
//!
//! - `interp` — машина, то есть `adamas eval`;
//! - `native` — порождённый C, собранный `-O2` и запущенный процессом;
//! - `rust` — тот же алгоритм на Rust, теми же формами данных
//!   (`Box`-рекурсия), в этом же процессе;
//! - `floor` — тот же путь при `d = 0`: цена `fork`/`exec` и печати, которую
//!   `native` платит сверх работы.
//!
//! Сосед на Rust написан **эквивалентным кодом**, как того и требует §6
//! («Rustc на эквивалентном коде»), а не идиоматичным: те же конструкторы, та
//! же владеющая рекурсия, то же заворачивание арифметики. Идиоматичный сосед
//! (массив, цикл) мерил бы отсутствие цикла в языке, а не качество понижения.
//!
//! # Чем проверено, что мерится не пустота
//!
//! Тремя вещами разом. Ответ **печатается** и сверен с машиной — выброси
//! компилятор C вычисление, печатать станет нечего. Точек по глубине три, и
//! шаг глубины удваивает работу: линейному исполнению отвечает удвоение
//! времени. И `floor` показывает, сколько в измеренном не работа, а запуск
//! процесса.
//!
//! # Шов под трек B
//!
//! [`Shape`] — параметр, а не копия файла. `Pure` и `TailResumptive`
//! отличаются одной веткой: множитель приходит операцией `ask` под хвостово
//! резумптивным хендлером, ответ тот же. Машина считает обе формы сегодня;
//! понижение вторую отвергает, и бенчмарк это **называет вслух**, сверяя, что
//! отказ — про хендлер. Появится вторая форма — точка `native/handled`
//! начнёт мериться без правки файла.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{PRINT_DEPTH, Term};
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::mono;
use adamas_elab::{Owned, Warnings};
use criterion::{Criterion, criterion_group, criterion_main};

/// Глубины дерева: шаг удваивает работу, и все четверо считаются на одних и
/// тех же трёх точках.
const DEPTHS: [usize; 3] = [14, 16, 18];

/// Глубина, на которой мерится цена самого понижения.
const CODEGEN_DEPTH: usize = 16;

// --- исходник -----------------------------------------------------------

/// Форма программы: чистый сосед и тот же алгоритм под хендлером.
///
/// Обе считают одно число. Различие ровно одно: откуда `scaled` берёт
/// множитель — из литерала или из операции `ask`, чья ветка зовёт `resume` в
/// хвосте.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// Чистый сосед: множитель написан литералом.
    Pure,
    /// Тот же алгоритм под хвостово резумптивным хендлером.
    TailResumptive,
}

impl Shape {
    /// Имя в идентификаторе точки замера.
    const fn name(self) -> &'static str {
        match self {
            Self::Pure => "pure",
            Self::TailResumptive => "handled",
        }
    }
}

/// Программа: дерево глубины `depth`, построенное, умноженное и свёрнутое.
fn source(shape: Shape, depth: usize) -> String {
    let mut nat = String::new();
    for _ in 0..depth {
        nat.push_str("(Succ ");
    }
    nat.push_str("Zero");
    for _ in 0..depth {
        nat.push(')');
    }

    // Разница форм — три строки: объявление эффекта, row у `scaled` и то,
    // откуда берётся множитель. Остальное общее дословно.
    let (effect, row, factor) = match shape {
        Shape::Pure => ("", "", "3"),
        // `Unit` объявлением эффекта требуется: нульарная операция пишется
        // через него.
        Shape::TailResumptive => (
            "data Unit where\n  MkUnit : Unit\n\neffect Ask where\n  ask : Int64\n",
            "{Ask} ",
            "ask",
        ),
    };
    let entry = match shape {
        Shape::Pure => "main = computed",
        Shape::TailResumptive => {
            "main = handle computed with\n\
             \x20 return v -> v\n\
             \x20 ask -> resume 3"
        }
    };

    format!(
        "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Int64 -> Tree
  Node : Tree -> Tree -> Tree

{effect}
-- Лист получает номер пути в двоичной записи: значения различны, и
-- переставленные поддеревья меняют ответ.
grow : Nat -> Int64 -> Tree
grow Zero seed = Leaf seed
grow (Succ k) seed =
  let doubled : Int64 = mulInt64 seed 2
  Node (grow k doubled) (grow k (addInt64 doubled 1))

scaled : Tree -> {row}Tree
scaled (Leaf x) = Leaf (mulInt64 x {factor})
scaled (Node l r) = Node (scaled l) (scaled r)

total : Tree -> Int64
total (Leaf x) = x
total (Node l r) = addInt64 (total l) (total r)

depth : Nat
depth = {nat}

-- Названо `let`-ом верхнего уровня, а не написано в `handle`: приостановленное
-- вычисление хендлер берёт с написанным типом (§3.4).
computed : {row}Int64
computed = total (scaled (grow depth 1))

main : Int64
{entry}
"
    )
}

// --- машина -------------------------------------------------------------

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
fn elaborated(source: &str) -> (Signature, Metas, Instances) {
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
fn entry(signature: &Signature) -> Term {
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

/// Программа, готовая к замеру обоими путями.
struct Program {
    signature: Signature,
    /// Терм, как написан: его считает машина.
    written: Term,
    /// Он же после специализации: его понижает бэкенд.
    made: Term,
    /// Ответ по мнению машины.
    answer: String,
}

impl Program {
    fn new(shape: Shape, depth: usize) -> Self {
        let text = source(shape, depth);
        let (mut signature, mut metas, instances) = elaborated(&text);
        let written = entry(&signature);
        let answer = adamas_interp::run(&signature, &written)
            .expect("операция обязана встретить хендлер")
            .printed(Some(PRINT_DEPTH))
            .to_string();
        let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
            .expect("специализация обязана пройти")
            .term;
        Self {
            signature,
            written,
            made,
            answer,
        }
    }

    /// Текст C либо названный отказ понижения.
    fn lowered(&self) -> Result<String, adamas_codegen::CompileError> {
        adamas_codegen::compile(&self.signature, &self.made)
    }
}

// --- порождённый C ------------------------------------------------------

/// Место под порождённый C и его сборку.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("bench-native");
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Объектные файлы рантайма: собираются однажды на весь прогон.
///
/// `-O2`, а не `-O1` тестового харнесса: замер говорит о том, что получит
/// пользователь release-сборкой, и уровень оптимизации — часть окружения,
/// которое число обязано нести рядом с собой.
fn runtime() -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let dir = scratch();
        [
            "object.c",
            "array.c",
            "region.c",
            "evidence.c",
            "closure.c",
            "frame.c",
        ]
        .iter()
        .map(|name| {
            let object = dir.join(format!("{name}.o"));
            let status = Command::new(env!("ADAMAS_CC"))
                .args(["-std=c11", "-O2", "-c"])
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
fn built(name: &str, text: &str) -> PathBuf {
    let dir = scratch();
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();
    compiled(&source, &binary);
    binary
}

/// Вызов компилятора C — отдельно, потому что он же и мерится.
fn compiled(source: &Path, binary: &Path) {
    let output = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O2", "-fwrapv", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(source)
        .args(runtime())
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
fn ran(binary: &Path) -> (String, String) {
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

/// Собранная программа, чей ответ уже сверен с машиной.
fn checked(program: &Program, name: &str) -> PathBuf {
    let text = program.lowered().expect("чистая форма обязана понижаться");
    let binary = built(name, &text);
    let (stdout, stderr) = ran(&binary);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        program.answer,
        "{name}: понижение посчитало не то, что машина"
    );
    // Счётчики печатает точка входа безусловно; строку видно в отчёте прогона
    // `--test`, и по ней читается, сработал ли reuse.
    eprintln!("{name}: ответ {}, {}", program.answer, stderr.trim_end());
    binary
}

// --- сосед на Rust ------------------------------------------------------

/// Тот же алгоритм эквивалентным кодом: те же конструкторы, та же владеющая
/// рекурсия, то же заворачивание.
enum Tree {
    Leaf(i64),
    Node(Box<Tree>, Box<Tree>),
}

fn grow(depth: usize, seed: i64) -> Tree {
    if depth == 0 {
        return Tree::Leaf(seed);
    }
    let doubled = seed.wrapping_mul(2);
    Tree::Node(
        Box::new(grow(depth - 1, doubled)),
        Box::new(grow(depth - 1, doubled.wrapping_add(1))),
    )
}

fn scaled(tree: Tree) -> Tree {
    match tree {
        Tree::Leaf(x) => Tree::Leaf(x.wrapping_mul(3)),
        Tree::Node(left, right) => Tree::Node(Box::new(scaled(*left)), Box::new(scaled(*right))),
    }
}

fn total(tree: Tree) -> i64 {
    match tree {
        Tree::Leaf(x) => x,
        Tree::Node(left, right) => total(*left).wrapping_add(total(*right)),
    }
}

fn neighbour(depth: usize) -> i64 {
    total(scaled(grow(depth, 1)))
}

// --- замеры -------------------------------------------------------------

fn symbolic(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("symbolic");
    // Точка `native` — запуск процесса, точка `interp` — секунды: сотня
    // выборок по умолчанию превратила бы прогон в часы.
    group.sample_size(10);

    // Цена запуска процесса и печати: та же программа без работы.
    let floor = Program::new(Shape::Pure, 0);
    let binary = checked(&floor, "floor");
    group.bench_function("floor", |bencher| bencher.iter(|| ran(&binary)));

    // Сосед на Rust — только у чистой формы: под хендлером сравнивать не с
    // чем, там сравниваются между собой две формы понижения.
    for depth in DEPTHS {
        let pure = Program::new(Shape::Pure, depth);
        let expected: i64 = pure.answer.parse().expect("ответ — число");
        assert_eq!(
            neighbour(depth),
            expected,
            "сосед на Rust считает не тот же алгоритм"
        );
        group.bench_function(format!("rust/{depth}"), |bencher| {
            bencher.iter(|| neighbour(depth));
        });
    }

    // Формы обязаны считать одно число: иначе «тот же алгоритм под хендлером»
    // было бы неправдой, и сравнение шло бы между разными программами.
    let sample = DEPTHS[0];
    assert_eq!(
        Program::new(Shape::Pure, sample).answer,
        Program::new(Shape::TailResumptive, sample).answer,
        "формы обязаны считать одно число"
    );

    for shape in [Shape::Pure, Shape::TailResumptive] {
        let name = shape.name();
        for depth in DEPTHS {
            let program = Program::new(shape, depth);
            match program.lowered() {
                Ok(text) => {
                    let binary = built(&format!("{name}{depth}"), &text);
                    let (stdout, stderr) = ran(&binary);
                    assert_eq!(
                        stdout.trim_end_matches('\n'),
                        program.answer,
                        "{name}/{depth}: понижение посчитало не то, что машина"
                    );
                    eprintln!(
                        "native/{name}/{depth}: ответ {}, {}",
                        program.answer,
                        stderr.trim_end()
                    );
                    group.bench_function(format!("native/{name}/{depth}"), |bencher| {
                        bencher.iter(|| ran(&binary));
                    });
                }
                // Шов трека B: форма под хендлером сегодня отвергается, и
                // отказ обязан быть про хендлер, а не про что-то ещё.
                Err(error) => {
                    let refusal = error.to_string();
                    assert!(
                        shape == Shape::TailResumptive && refusal.contains("#handle"),
                        "{name}/{depth}: понижение отвергло по неожиданной причине: {refusal}"
                    );
                    eprintln!(
                        "native/{name}/{depth}: не мерится — понижение отвергает: {refusal} (трек B волны 4)"
                    );
                }
            }
        }
        for depth in DEPTHS {
            let program = Program::new(shape, depth);
            group.bench_function(format!("interp/{name}/{depth}"), |bencher| {
                bencher.iter(|| adamas_interp::run(&program.signature, &program.written).unwrap());
            });
        }
    }

    group.finish();
}

fn codegen(criterion: &mut Criterion) {
    let program = Program::new(Shape::Pure, CODEGEN_DEPTH);
    let lowered = adamas_codegen::lower::lower(&program.signature, &program.made)
        .expect("чистая форма обязана понижаться");
    let inserted = adamas_codegen::perceus::insert(lowered.clone());
    let text = adamas_codegen::emit_c::emit(&inserted).expect("форма понижения известна эмиттеру");

    let mut group = criterion.benchmark_group("codegen");
    group.bench_function("lower", |bencher| {
        bencher.iter(|| adamas_codegen::lower::lower(&program.signature, &program.made).unwrap());
    });
    group.bench_function("perceus", |bencher| {
        bencher.iter(|| adamas_codegen::perceus::insert(lowered.clone()));
    });
    group.bench_function("emit", |bencher| {
        bencher.iter(|| adamas_codegen::emit_c::emit(&inserted).unwrap());
    });

    // §6 время сборки не ограничивает — точка стоит затем, чтобы доля
    // понижения в общем пути читалась, а не угадывалась.
    let dir = scratch();
    let source = dir.join("codegen.c");
    let binary = dir.join("codegen");
    std::fs::write(&source, &text).unwrap();
    group.sample_size(10);
    group.bench_function("cc", |bencher| bencher.iter(|| compiled(&source, &binary)));
    group.finish();
}

criterion_group!(benches, symbolic, codegen);
criterion_main!(benches);

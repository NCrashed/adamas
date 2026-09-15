//! Нагрузки трека Z, кроме символьной: скалярный цикл и FBIP-цикл.
//!
//! Трек Z Фазы 7 (`docs/phase7-plan.md`) мерит разрыв двух бэкендов на четырёх
//! нагрузках — скалярная арифметика, аллокационно-тяжёлый символьный код,
//! FBIP-цикл, SIMD-ядро. LLVM-эмиттера ещё нет, поэтому здесь берётся первая
//! половина обязательства: те же нагрузки на **одном** бэкенде, чтобы к приходу
//! второго было с чем сравнивать. Таблица — `docs/measurements/workload-gap/`.
//!
//! Символьная нагрузка мерится не здесь, а в `native.rs`: там же живёт и
//! **методика**, которой подчиняется этот стенд. Читать её надо там; здесь
//! только две нагрузки и их соседи.
//!
//! # Почему отдельный стенд, а не ещё две группы в `native.rs`
//!
//! Требование Z дословно: «каждая строка воспроизводится одной командой».
//! Фильтр criterion гасит **точки**, но не подготовку вокруг них: парный замер
//! `native.rs` идёт после `group.finish()` и стоит минут. Команда, обязанная
//! воспроизвести одну строку, тянула бы за собой весь символьный стенд.
//! Общее у двух стендов вынесено в `harness`, а не скопировано.
//!
//! # Первая нагрузка: скалярная арифметика, и почему у неё две формы
//!
//! `mix n acc = mix (n − 1) (f acc n)`, счётчик и накопитель плоские. Форм
//! цепочки две ([`Chain`]), и вторая заведена **замером**, а не для полноты.
//!
//! Естественная запись — `acc · K + n` с множителем-литералом. Она даёт разрыв
//! с соседом в **шесть раз**, и ни одна его доля нам не принадлежит:
//! развёрнутая на `U` витков, аффинная цепочка с постоянным `K` складывается
//! обратно в одно умножение на `K^U` плюс член, линейный по счётчику. LLVM это
//! делает, gcc нет. Проверено тремя способами, и все три говорят одно: тот же
//! цикл руками на C стоит столько же, сколько наш; тот же цикл на Rust с
//! множителем **из аргумента** стоит столько же, сколько наш; а цепочка
//! `acc · acc · K + n`, которую разворачивать нечем, ставит отношение на
//! **1.08**. Первые два свидетеля — `scalar-decomposition.sh`, третий — точка
//! [`Chain::Squaring`] рядом.
//!
//! Мерятся поэтому обе, и в таблице стоят обе. Выкинуть аффинную значило бы
//! спрятать шестикратный разрыв, который существует; выкинуть нелинейную —
//! выдать одну оптимизацию LLVM за качество понижения.
//!
//! До трека A волны 5 нагрузка не выражалась ни в одной форме: счётчик обязан
//! был быть индуктивным. Теперь он плоский, и это наблюдаемо — прогон печатает
//! **ноль** выданных блоков, то есть на витке нет ни ячейки кучи (проверяется
//! ниже, а не предполагается).
//!
//! Самовызов в хвосте в порождённом C записан обычным вызовом `fn_1(...)`,
//! петли эмиттер не строит. Что она всё-таки получается, проверено прогоном, а
//! не чтением: [`SCALAR_TURNS`] витков — это глубина рекурсии, на которой
//! кадров не хватило бы никакому стеку, и прогон её проходит. Сосед той же
//! проверки не проходит и потому написан петлёй — см. «сосед на Rust» ниже.
//!
//! # Третья нагрузка: FBIP-цикл
//!
//! Список из [`FBIP_CELLS`] ячеек, [`FBIP_PASSES`] проходов; проход
//! (`step`) разбирает `Cons` и строит `Cons` — каноническая форма §5.1, в
//! которой Perceus переписывает разобранную ячейку вместо того, чтобы ронять
//! её и брать новую. Свёртка `total` умножает накопитель на три, поэтому она
//! чувствительна к порядку: проход список **разворачивает**, и потерянный
//! проход виден ответом, а не только временем.
//!
//! Наблюдаемое здесь не время, а счётчик: блоков выдано ровно
//! [`FBIP_CELLS`] — столько, сколько построил `build`. Все
//! [`FBIP_PASSES`] проходов стоят **ноль** ячеек. Это и проверяется
//! утверждением: строка, у которой reuse отвалился, упадёт здесь, а не
//! разойдётся на проценты во времени.
//!
//! Сосед на Rust написан **эквивалентным кодом** (§6: «Rustc на эквивалентном
//! коде»): тот же список из `Cons`/`Nil` на `Box`, то же владение, тот же
//! порядок «освободить, потом взять». Reuse у него не бывает по построению — `Box::new`
//! берёт ячейку, а разобранная уходит в `free`, — и это не поддавка, а ровно
//! то, что §5.1 обещает выиграть: «без FBIP каждое преобразование = O(n)
//! аллокаций; с FBIP на уникальных инпутах — 0».
//!
//! # Четвёртая нагрузка: дыра
//!
//! SIMD-ядра здесь нет, и это не упущение стенда. `Simd n a` (§4.9) в языке не
//! реализован: ни типа, ни класса `Primitive`, ни операций, ни выравненных
//! буферов. Проверено прогоном: `adamas check` на `lane : Simd 4 Float32`
//! отвечает «имя `Simd` не найдено». Трек H Фазы 7. Скалярный эквивалент тоже не
//! заведён: без `Simd` он неотличим от первой нагрузки, а строка, дублирующая
//! соседнюю, разрыва не мерит.
//!
//! # Что сверяется до всякого замера
//!
//! - **Ответ машины** — на мелком размере. Полный размер машине не по силам:
//!   [`SCALAR_TURNS`] витков интерпретатор считал бы часами. Мелкий размер
//!   ловит то, ради чего сверка и стоит: расхождение семантики, а не арифметики
//!   большого числа.
//! - **Ответ соседа** — на полном. Обе стороны печатают число, и совпадение на
//!   [`SCALAR_TURNS`] витках означает, что заворачивание, порядок и знаковость
//!   у них одни.
//! - **Счётчики блоков** — у обеих нагрузок, утверждением.
//!
//! # Чем проверено, что строки мерят названное
//!
//! Обеим подсунуто замедление, и обе на него ответили (2026-09-15).
//!
//! - **Скалярной** — лишнее умножение в цепочке, у обеих сторон разом
//!   (`acc · K + n` → `acc · acc · K + n`). Наша сторона 47.1 → 77.7 мс, и это
//!   ровно то, чего стоит второе умножение в зависимой цепочке. Заодно
//!   выяснилось главное про эту нагрузку: сосед на том же шаге идёт 7.6 → 72.5,
//!   то есть в **девять с половиной раз**, и шестикратный разрыв аффинной
//!   формы обращается в паритет. Отсюда две цепочки в таблице, а не одна.
//! - **FBIP** — выключенный reuse: одна строка [`adamas_codegen::perceus`]
//!   (`Reclaim` не заводится никогда), и всё остальное как было. Блоков стало
//!   6 500 000 вместо 100 000 — ровно ячейка на элемент на проход, — время
//!   14.1 → 36.9 мс, отношение 0.45 → **1.22**. То есть строка мерит именно
//!   переписывание на месте: без него понижение оказывается **медленнее**
//!   соседа, платя ту же аллокацию плюс счётчик ссылок.
//!
//!   Утверждение о счётчике этот мутант ловит первым и без всякого времени:
//!   прогон падает на «проход выдал ячейки».

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

use std::path::PathBuf;

use adamas_core::term::PRINT_DEPTH;
use adamas_elab::mono;
use criterion::{Criterion, SamplingMode, criterion_group};

use harness::{NEIGHBOUR, blocks, built, by_floor, elaborated, entry, ran, ran_neighbour, ratio};

/// Место под порождённый C и его сборку — своё у стенда.
const STAND: &str = "bench-workloads";

/// Множитель скалярной цепочки: тот же, что у `PCG`-семейства.
const MIX: u64 = 6_364_136_223_846_793_005;

/// Форма скалярной цепочки. Различаются они одним умножением, а числом — в
/// шесть раз, и вся разница принадлежит **соседу**, не нам.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Chain {
    /// `acc := acc · acc · K + n`. По `acc` нелинейна, разворачивать нечего.
    Squaring,
    /// `acc := acc · K + n` — аффинная, и множитель у неё **литерал**.
    ///
    /// Развёрнутая на `U` витков, такая цепочка складывается обратно: `K^U`
    /// считается на компиляции, а сумма `Σ K^j · b_j` линейна по счётчику.
    /// LLVM это делает, gcc нет, и отсюда шестикратный разрыв, к понижению
    /// отношения не имеющий. Свидетели — `scalar-decomposition.sh` и точка
    /// [`Chain::Squaring`] рядом.
    Affine,
}

impl Chain {
    const ALL: [Self; 2] = [Self::Squaring, Self::Affine];

    /// Имя группы замера и запроса к соседу.
    const fn name(self) -> &'static str {
        match self {
            Self::Squaring => "scalar",
            Self::Affine => "scalar-affine",
        }
    }

    /// Тело витка на Adamas.
    fn step(self) -> String {
        match self {
            Self::Squaring => format!("addUInt64 (mulUInt64 (mulUInt64 acc acc) {MIX}) n"),
            Self::Affine => format!("addUInt64 (mulUInt64 acc {MIX}) n"),
        }
    }

    /// Он же на Rust — те же операции в том же порядке.
    fn mix(self, n: u64) -> u64 {
        let (mut acc, mut left): (u64, u64) = (0, n);
        match self {
            Self::Squaring => {
                while left != 0 {
                    acc = acc.wrapping_mul(acc).wrapping_mul(MIX).wrapping_add(left);
                    left -= 1;
                }
            }
            Self::Affine => {
                while left != 0 {
                    acc = acc.wrapping_mul(MIX).wrapping_add(left);
                    left -= 1;
                }
            }
        }
        acc
    }
}

/// Витков скалярного цикла.
///
/// Выбрано так, чтобы работа была на два порядка выше пола запуска процесса
/// (~0.2 мс): полсотни миллионов витков идут около 50 мс.
const SCALAR_TURNS: u64 = 50_000_000;

/// Ячеек в списке FBIP-цикла и проходов по нему.
///
/// Ячеек столько, чтобы список не помещался в кэш и обход платил за память;
/// проходов столько, чтобы построение списка (единственное место, где ячейки
/// выдаются) было малой долей измеряемого — иначе мерился бы `build`, а не
/// reuse.
const FBIP_CELLS: i64 = 100_000;
const FBIP_PASSES: i64 = 64;

/// Мелкие размеры: на них сверяется ответ машины.
const SCALAR_SMALL: u64 = 1_000;
const FBIP_SMALL: (i64, i64) = (16, 5);

// --- исходники -----------------------------------------------------------

/// `Bool` объявляется программой: литеральный паттерн есть разбор по `eqT x k`,
/// и конструкторы ответа он берёт соглашением (трек A волны 5).
const BOOL: &str = "\
data Bool where
  True : Bool
  False : Bool
";

/// Скалярный цикл: плоский счётчик, плоский накопитель, ноль ячеек кучи.
fn scalar_source(chain: Chain, turns: u64) -> String {
    let step = chain.step();
    format!(
        "{BOOL}
mix : UInt64 -> UInt64 -> UInt64
mix 0 acc = acc
mix n acc = mix (subUInt64 n 1) ({step})

main : UInt64
main = mix {turns} 0
"
    )
}

/// FBIP-цикл: список строится однажды, проходы переписывают его на месте.
fn fbip_source(cells: i64, passes: i64) -> String {
    format!(
        "{BOOL}
data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

-- Разобран `Cons`, построен `Cons`: форма та же, слоты переписываются (§5.1).
step : List -> List -> List
step Nil acc = acc
step (Cons x xs) acc = step xs (Cons (addInt64 x 1) acc)

turn : Int64 -> List -> List
turn 0 xs = xs
turn n xs = turn (subInt64 n 1) (step xs Nil)

-- Свёртка чувствительна к порядку: проход разворачивает список, и потерянный
-- проход виден ответом.
total : List -> Int64 -> Int64
total Nil acc = acc
total (Cons x xs) acc = total xs (addInt64 (mulInt64 acc 3) x)

main : Int64
main = total (turn {passes} (build {cells} Nil)) 0
"
    )
}

// --- понижение и машина --------------------------------------------------

/// Порождённый C: специализация, понижение, эмиссия.
fn lowered(source: &str) -> String {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = entry(&signature);
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана пройти")
        .term;
    adamas_codegen::compile(&signature, &made).expect("нагрузка обязана понижаться")
}

/// Ответ машины, то есть `adamas eval`.
fn machine(source: &str) -> String {
    let (signature, _, _) = elaborated(source);
    let written = entry(&signature);
    adamas_interp::run(&signature, &written)
        .expect("чистая программа обязана считаться")
        .printed(Some(PRINT_DEPTH))
        .to_string()
}

/// Собранная нагрузка: двоичный файл, ответ, счётчики блоков.
struct Load {
    binary: PathBuf,
    answer: String,
    allocated: usize,
    live: usize,
}

impl Load {
    fn new(name: &str, source: &str) -> Self {
        let binary = built(&harness::scratch(STAND), name, &lowered(source));
        let (stdout, stderr) = ran(&binary);
        let (allocated, live) = blocks(&stderr);
        eprintln!("{name}: ответ {}, {}", stdout.trim_end(), stderr.trim_end());
        Self {
            binary,
            answer: stdout.trim_end_matches('\n').to_owned(),
            allocated,
            live,
        }
    }
}

/// Понижение отвечает то же, что машина, — на размере, который машине по силам.
fn agrees(name: &str, source: &str) {
    let expected = machine(source);
    let load = Load::new(name, source);
    assert_eq!(
        load.answer, expected,
        "{name}: понижение посчитало не то, что машина"
    );
    assert_eq!(load.live, 0, "{name}: прогон оставил живые блоки");
}

// --- сосед на Rust -------------------------------------------------------
//
// Оба соседа написаны **петлёй, а не самовызовом**, и это измерено, а не
// выбрано. Хвостовая рекурсия — та самая, какой обе нагрузки написаны на
// Adamas, — у rustc гарантии не имеет, и обрывается она в обе стороны: обход
// списка упал `SIGABRT` уже в release (освобождение `Box`, из которого
// значение вынуто, стоит после вызова, и вызов перестаёт быть последним
// действием), а скалярный `mix` — в debug, под `cargo test --all-targets`,
// где сворачивать хвост некому.
//
// Сравниваются поэтому две петли. У порождённого C она тоже получается —
// самовызов в хвосте эмиттер печатает обычным вызовом, а в петлю его
// сворачивает `-foptimize-sibling-calls`, — и вот это как раз проверено
// прогоном: [`SCALAR_TURNS`] витков ни одному стеку кадрами не покрыть.
// Кредита за несвёрнутый хвост соседа стенд себе не берёт: разной остаётся
// ровно та вещь, ради которой строка и мерится, — у соседа ячейка на элемент
// прохода, у понижения ноль.

/// Список эквивалентными формами данных: те же конструкторы, владение через
/// `Box`.
enum List {
    Nil,
    Cons(i64, Box<List>),
}

fn build(n: i64, xs: List) -> List {
    let mut xs = xs;
    let mut left = n;
    while left != 0 {
        xs = List::Cons(left, Box::new(xs));
        left -= 1;
    }
    xs
}

/// Проход: разобранная ячейка уходит в `free`, построенная берётся `Box::new`.
///
/// Переписать её на месте Rust не даёт, и это не свойство кода, а свойство
/// модели: reuse §5.1 держится на счётчике ссылок, которого у `Box` нет.
/// Порядок здесь тот же, что у понижения, — сперва освободить, потом взять, —
/// иначе аллокатор соседа не попадал бы в tcache там, где попадает наш.
fn step(xs: List, acc: List) -> List {
    let mut xs = xs;
    let mut acc = acc;
    while let List::Cons(x, rest) = xs {
        xs = *rest;
        acc = List::Cons(x.wrapping_add(1), Box::new(acc));
    }
    acc
}

fn turn(n: i64, xs: List) -> List {
    let mut xs = xs;
    for _ in 0..n {
        xs = step(xs, List::Nil);
    }
    xs
}

fn total(xs: List, acc: i64) -> i64 {
    let mut xs = xs;
    let mut acc = acc;
    while let List::Cons(x, rest) = xs {
        xs = *rest;
        acc = acc.wrapping_mul(3).wrapping_add(x);
    }
    acc
}

/// Дочерний прогон соседа, если стенд запущен им.
///
/// Запрос — имя нагрузки и её размеры через двоеточие: `scalar:<витков>`,
/// `scalar-affine:<витков>`, `fbip:<ячеек>:<проходов>`.
fn as_child() -> bool {
    let Ok(request) = std::env::var(NEIGHBOUR) else {
        return false;
    };
    let mut field = request.split(':');
    let kind = field.next().expect("у запроса есть имя нагрузки");
    let number = |field: Option<&str>| -> i64 {
        field
            .expect("размер нагрузки назван")
            .parse()
            .expect("размер нагрузки — число")
    };
    if let Some(chain) = Chain::ALL.into_iter().find(|chain| chain.name() == kind) {
        let turns = number(field.next());
        println!(
            "{}",
            chain.mix(u64::try_from(turns).expect("витков не меньше нуля"))
        );
        return true;
    }
    match kind {
        "fbip" => {
            let cells = number(field.next());
            let passes = number(field.next());
            println!("{}", total(turn(passes, build(cells, List::Nil)), 0));
        }
        other => panic!("стенд не знает нагрузки `{other}`"),
    }
    true
}

// --- замеры --------------------------------------------------------------

/// Скалярная арифметика: первая нагрузка трека Z, обеими цепочками.
fn scalar(criterion: &mut Criterion) {
    for chain in Chain::ALL {
        one_chain(criterion, chain);
    }
}

/// Одна форма цепочки: пол, работа, сосед, отношение.
fn one_chain(criterion: &mut Criterion, chain: Chain) {
    let name = chain.name();
    let mut group = criterion.benchmark_group(name);
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    agrees(
        &format!("{name}-small"),
        &scalar_source(chain, SCALAR_SMALL),
    );

    // Пол — та же программа без работы; свой у каждой стороны, потому что
    // двоичных файлов два.
    let floor = Load::new(&format!("{name}-floor"), &scalar_source(chain, 0));
    let idle = format!("{name}:0");
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&floor.binary)));
    });
    group.bench_function("rust/floor", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&idle)));
    });

    let load = Load::new(name, &scalar_source(chain, SCALAR_TURNS));
    // Плоский счётчик наблюдаем здесь: индуктивный дал бы ячейку на виток.
    assert_eq!(
        load.allocated, 0,
        "{name}: скалярный цикл выдал блоки — счётчик или накопитель перестал \
         быть плоским"
    );
    let request = format!("{name}:{SCALAR_TURNS}");
    let (stdout, _) = ran_neighbour(&request);
    assert_eq!(
        stdout.trim(),
        load.answer,
        "{name}: сосед на Rust считает не тот же цикл"
    );

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&load.binary)));
    });
    group.bench_function("rust", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&request)));
    });
    group.finish();

    // Число строки таблицы берётся здесь, а не у отчёта: см. [`ratio`].
    ratio(
        name,
        || drop(ran(&load.binary)),
        || drop(ran(&floor.binary)),
        || drop(ran_neighbour(&request)),
        || drop(ran_neighbour(&idle)),
    );
}

/// FBIP-цикл: третья нагрузка трека Z.
fn fbip(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("fbip");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    let (cells, passes) = FBIP_SMALL;
    agrees("fbip-small", &fbip_source(cells, passes));

    let floor = Load::new("fbip-floor", &fbip_source(0, 0));
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&floor.binary)));
    });
    group.bench_function("rust/floor", |bencher| {
        by_floor(bencher, || drop(ran_neighbour("fbip:0:0")));
    });

    let load = Load::new("fbip", &fbip_source(FBIP_CELLS, FBIP_PASSES));
    // Единственные выданные ячейки — те, что построил `build`. Все проходы
    // переписывают их на месте, и это утверждение, а не наблюдение: сломанный
    // reuse уронит стенд здесь.
    assert_eq!(
        load.allocated,
        usize::try_from(FBIP_CELLS).expect("ячеек не меньше нуля"),
        "проход выдал ячейки — reuse §5.1 не сработал"
    );
    let request = format!("fbip:{FBIP_CELLS}:{FBIP_PASSES}");
    let (stdout, _) = ran_neighbour(&request);
    assert_eq!(
        stdout.trim(),
        load.answer,
        "сосед на Rust считает не тот же цикл"
    );

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&load.binary)));
    });
    group.bench_function("rust", |bencher| {
        by_floor(bencher, || drop(ran_neighbour(&request)));
    });
    group.finish();

    ratio(
        "FBIP-цикл",
        || drop(ran(&load.binary)),
        || drop(ran(&floor.binary)),
        || drop(ran_neighbour(&request)),
        || drop(ran_neighbour("fbip:0:0")),
    );
}

criterion_group!(benches, scalar, fbip);

/// `main` написан руками, а не взят у `criterion_main!`: дочерний прогон
/// соседа ([`as_child`]) обязан отвечать раньше, чем criterion разберёт
/// аргументы. Остальное — дословно то, во что разворачивается макрос.
fn main() {
    if as_child() {
        return;
    }
    benches();
    Criterion::default().configure_from_args().final_summary();
}

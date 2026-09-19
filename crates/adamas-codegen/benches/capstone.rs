//! Капстоун против соседа, написанного руками на C с intrinsics.
//!
//! Милестоун Фазы 7 (§9) записан одной строкой: *systems capstone (packet
//! processor) достигает near-C performance на SIMD-нагрузках*. §6 держит под
//! неё строку «SIMD-heavy код (§4.9) - паритет с C+intrinsics», и референсом
//! там стоит **ручной** вектор. Этот стенд её и мерит - не на микроядре, как
//! мерила её строка 4б таблицы разрыва, а на самом капстоуне.
//!
//! Таблица и разбор - `docs/measurements/capstone-gap/README.md`. **Методика**
//! живёт в шапке `native.rs`, разделом «Методика»; здесь она не
//! пересказывается.
//!
//! # Программа берётся у корпуса, а сосед пишется рядом
//!
//! Капстоун - `tests/golden/eval/packets.adamas`, программа корпуса: её
//! прогоняет договором трёх вычислителей `tests/agreement.rs`, а многопоточную
//! половину - `tests/capstone.rs`. Стенд её **не переписывает**, а читает и
//! подставляет две строки размера ([`harness::resized`]); имя размера,
//! встретившееся не ровно один раз, роняет прогон. Второй копии программы не
//! заводится - на этом волна 5 Фазы 6 потеряла пункт милестоуна.
//!
//! Второй записи не избежать ровно у соседа: §6 требует эквивалентного кода,
//! то есть отдельной реализации. Разъезд с ней ловится **ответом** - обе
//! стороны печатают одну строку, и стенд сверяет её до всякого замера, на
//! полном размере.
//!
//! # Однопоточно, и это выбор, а не умолчание
//!
//! Капстоун умеет четыре настоящих воркера, и что он на них отвечает верно,
//! проверено врозь (`tests/capstone.rs`, 24 прогона обоими бэкендами). Здесь
//! обе стороны идут **однопоточными**: §6 спрашивает о качестве кода, а четыре
//! потока мерили бы планировщик и раскладку кучи под ним. Нашей стороне для
//! этого довольно не задавать `ADAMAS_THREADS`; у соседа воркеры идут по
//! очереди.
//!
//! # Что именно сравнивается
//!
//! Строк у стенда две, и вторая есть разложение первой.
//!
//! *Капстоун целиком.* Пол - тот же капстоун на **одном** пакете и нуле
//! проходов: меньше он не бывает, `cellAt churned 0` требует хотя бы одного
//! пакета. Пол поэтому вычитает не только запуск процесса, но и постоянную
//! часть работы - заведение питомника, четыре файбера, печать ответа.
//!
//! *Горячая половина.* Полом берётся тот же капстоун при `rounds = 0`, то есть
//! программа, у которой `churning` - тождество. Разность двух точек и есть
//! цена вектора над колонкой, а отношение разностей - то, что §6 и называет
//! «SIMD-heavy код».
//!
//! # Чем проверено, что сравниваются коды
//!
//! Тем же, чем это проверено у таблицы разрыва: строка сборки у соседа та же
//! ([`harness::RELEASE`] плюс `-fwrapv -ffp-contract=off`), базовая линия
//! архитектуры у обеих сторон generic (`gcc` без `-march`, `llc` без `-mcpu`),
//! межмодульная оптимизация у обеих. Свидетели печатаются под
//! [`harness::WITNESS`]: счёт вызовов в горячей функции каждой стороны и цена
//! отнятой межмодульной оптимизации.

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

use harness::{
    Backend, Column, Load, Support, by_floor, corpus, elaborated, entry, llvm_against_c, ran,
    ratio, resized, same_work,
};

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::llvm::Toolchain;
use adamas_elab::mono;

const STAND: &str = "bench-capstone";

/// Пакетов в буфере: 4096 по 64 байта - буфер в 256 килобайт.
///
/// Размер выбран замером, а не круглостью: нагрузка пакетов **буферами**, а не
/// потоком, и полезная часть (четыре слова на пакет, 128 килобайт) держится в
/// L2. Ровно того же держится и сосед, так что отношение о кэше ничего не
/// говорит - оно говорит о витке.
const PACKETS: u64 = 4096;

/// Проходов вектора по колонке.
///
/// Столько, чтобы строка была тем, чем названа: при этом числе на `churning`
/// приходится около девяти десятых измеряемого у обеих сторон, и «SIMD-heavy»
/// перестаёт быть словом. Проверяется это второй строкой стенда, а не
/// предполагается.
const ROUNDS: u64 = 1024;

/// Пол капстоуна: один пакет, ноль проходов.
///
/// Нуля пакетов не бывает - `cellAt churned 0` читает нулевой пакет, и при
/// пустой колонке прогон обрывается выходом за длину. Свой пол у каждой
/// стороны, потому что двоичных файлов три.
const FLOOR_PACKETS: u64 = 1;

/// Текст соседа. Собирается тем же компилятором и той же строкой, что наш C.
const NEIGHBOUR: &str = include_str!("neighbour/packets.c");

// --- программа берётся у корпуса ------------------------------------------

fn capstone_source(packets: u64, rounds: u64) -> String {
    resized(
        &corpus("packets"),
        &[("packets", packets), ("rounds", rounds)],
    )
}

/// Мутант «горячая половина по дорожке»: тот же капстоун без `Simd` в `churn`.
///
/// Нужен ради одного числа - чего `Simd` стоит **у нас**, - и оно же есть
/// ответ на вопрос, который сосед задаёт своей парой точек: на этом ядре и на
/// этой базовой линии ручной вектор проигрывает дорожке. Программа при этом
/// остаётся одной: мутант получается заменой в тексте корпуса, замена обязана
/// найтись, а ответ обязан совпасть с невредимым - иначе сравнивались бы две
/// разные работы.
fn per_lane_source(packets: u64, rounds: u64) -> String {
    let from = "  let window : Simd 4 UInt64 = simdLoad 4 xs at\n  \
                let next : Simd 4 UInt64 = simdAdd (simdMul window (simdSplat 4 spice)) \
                (simdSplat 4 pepper)\n  \
                let put : Array cells UInt64 = simdStore 4 xs at next\n  \
                churn put p";
    let to = "  let w0 : UInt64 = arrayIndex xs at\n  \
              let w1 : UInt64 = arrayIndex xs (addUInt64 at 1)\n  \
              let w2 : UInt64 = arrayIndex xs (addUInt64 at 2)\n  \
              let w3 : UInt64 = arrayIndex xs (addUInt64 at 3)\n  \
              let a0 : Array cells UInt64 = arraySet xs at \
              (addUInt64 (mulUInt64 w0 spice) pepper)\n  \
              let a1 : Array cells UInt64 = arraySet a0 (addUInt64 at 1) \
              (addUInt64 (mulUInt64 w1 spice) pepper)\n  \
              let a2 : Array cells UInt64 = arraySet a1 (addUInt64 at 2) \
              (addUInt64 (mulUInt64 w2 spice) pepper)\n  \
              let a3 : Array cells UInt64 = arraySet a2 (addUInt64 at 3) \
              (addUInt64 (mulUInt64 w3 spice) pepper)\n  \
              churn a3 p";
    let source = capstone_source(packets, rounds);
    assert!(
        source.contains(from),
        "мутант «по дорожке» не применился: тело `churn` в корпусе другое"
    );
    source.replace(from, to)
}

// --- понижение: одна программа, два бэкенда --------------------------------

struct Both {
    c: String,
    llvm: Result<Artefacts, adamas_codegen::CompileError>,
}

fn both(source: &str) -> Both {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = entry(&signature);
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана пройти")
        .term;
    Both {
        c: adamas_codegen::compile(&signature, &made).expect("капстоун обязан понижаться"),
        llvm: adamas_codegen::compile_llvm(&signature, &made),
    }
}

/// Капстоун, собранный обоими бэкендами из **одного** понижения.
struct Sides {
    source: String,
    c: Load,
    llvm: Option<Load>,
    ll: String,
}

fn sides(name: &str, source: &str, backend: Option<&Backend>) -> Sides {
    let program = both(source);
    let dir = harness::scratch(STAND);
    let c = Load::measured(name, harness::built(&dir, name, &program.c));
    let ll = program
        .llvm
        .as_ref()
        .map(|it| it.ll.clone())
        .unwrap_or_default();
    let llvm = backend.and_then(|backend| match &program.llvm {
        Ok(artefacts) => Some(backend.load(
            &format!("{name}-llvm"),
            artefacts,
            &backend.pipeline(),
            Support::Bitcode,
        )),
        Err(error) => {
            eprintln!("{name}: LLVM-эмиттер капстоун не берёт: {error}");
            None
        }
    });
    if let Some(llvm) = &llvm {
        same_work(name, &c, llvm);
    }
    Sides {
        source: source.to_owned(),
        c,
        llvm,
        ll,
    }
}

// --- сосед ------------------------------------------------------------------

/// Горячая половина соседа: руками вектором либо руками по дорожке.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kernel {
    /// `_mm_*` - то, что §6 называет референсом.
    Intrinsics,
    /// Та же работа по дорожке: точка разложения, а не сосед.
    PerLane,
    /// `_mm256_*`: тот же вектор, написанный под широкую базовую линию.
    Wide,
}

/// Базовая линия архитектуры, которую свидетель даёт **обеим** сторонам разом.
///
/// Штатное сравнение идёт на generic, как того требует таблица разрыва. Этот
/// ключ существует ради одного вопроса, который иначе остался бы догадкой: не
/// сидит ли отставание в узости базовой линии. Ответ в README; ставится он
/// обеим сторонам, и сосед при этом **переписывается** на `_mm256_*` -
/// сравнивать нашу широкую сборку с соседом, прибитым к 128 битам, значило бы
/// записать себе в заслугу то, что сосед не переписан.
const WIDER: &str = "-march=x86-64-v3";

/// Сосед, собранный той же строкой, что наш C.
///
/// Строка обязана быть той же: Фаза 6 намерила разрыв, 99% которого оказались
/// строкой сборки. `-march` не ставится ни одной стороне - у нас `llc` без
/// `-mcpu` и `gcc` без `-march`, - потому что иначе число мерило бы ключ
/// компилятора, а не руку программиста.
fn neighbour(dir: &Path, name: &str, packets: u64, rounds: u64, kernel: Kernel) -> PathBuf {
    let source = dir.join(format!("{name}.c"));
    std::fs::write(&source, NEIGHBOUR).expect("сосед обязан записываться");
    let binary = dir.join(name);
    let mut command = Command::new(env!("ADAMAS_CC"));
    command
        .args(harness::RELEASE)
        .args(["-fwrapv", "-ffp-contract=off", "-w"])
        .arg(format!("-DPACKETS={packets}"))
        .arg(format!("-DROUNDS={rounds}"));
    match kernel {
        Kernel::Intrinsics => {}
        Kernel::PerLane => {
            command.arg("-DKERNEL_SCALAR=1");
        }
        Kernel::Wide => {
            command.arg("-DKERNEL_WIDE=1").arg(WIDER);
        }
    }
    let made = command
        .arg(&source)
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    assert!(
        made.status.success(),
        "сосед не собрался:\n{}",
        String::from_utf8_lossy(&made.stderr)
    );
    binary
}

/// Наш порождённый C, собранный под ту же широкую базовую линию.
///
/// Рантайм при этом остаётся собранным под generic, и это не перекос: свидетель
/// мерит **горячую половину**, то есть разность двух точек, а рантайм в обеих
/// один и тот же и из разности уходит. На витке `churning` вызовов рантайма нет
/// ни одного - это и печатает свидетель витка.
fn built_wider(dir: &Path, name: &str, text: &str) -> PathBuf {
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).expect("порождённый C обязан записываться");
    let made = Command::new(env!("ADAMAS_CC"))
        .args(harness::RELEASE)
        .args(["-fwrapv", "-ffp-contract=off", "-w", WIDER])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(harness::runtime(dir))
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    assert!(
        made.status.success(),
        "порождённый C не собрался под {WIDER}:\n{}",
        String::from_utf8_lossy(&made.stderr)
    );
    binary
}

/// Ответ соседа: он же свидетель того, что сравнивается одна работа.
fn neighbour_answer(binary: &Path) -> String {
    let (stdout, _) = ran(binary);
    stdout.trim_end_matches('\n').to_owned()
}

// --- свидетель самого витка -------------------------------------------------

/// Функция, в теле которой стоит пакетное умножение дорожек.
///
/// Имя гвоздём не прибивается: у нашей стороны это `fn_8` либо
/// `fn_8.constprop.0`, и номер зависит от порядка понижения, а у соседа -
/// `churn` либо `churn.constprop.0`. Ищется поэтому **инструкция**; неизвестная
/// архитектура - отказ, потому что свидетель, молча считающий ноль, обманчив.
///
/// `pmuludq` выбран не как «какая-нибудь пакетная», а по существу: умножения
/// 64-битных дорожек в базовой линии x86-64 нет, и обе стороны обязаны
/// разворачивать его через 32×32→64. Найдись у одной из них что-то другое -
/// сравнивались бы разные ядра.
fn window_symbol(tools: &Toolchain, binary: &Path) -> String {
    let needle = if cfg!(target_arch = "x86_64") {
        "pmuludq"
    } else {
        panic!(
            "мнемоники пакетного умножения этой архитектуры свидетель не знает: \
             посчитать ноль значило бы соврать"
        )
    };
    let shown = Command::new(tools.tool("llvm-objdump"))
        .arg("-d")
        .arg(binary)
        .output()
        .expect("дизассемблер обязан запускаться");
    assert!(
        shown.status.success(),
        "`{}` не дизассемблировался",
        binary.display()
    );
    let text = String::from_utf8_lossy(&shown.stdout).into_owned();
    let mut symbol = String::new();
    for line in text.lines() {
        if let Some(rest) = line.strip_suffix(">:") {
            if let Some(open) = rest.rfind('<') {
                symbol.clear();
                symbol.push_str(&rest[open + 1..]);
            }
            continue;
        }
        if line.contains(needle) && !symbol.is_empty() {
            return symbol;
        }
    }
    panic!(
        "в `{}` нет ни одного `{needle}`: вектор собрался не тем, чем назван",
        binary.display()
    );
}

/// Что стоит в теле самого витка - у каждой из трёх сторон.
///
/// Свидетель `main` отвечает на вопрос про строку сборки, а этот - на вопрос
/// про виток: обе стороны держат его отдельной функцией, зовомой один раз, и
/// вызова **внутри** неё быть не должно ни у кого. Появись он - число говорило
/// бы о границе единиц трансляции, а не о коде.
fn hot_window(side: &str, tools: &Toolchain, binary: &Path) {
    let symbol = window_symbol(tools, binary);
    harness::hot_function("виток капстоуна", side, tools, binary, &symbol);
}

// --- замер ------------------------------------------------------------------

struct Stand {
    /// Капстоун на полном размере.
    load: Sides,
    /// Он же на одном пакете и нуле проходов: пол.
    floor: Sides,
    /// Он же на полном размере пакетов, но с `churning`-тождеством.
    bare: Sides,
    /// Он же с горячей половиной по дорожке, и его собственный пол.
    lane: Sides,
    lane_bare: Sides,
    /// Сосед: те же четыре точки.
    them: PathBuf,
    them_floor: PathBuf,
    them_bare: PathBuf,
    them_lane: PathBuf,
    them_lane_bare: PathBuf,
}

fn stand(backend: Option<&Backend>) -> Stand {
    let dir = harness::scratch(STAND);
    let load = sides("capstone", &capstone_source(PACKETS, ROUNDS), backend);
    let floor = sides(
        "capstone-floor",
        &capstone_source(FLOOR_PACKETS, 0),
        backend,
    );
    let bare = sides("capstone-bare", &capstone_source(PACKETS, 0), backend);
    let lane = sides("capstone-lane", &per_lane_source(PACKETS, ROUNDS), backend);
    let lane_bare = sides("capstone-lane-bare", &per_lane_source(PACKETS, 0), backend);

    let them = neighbour(&dir, "neighbour", PACKETS, ROUNDS, Kernel::Intrinsics);
    let them_floor = neighbour(
        &dir,
        "neighbour-floor",
        FLOOR_PACKETS,
        0,
        Kernel::Intrinsics,
    );
    let them_bare = neighbour(&dir, "neighbour-bare", PACKETS, 0, Kernel::Intrinsics);
    let them_lane = neighbour(&dir, "neighbour-lane", PACKETS, ROUNDS, Kernel::PerLane);
    let them_lane_bare = neighbour(&dir, "neighbour-lane-bare", PACKETS, 0, Kernel::PerLane);

    // Обе стороны считают одно, и это проверяется до всякого замера. Ответ
    // капстоуна зависит от содержимого пакета всеми своими полями
    // (`tests/capstone.rs`, четыре мутанта), так что совпадение строки - не
    // совпадение правдоподобных чисел.
    assert_eq!(
        neighbour_answer(&them),
        load.c.answer,
        "сосед на C считает не тот же капстоун"
    );
    assert_eq!(
        neighbour_answer(&them_bare),
        bare.c.answer,
        "сосед при `rounds = 0` считает не то же, что капстоун при `rounds = 0`"
    );
    assert_eq!(
        neighbour_answer(&them_lane),
        load.c.answer,
        "дорожечная половина соседа считает не то же, что его же вектор"
    );
    assert_eq!(
        lane.c.answer, load.c.answer,
        "мутант «по дорожке» посчитал не то же, что вектор: сравнивались бы две \
         разные работы"
    );
    // Колонка переписывается по месту, сколько бы проходов ни прошло: блоков у
    // полного прогона столько же, сколько у прогона без единого прохода.
    // Скопируй `simdStore` колонку на витке - строка мерила бы аллокатор.
    assert_eq!(
        load.c.allocated, bare.c.allocated,
        "проходы вектора выдали блоки: `simdStore` перестал писать по месту"
    );
    assert_eq!(load.c.live, 0, "капстоун оставил живые блоки");

    Stand {
        load,
        floor,
        bare,
        lane,
        lane_bare,
        them,
        them_floor,
        them_bare,
        them_lane,
        them_lane_bare,
    }
}

/// Абсолютные времена точек: то, что печатает отчёт criterion.
///
/// Врозь от [`capstone`] потому, что жанр другой: здесь выборка criterion, а
/// ниже — чередование [`ratio`], которое отчёта не читает вовсе. Числа таблицы
/// берутся оттуда, а не отсюда.
fn timings(criterion: &mut Criterion, it: &Stand) {
    let mut group = criterion.benchmark_group("capstone");
    group.sample_size(10);
    group.sampling_mode(SamplingMode::Flat);

    group.bench_function("native", |bencher| {
        by_floor(bencher, || drop(ran(&it.load.c.binary)));
    });
    group.bench_function("floor", |bencher| {
        by_floor(bencher, || drop(ran(&it.floor.c.binary)));
    });
    group.bench_function("neighbour", |bencher| {
        by_floor(bencher, || drop(ran(&it.them)));
    });
    group.bench_function("neighbour/floor", |bencher| {
        by_floor(bencher, || drop(ran(&it.them_floor)));
    });
    if let (Some(llvm), Some(llvm_floor)) = (&it.load.llvm, &it.floor.llvm) {
        group.bench_function("llvm", |bencher| {
            by_floor(bencher, || drop(ran(&llvm.binary)));
        });
        group.bench_function("llvm/floor", |bencher| {
            by_floor(bencher, || drop(ran(&llvm_floor.binary)));
        });
    }
    group.finish();
}

fn capstone(criterion: &mut Criterion) {
    let backend = Backend::new(STAND);
    let it = stand(backend.as_ref());
    timings(criterion, &it);

    // Строка милестоуна: капстоун целиком, обоими бэкендами.
    ratio(
        "капстоун, C-путь против соседа",
        || drop(ran(&it.load.c.binary)),
        || drop(ran(&it.floor.c.binary)),
        || drop(ran(&it.them)),
        || drop(ran(&it.them_floor)),
    );
    if let (Some(llvm), Some(llvm_floor)) = (&it.load.llvm, &it.floor.llvm) {
        ratio(
            "капстоун, LLVM-путь против соседа",
            || drop(ran(&llvm.binary)),
            || drop(ran(&llvm_floor.binary)),
            || drop(ran(&it.them)),
            || drop(ran(&it.them_floor)),
        );
    }

    // Та же строка, разложенная: горячая половина против неё же у соседа.
    ratio(
        "горячая половина, C-путь против соседа",
        || drop(ran(&it.load.c.binary)),
        || drop(ran(&it.bare.c.binary)),
        || drop(ran(&it.them)),
        || drop(ran(&it.them_bare)),
    );
    if let (Some(llvm), Some(bare)) = (&it.load.llvm, &it.bare.llvm) {
        ratio(
            "горячая половина, LLVM-путь против соседа",
            || drop(ran(&llvm.binary)),
            || drop(ran(&bare.binary)),
            || drop(ran(&it.them)),
            || drop(ran(&it.them_bare)),
        );
    }

    // Остаток программы: разбор, регионы, пересылка, свёртка - всё, кроме
    // `churning`. Строка §6 не о нём, и стоит он здесь затем, чтобы число
    // капстоуна целиком читалось: оно есть смесь двух половин, и доли их
    // названы, а не угаданы.
    ratio(
        "холодная половина, C-путь против соседа",
        || drop(ran(&it.bare.c.binary)),
        || drop(ran(&it.floor.c.binary)),
        || drop(ran(&it.them_bare)),
        || drop(ran(&it.them_floor)),
    );
    if let (Some(bare), Some(floor)) = (&it.bare.llvm, &it.floor.llvm) {
        ratio(
            "холодная половина, LLVM-путь против соседа",
            || drop(ran(&bare.binary)),
            || drop(ran(&floor.binary)),
            || drop(ran(&it.them_bare)),
            || drop(ran(&it.them_floor)),
        );
    }

    // Чего вектор стоит **сам по себе**: у нас и у соседа, на одной работе.
    // Больше единицы значит «вектор медленнее дорожки».
    ratio(
        "вектор против дорожки, C-путь",
        || drop(ran(&it.load.c.binary)),
        || drop(ran(&it.bare.c.binary)),
        || drop(ran(&it.lane.c.binary)),
        || drop(ran(&it.lane_bare.c.binary)),
    );
    if let (Some(llvm), Some(bare), Some(lane), Some(lane_bare)) = (
        &it.load.llvm,
        &it.bare.llvm,
        &it.lane.llvm,
        &it.lane_bare.llvm,
    ) {
        ratio(
            "вектор против дорожки, LLVM-путь",
            || drop(ran(&llvm.binary)),
            || drop(ran(&bare.binary)),
            || drop(ran(&lane.binary)),
            || drop(ran(&lane_bare.binary)),
        );
    }
    ratio(
        "вектор против дорожки, у соседа",
        || drop(ran(&it.them)),
        || drop(ran(&it.them_bare)),
        || drop(ran(&it.them_lane)),
        || drop(ran(&it.them_lane_bare)),
    );

    wider_baseline(&it);

    // Второй столбец: LLVM против C на том же капстоуне.
    if let (Some(llvm), Some(llvm_floor)) = (&it.load.llvm, &it.floor.llvm) {
        llvm_against_c(
            "капстоун",
            &Column {
                llvm,
                llvm_floor,
                c: &it.load.c,
                c_floor: &it.floor.c,
                ll: &it.load.ll,
            },
        );
        witnesses(backend.as_ref(), &it);
    }
}

/// Та же горячая половина при **широкой** базовой линии у обеих сторон.
///
/// Вопрос, на который отвечает свидетель: не сидит ли отставание в том, что
/// базовая линия узка. Ответ обязан быть числом, а не доводом, поэтому
/// `-march=x86-64-v3` даётся **и нам, и соседу**, а сосед при этом
/// переписывается на `_mm256_*`: ручные intrinsics прибиты к ширине, которую
/// написал программист, и наша широкая сборка против его узкой мерила бы не
/// код, а то, что его не переписали.
///
/// Мерится только горячая половина: рантайм под generic остаётся общим у обеих
/// наших точек и из разности уходит. LLVM-путь сюда не входит - его базовую
/// линию задаёт `llc`, а `-mcpu` стенд не передаёт; названо, чтобы не
/// показалось измеренным.
fn wider_baseline(it: &Stand) {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("свидетель/широкая базовая линия: `{WIDER}` - ключ x86-64, здесь не мерено");
        return;
    }
    let dir = harness::scratch(STAND);
    let ours = built_wider(&dir, "capstone-wide", &both(&it.load.source).c);
    let ours_bare = built_wider(&dir, "capstone-wide-bare", &both(&it.bare.source).c);
    let them = neighbour(&dir, "neighbour-wide", PACKETS, ROUNDS, Kernel::Wide);
    let them_bare = neighbour(&dir, "neighbour-wide-bare", PACKETS, 0, Kernel::Wide);
    let (answer, _) = ran(&ours);
    assert_eq!(
        answer.trim_end_matches('\n'),
        it.load.c.answer,
        "широкая сборка посчитала не то же, что штатная"
    );
    assert_eq!(
        neighbour_answer(&them),
        it.load.c.answer,
        "широкий сосед считает не тот же капстоун"
    );
    ratio(
        "горячая половина при широкой базовой линии, C-путь против соседа",
        || drop(ran(&ours)),
        || drop(ran(&ours_bare)),
        || drop(ran(&them)),
        || drop(ran(&them_bare)),
    );
    // И та же наша сторона против самой себя: чего ширина стоит нам одним.
    ratio(
        "широкая базовая линия против штатной, C-путь",
        || drop(ran(&ours)),
        || drop(ran(&ours_bare)),
        || drop(ran(&it.load.c.binary)),
        || drop(ran(&it.bare.c.binary)),
    );
}

/// Свидетели: чем доказано, что сравниваются коды, а не строки сборки.
fn witnesses(backend: Option<&Backend>, it: &Stand) {
    let (Some(backend), Some(llvm), Some(llvm_floor)) = (backend, &it.load.llvm, &it.floor.llvm)
    else {
        return;
    };
    // Счёт вызовов внутри горячей функции соседа - там же, где у наших сторон:
    // строка «сосед быстрее» читалась бы иначе, окажись у него на витке вызов.
    harness::hot_function(
        "капстоун",
        "сосед",
        &backend.tools,
        &it.them,
        harness::HOT_C,
    );
    // И то же самое у **витка**, а не у точки входа: сам `churning` у всех
    // троих лежит отдельной функцией, зовомой один раз, и вызова внутри неё не
    // должно быть ни у кого.
    hot_window("C", &backend.tools, &it.load.c.binary);
    hot_window("LLVM", &backend.tools, &llvm.binary);
    hot_window("сосед", &backend.tools, &it.them);
    harness::witnesses(
        "капстоун",
        backend,
        &Column {
            llvm,
            llvm_floor,
            c: &it.load.c,
            c_floor: &it.floor.c,
            ll: &it.load.ll,
        },
        |stem, pipeline, support| {
            let side = backend.load(
                stem,
                both(&it.load.source)
                    .llvm
                    .as_ref()
                    .expect("эмиттер капстоун уже взял выше"),
                pipeline,
                support,
            );
            let side_floor = backend.load(
                &format!("{stem}-floor"),
                both(&it.floor.source)
                    .llvm
                    .as_ref()
                    .expect("эмиттер пол уже взял выше"),
                pipeline,
                support,
            );
            (side, side_floor)
        },
        |stem| {
            let dir = harness::scratch(STAND);
            (
                Load::measured(
                    stem,
                    harness::built_apart(&dir, stem, &both(&it.load.source).c),
                ),
                Load::measured(
                    &format!("{stem}-floor"),
                    harness::built_apart(&dir, &format!("{stem}-floor"), &both(&it.floor.source).c),
                ),
            )
        },
    );
}

criterion_group!(benches, capstone);

fn main() {
    benches();
    Criterion::default().configure_from_args().final_summary();
}

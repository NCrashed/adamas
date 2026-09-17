//! Капстоун Фазы 7 (§9): обработчик пакетов под настоящими потоками.
//!
//! Договор трёх вычислителей капстоун проходит наравне со всем корпусом -
//! `agreement.rs` и `llvm.rs` держат его без единой строки здесь. Этот
//! свидетель показывает то, чего корпус не показывает по построению, и того
//! ровно два.
//!
//! *Круг питомника идёт на воркерах.* Корпусный прогон однопоточен: `mempool`
//! там один и тот же, но выдают из него по очереди. Под `ADAMAS_THREADS`
//! четыре задачи укладывают в одну **разделяемую** область одновременно, и
//! проверяется, что ответ от этого не меняется, а блоков не остаётся. Третье
//! наблюдаемое несущее: хотя бы один прогон обязан аллоцировать **на
//! воркере**, иначе «из нескольких воркеров» проверялось бы одним.
//!
//! *Ответ различает содержимое.* Программа, печатающая правдоподобное число,
//! доказывает меньше, чем кажется: перепутанное поле, потерянный разряд длины
//! и переставленные дорожки вектора дают такое же правдоподобное число.
//! Мутанты ниже - по одной правке **исходника** на каждый из трёх путей, - и
//! каждая обязана ответ сдвинуть.
//!
//! # Чего здесь нет, и это названо
//!
//! Утверждения «область одна» тут нет, и капстоун его не доказывает: ни один
//! воркер не читает чужую ячейку, а на своей копии обычная область ответила бы
//! то же. Доказывает его различающая программа трека B (`tests/shared.rs`),
//! живущая там, где машины нет. Здесь взамен проверяется соседнее и тоже
//! проверяемое: разделяемая область даёт **тот же** ответ, что обычная, - то
//! есть капстоун к выбору стратегии безразличен, и оттого остался программой
//! корпуса.

mod harness;

/// Сколько раз гонять каждую многопоточную программу.
///
/// То же число и по той же причине, что в `threads.rs` и `shared.rs`:
/// планировщик разводит файберы по-разному, и один зелёный прогон значит «в
/// этот раз повезло».
const RUNS: usize = 24;

/// Сколько воркеров у круга.
const THREADS: &str = "4";

/// Наименьший размер капстоуна: §9 требует от demo target'а пятисот строк, а
/// милестоун фазы - программы, в которой подсистемы встречаются. Число здесь
/// стоит затем же, зачем оно стоит у капстоуна Фазы 6: утверждение, ничем не
/// меряемое, тихо перестаёт быть правдой при первой же чистке фикстуры.
const LINES: usize = 500;

/// Исходник капстоуна.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отсутствие капстоуна означает сломанный корпус"
)]
fn capstone() -> String {
    std::fs::read_to_string(harness::corpus().join("packets.adamas"))
        .expect("фикстура `packets` обязана читаться")
}

/// Капстоун лежит в корпусе и не усох.
#[test]
fn the_capstone_is_a_corpus_program() {
    let source = capstone();
    let lines = source.lines().count();
    assert!(
        lines >= LINES,
        "капстоун усох до {lines} строк при {LINES} по §9"
    );
    // Пять подсистем названы поимённо: пропади любая, и «трогает их вместе»
    // перестало бы быть правдой, а прогон остался бы зелёным.
    for marker in [
        "arrayNew",
        "shlUInt64",
        "simdLoad",
        "sharedNew",
        "withNursery",
    ] {
        assert!(
            source.contains(marker),
            "капстоун потерял `{marker}`: подсистема ушла из программы"
        );
    }
}

/// Четыре воркера над одной разделяемой областью: ответ тот же, блоков ноль.
#[test]
fn the_capstone_runs_on_several_workers() {
    let source = capstone();
    let expected = harness::machine_printed(&source)
        .unwrap_or_else(|why| panic!("машина обязана отвечать, а сказала `{why}`"));
    let mut spread = 0;
    for run in 0..RUNS {
        let ran =
            harness::c_printed_with("capstone.threads", &source, &[("ADAMAS_THREADS", THREADS)]);
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
    eprintln!("капстоун на {THREADS} потоках (C): {RUNS} прогонов, {spread} с работой на воркере");
}

/// Он же на LLVM-пути: тот же текст, те же потоки, тот же ответ.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_llvm_capstone_runs_on_several_workers() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = adamas_codegen::llvm::Pipeline::optimised();
    let source = capstone();
    let expected = harness::machine_printed(&source).expect("машина обязана отвечать");
    let artefacts =
        harness::llvm_text("капстоун", &source).expect("капстоун обязан браться эмиттером");
    let binary = harness::llvm_binary("capstone.threads.llvm", &artefacts, &tools, &pipeline);

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
        let (_, live) = harness::blocks("капстоун", counted.lines().next().unwrap_or_default());
        assert_eq!(live, 0, "LLVM-путь: прогон {run} оставил блоки живыми");
        if counted.contains("потоков выдавало") {
            spread += 1;
        }
    }
    eprintln!(
        "капстоун на {THREADS} потоках (LLVM): {RUNS} прогонов, {spread} с работой на воркере"
    );
}

/// Мутанты: одна правка исходника на каждый путь, и каждая меняет ответ.
///
/// Правятся **строки программы**, а не порождённый код: у капстоуна проверяется
/// не эмиттер (его проверяют мутанты `llvm.rs`), а то, что ответ зависит от
/// содержимого пакета. Правка, не нашедшаяся в тексте, роняет тест наравне с
/// правкой, ничего не изменившей: мутант, который не применился, доказывает не
/// больше, чем мутант, который не убил.
#[test]
fn the_answer_depends_on_what_is_in_the_packet() {
    let source = capstone();
    let honest = harness::machine_printed(&source)
        .unwrap_or_else(|why| panic!("машина обязана отвечать, а сказала `{why}`"));
    let mutants: [(&str, &str, &str); 4] = [
        (
            "перепутанное поле: время жизни читается со смещения протокола",
            "  ttl c1 = field c1 56 8",
            "  ttl c1 = field c1 48 8",
        ),
        (
            "потерянный разряд: длина читается восемью битами вместо шестнадцати",
            "  length c0 = field c0 32 16",
            "  length c0 = field c0 32 8",
        ),
        (
            "переставленные дорожки: нулевая и первая полосы свёртки обменялись",
            "    (subUInt64 (simdLane v 2) (subUInt64 (simdLane v 1) (simdLane v 0)))",
            "    (subUInt64 (simdLane v 2) (subUInt64 (simdLane v 0) (simdLane v 1)))",
        ),
        (
            "потерянное слово нагрузки: седьмая ячейка пакета не заполняется",
            "  arraySet a6 (addUInt64 base 7) (grain seed (addUInt64 base 7))",
            "  arraySet a6 (addUInt64 base 7) zero",
        ),
    ];
    for (why, from, to) in mutants {
        assert!(
            source.contains(from),
            "мутант «{why}» не применился: `{from}` в исходнике не встречается"
        );
        let broken = source.replace(from, to);
        let printed = harness::machine_printed(&broken)
            .unwrap_or_else(|reason| panic!("мутант «{why}» не считается: {reason}"));
        assert_ne!(printed, honest, "мутант «{why}» ответ не сдвинул");
        eprintln!("мутант «{why}» убит");
    }
}

/// Разделяемая область даёт тот же ответ, что обычная.
///
/// Мутант здесь - **обычная область дословно**, и утверждение у него своё:
/// капстоун к выбору стратегии безразличен. Именно это и делает его программой
/// корпуса: программа, которая различает область-значение и область-тождество,
/// договором трёх вычислителей не берётся вовсе (см. шапку).
#[test]
fn the_shared_arena_answers_what_a_plain_one_answers() {
    let source = capstone();
    let honest =
        harness::c_printed_with("capstone.shared", &source, &[("ADAMAS_THREADS", THREADS)]);
    let plain = source.replace("  new u = sharedNew", "  new u = regionNew");
    assert_ne!(plain, source, "мутант не применился: `sharedNew` не найден");
    let other = harness::c_printed_with("capstone.plain", &plain, &[("ADAMAS_THREADS", THREADS)]);
    assert_eq!(
        other.printed, honest.printed,
        "обычная область ответила иначе: капстоун различает тождество и значение, \
         а такая программа корпусом не берётся"
    );
    assert_eq!(other.live, Some(0), "обычная область оставила блоки живыми");
}

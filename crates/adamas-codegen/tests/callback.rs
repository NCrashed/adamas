//! Экспорт доходит до ответа обоими понижениями (§5.3, трек C волны 3 Фазы 8).
//!
//! Свидетель отвечает на один вопрос: **печатает ли эмиттер обёртку экспорта
//! так, что настоящая чужая функция зовёт наше определение и программа
//! отвечает верно**. Проверяется прогоном до линковки и до ответа, а не чтением
//! `.ll`: разбор текстового IR принимает неизвестное имя молча, и для границы
//! этот жанр опаснее обычного - ошибиться в ней может только линковка и ABI.
//!
//! Программа - фикстура корпуса `tests/golden/eval/qsort.adamas`, а не строка
//! здесь, и стоит она в `eval/`, а не в `programs/`: ответ сходится у **всех
//! трёх** вычислителей, и договор корпуса держит это наравне со всем прочим
//! (`agreement.rs`, `llvm.rs`). Здесь проверяется то, чего договор не видит, -
//! форма напечатанного и отказы понижения.
//!
//! Чужая сторона здесь - **libc**: `qsort` уровня 1 и есть то, что §5.3
//! называет покрытым голым указателем на функцию. Своего объектника свидетелю
//! поэтому не нужно.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::Path;

use adamas_codegen::llvm::Pipeline;

/// Ответ программы: `[3, 1, 4, 2]` уезжает в `qsort` и приезжает `[1, 2, 3, 4]`.
///
/// Записан здесь **не вместо** машины, а рядом с ней: машина эту программу
/// считает (`agreement.rs`), и ответ её тот же. Число названо потому, что оно
/// показывает, чем свидетель ловит неверный колбэк: не позови `qsort` наше
/// определение ни разу - вышло бы `3142`, переверни знак - `4321`.
const ANSWER: &str = "1234";

/// Программа корпуса, а не строка здесь.
fn source() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval/qsort.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Понижение в C доходит до ответа.
#[test]
fn the_c_lowering_exports_the_callback() {
    let text = harness::text(&source()).expect("понижение обязано взять экспорт");
    let (stdout, stderr) = harness::built_with("callback", &text, &[]);
    assert_eq!(stdout.trim_end(), ANSWER, "C посчитал не то");
    let (_, live) = harness::blocks("callback", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Понижение в текстовый `.ll` доходит до ответа - обеими цепочками.
#[test]
fn both_llvm_toolchains_export_the_callback() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts =
        harness::llvm_text("callback", &source()).expect("понижение обязано взять экспорт");
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("callback-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), ANSWER, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("callback", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Обёртка печатается **один раз на символ**, а не на место, где едет адрес.
///
/// У C её три упоминания: объявление с меткой, заголовок определения и взятие
/// адреса. Объяви её дважды - `-Werror` этого не поймает (повторное совместимое
/// объявление законно), а свидетель формы поймает.
#[test]
fn an_exported_symbol_is_defined_once() {
    let text = harness::text(&source()).expect("понижение обязано взять экспорт");
    let declared = text
        .lines()
        .filter(|line| line.contains("adamas_export_byWord") && line.contains("__asm__"))
        .count();
    assert_eq!(declared, 1, "объявление напечатано {declared} раз(а)");
    let mentioned = text.matches("adamas_export_byWord").count();
    assert_eq!(
        mentioned, 3,
        "упоминаний ожидалось три: объявление, определение и взятие адреса"
    );
    // Символ у линкера - написанное имя, а внутри единицы его нет вовсе:
    // системный заголовок вправе занять его собой (тот же довод, что у
    // `emit_c::prototypes`).
    assert!(
        text.contains("__asm__(\"byWord\")"),
        "метка символа не напечатана"
    );
}

/// `.ll` определяет обёртку внешней, сишным соглашением, и зовёт внутреннюю
/// своим.
///
/// Сверяется текстом, а не прогоном, и это здесь законно: прогон выше уже
/// показал, что связка работает, а эти две строки говорят **почему** - если
/// соглашение у определения окажется `tailcc`, чужая сторона позовёт его по
/// чужому ABI, и поймает это не разбор, а поведение.
#[test]
fn the_llvm_wrapper_is_external_and_calls_by_the_inner_convention() {
    let artefacts =
        harness::llvm_text("callback", &source()).expect("понижение обязано взять экспорт");
    let defined = artefacts
        .ll
        .lines()
        .filter(|line| line.starts_with("define") && line.contains("@byWord("))
        .collect::<Vec<_>>();
    assert_eq!(
        defined.len(),
        1,
        "обёртка определена {} раз(а)",
        defined.len()
    );
    assert!(
        !defined[0].contains("tailcc") && !defined[0].contains("internal"),
        "обёртка обязана быть внешней и сишного соглашения: {}",
        defined[0]
    );
    assert!(
        artefacts.ll.contains("ptrtoint ptr @byWord to i64"),
        "адрес обёртки не берётся"
    );
}

/// Замыкание в позиции колбэка отвергается названной причиной.
///
/// Тип его пропускает - форма та же, - а уровень 1 берёт голый указатель, при
/// котором среды нет вовсе. Отказ стоит у понижения, а не у элаборации: тип
/// здесь верен, неверна **форма значения**, и знает её тот, кто её строит.
#[test]
fn a_lambda_in_the_callback_position_is_refused() {
    let text = source().replace("qsort xs 4 8 byWord", "qsort xs 4 8 (\\a b -> byWord a b)");
    let said = harness::text(&text).expect_err("замыкание в позиции колбэка обязано отказать");
    let said = said.to_string();
    assert!(
        said.contains("в позиции колбэка стоит не имя") && said.contains("userdata"),
        "отказ обязан назвать причину и место среды: {said}"
    );
}

/// Имя без `export` в позиции колбэка отвергается названной причиной.
///
/// Разница с предыдущим свидетелем не косметическая: здесь форма значения
/// **та самая**, а символа у линкера нет, и молча взять адрес было бы нечем.
#[test]
fn a_name_without_an_export_is_refused() {
    let text = source().replace("export \"C\" fn byWord\n", "");
    let said = harness::text(&text).expect_err("имя без экспорта обязано отказать");
    let said = said.to_string();
    assert!(
        said.contains("не объявленное `export \"C\"`"),
        "отказ обязан сказать, чего у имени нет: {said}"
    );
}

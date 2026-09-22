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

/// Программа корпуса, где регистрация **переживает** чужой вызов (§5.3,
/// уровень 3).
fn outliving() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval/callback-outlives.adamas");
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

/// Замыкание в позиции колбэка у API **без** `userdata` отвергается.
///
/// Волна 3 легализовала замыкание (уровень 2), но легализовала его вместе со
/// вторым словом: среде нужно место, и место это пишет автор. `qsort` его не
/// принимает - это и есть граница между уровнями, - поэтому отказ здесь остался,
/// а причина у него теперь другая и названа ею.
#[test]
fn a_lambda_without_a_userdata_slot_is_refused() {
    let text = source().replace("qsort xs 4 8 byWord", "qsort xs 4 8 (\\a b -> byWord a b)");
    let said = harness::text(&text).expect_err("замыкание без места под среду обязано отказать");
    let said = said.to_string();
    assert!(
        said.contains("класть её некуда") && said.contains("callbackEnv"),
        "отказ обязан назвать причину и место среды: {said}"
    );
}

/// Колбэк уровня 3: понижение и машина отвечают одно (§5.3).
///
/// Свидетель тут нужен не ради ответа как такового, а ради **предела таблицы**.
/// Машина держит свою таблицу трамплинов, понижение - сишную
/// (`adamas-codegen/src/callback.c`), и числа слотов у них записаны порознь.
/// Разойдись они - пятая регистрация у одного отдала бы адрес, у другого ноль,
/// и программа посчитала бы разное. Ответ фикстуры это ловит четвёртым
/// разрядом; корпусной прогон согласия его тоже ловит, но идёт минутами и в
/// наборы мутантов не входит.
#[test]
fn a_registered_callback_agrees_with_the_machine() {
    let stderr = harness::agreed("callback-outlives", &outliving())
        .expect("понижение обязано взять уровень 3");
    let (_, live) = harness::blocks("callback-outlives", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Снятие регистрации стоит **после** последнего чужого вызова.
///
/// Это и есть разница между уровнем 2 и уровнем 3, и ответом она не
/// наблюдается: у понижения адрес экспорта есть настоящий сишный символ, и
/// позови чужая сторона его после снятия слота - он всё равно сработал бы.
/// Наблюдается разница порядком строк, и наблюдать её надо здесь: у машины та
/// же ошибка даёт отказ, то есть два вычислителя ловят одно разными способами.
#[test]
fn the_registration_outlives_the_foreign_call() {
    let text = harness::text(&outliving()).expect("понижение обязано взять уровень 3");
    let lines: Vec<&str> = text.lines().collect();
    let called = |needle: &str| {
        lines
            .iter()
            .rposition(|line| line.contains(needle) && !line.starts_with("extern "))
    };
    let sorted = called("adamas_foreign_qsort(").expect("вызов `qsort` напечатан");
    let released =
        called("adamas_foreign_adamas_callback_release(").expect("снятие регистрации напечатано");
    assert!(
        released > sorted,
        "регистрация снята до чужого вызова: {released} против {sorted}"
    );
}

/// Таблица трамплинов печатается только той программе, которая её зовёт.
///
/// Половина вторая обязательна: печатай её всем, и `qsort`-программа получила
/// бы четыре слота статики и два символа рантайма, которых не просила.
#[test]
fn the_trampoline_table_is_printed_on_demand() {
    let with = harness::text(&outliving()).expect("понижение обязано взять уровень 3");
    assert!(
        with.contains("adamas_callback_table"),
        "таблица не напечатана программе, которая её зовёт"
    );
    let without = harness::text(&source()).expect("понижение обязано взять экспорт");
    assert!(
        !without.contains("adamas_callback_table"),
        "таблица напечатана программе, которая её не зовёт"
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

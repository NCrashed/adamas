//! Колбэк уровня 2: среда замыкания и вектор evidence едут в `userdata` (§5.3).
//!
//! Свидетель отвечает на два вопроса, и второй из них - довод самого §5.3.
//!
//! 1. **Доходит ли среда.** Замыкание с захваченным массивом уезжает в
//!    `qsort_r` пятым словом, чужая сторона зовёт наш трамплин, трамплин
//!    достаёт замыкание из `userdata`. Потеряйся среда - ширина сравнения
//!    стала бы мусором.
//! 2. **Доходит ли вектор evidence.** Компаратор производит **настоящую**
//!    операцию, площадка которой стоит снаружи чужого вызова. Найти её изнутри
//!    колбэка можно только по вектору, приехавшему в том же `userdata`, и это
//!    ровно то, что §5.3 называет своим доводом: «evidence translation делает
//!    evidence значением, а не позицией в стеке».
//!
//! # Платформа объявлена, а не подразумевается
//!
//! `qsort_r` - единственная пара «указатель на функцию плюс `void *`» в libc,
//! которую можно позвать, не заводя потока, и порядок аргументов у неё
//! **разный** у glibc и у Darwin: там переставлены четвёртое и пятое слова, а
//! компаратор получает `userdata` первым аргументом. Выразить оба порядка
//! одним файлом язык не умеет, поэтому фикстура стоит не в корпусе `eval/`, а
//! рядом (`tests/golden/programs`), и свидетель объявлен линуксовым. Молчаливый
//! пропуск был бы обманчивым свидетелем; здесь пропуска нет - есть `cfg`,
//! видимый в исходнике.
//!
//! # Мутанты, которыми это мерено (2026-09-21)
//!
//! Снято на каждой правке порознь, с возвратом между ними. Полная таблица -
//! `docs/phase8-w3-trackD-notes.md`.

#![cfg(target_os = "linux")]
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::Path;

use adamas_codegen::llvm::Pipeline;

/// Ответ фикстуры со средой: `1234` - перестановка нашего массива чужой
/// стороной, младший разряд `8` - захваченная ширина, прочитанная **после**
/// вызова.
const CARRIED: &str = "12348";

/// Ответ фикстуры с операцией: та же перестановка, ширина приходит операцией.
const PERFORMED: &str = "1234";

fn fixture(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/programs")
        .join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Среда доходит до чужой стороны, и ответ у понижения тот же, что у машины.
///
/// [`harness::agreed`] сверяет C с машиной сам; здесь остаётся сказать, что
/// блоков живыми не остаётся - среда есть объект кучи, и дроп её стоит **после**
/// чужого вызова, а не до.
#[test]
fn the_c_lowering_and_the_machine_agree_on_the_environment() {
    let stderr = harness::agreed("userdata", &fixture("qsort-r-userdata.adamas"))
        .expect("понижение обязано взять колбэк со средой");
    let (_, live) = harness::blocks("userdata", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// То же обеими цепочками LLVM.
#[test]
fn both_llvm_toolchains_carry_the_environment() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("userdata", &fixture("qsort-r-userdata.adamas"))
        .expect("понижение обязано взять колбэк со средой");
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("userdata-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), CARRIED, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("userdata", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Среда **читается** через `userdata`, а не угадывается.
///
/// Утверждение о паре: та же программа с нулём в захваченной ячейке отвечает
/// иначе. Без этой половины ответ `12348` был бы зелен и у колбэка, которому
/// среда не доехала вовсе, - `memcmp` с мусорной длиной вправе случайно дать
/// тот же порядок, а вот **разные** ответы на разной среде подделать нечем.
#[test]
fn the_environment_is_read_and_not_guessed() {
    let source = fixture("qsort-r-userdata.adamas").replace("eight = 8", "eight = 0");
    // Ширина ноль: `memcmp` отвечает нулём всегда, порядок остаётся прежним
    // (`3142`), и младший разряд читает ту же нулевую ячейку.
    let text = harness::text(&source).expect("понижение обязано взять колбэк со средой");
    let (stdout, stderr) = harness::built_with("userdata-zero", &text, &[]);
    assert_eq!(stdout.trim_end(), "31420", "среда доехала не та");
    let (_, live) = harness::blocks("userdata-zero", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
    // И машина отвечает то же: договор трёх вычислителей держится на обеих
    // средах, а не на одной.
    let said = harness::machine_printed(&source).expect("машина обязана посчитать");
    assert_eq!(said, "31420", "машина посчитала не то");
}

/// Вектор evidence доходит: операция внутри колбэка находит свою площадку.
///
/// Площадка стоит **снаружи** чужого вызова, и другого пути к ней у колбэка
/// нет: стек продолжения у трамплина свой, свежий.
#[test]
fn the_evidence_vector_rides_in_the_userdata() {
    let text = harness::text(&fixture("qsort-r-evidence.adamas"))
        .expect("понижение обязано взять колбэк с операцией");
    let (stdout, stderr) = harness::built_with("evidence", &text, &[]);
    assert_eq!(stdout.trim_end(), PERFORMED, "C посчитал не то");
    let (_, live) = harness::blocks("evidence", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// То же обеими цепочками LLVM.
#[test]
fn both_llvm_toolchains_carry_the_evidence() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("evidence", &fixture("qsort-r-evidence.adamas"))
        .expect("понижение обязано взять колбэк с операцией");
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("evidence-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), PERFORMED, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("evidence", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Машина ту же программу **не** считает, и отказ у неё называет причину.
///
/// Это расхождение вычислителей на написуемой программе, и записано оно
/// свидетелем, а не памятью: колбэк у машины идёт отдельным прогоном
/// (`callback::answered` зовёт `run_linked`), и стек хендлеров места
/// регистрации тому прогону не виден. Начни машина считать - свидетель
/// покраснеет, и расхождение будет снято сознательно, а не молча.
#[test]
fn the_machine_names_the_handler_it_cannot_see() {
    let said = harness::machine_printed(&fixture("qsort-r-evidence.adamas"))
        .expect_err("машина обязана отказать на операции внутри колбэка");
    assert!(
        said.contains("отдельным прогоном") && said.contains("userdata"),
        "отказ обязан назвать причину расхождения: {said}"
    );
}

/// `callbackEnv` без колбэка со средой - отказ.
#[test]
fn a_userdata_slot_without_a_closure_is_refused() {
    let text = fixture("qsort-r-userdata.adamas").replace(
        "(\\a b -> memcmp a b (arrayIndex widths 0))",
        "compareByWord",
    );
    let text = text.replace(
        "runForeign : ",
        "compareByWord : CPtr -> CPtr -> {Foreign} Int32\n\
         compareByWord a b = memcmp a b 8\n\
         \n\
         export \"C\" fn compareByWord\n\
         \n\
         runForeign : ",
    );
    let said = harness::text(&text).expect_err("`callbackEnv` без среды обязан отказать");
    let said = said.to_string();
    assert!(
        said.contains("`callbackEnv` написан") && said.contains("уровень 1 среды не несёт"),
        "отказ обязан сказать, чего в вызове нет: {said}"
    );
}

/// Правило чужого кадра стоит **на объявлении** колбэка (§5.3).
///
/// Уровень 1 проверял его на `export`; у уровня 2 экспорта нет вовсе - наружу
/// едет трамплин, - и единственное место, где row колбэка написана, есть само
/// объявление `extern`. Отказ приходит готовым текстом от анализа §3.4.
#[test]
fn the_foreign_frame_rule_guards_the_declaration() {
    let text = fixture("qsort-r-evidence.adamas")
        .replace("  width -> resume (arrayNew 1 eight)", "  width -> blank");
    let said = harness::rejected(&text);
    assert!(
        said.contains("в позиции колбэка") && said.contains("абортивный"),
        "отказ обязан назвать эффект и вердикт его хендлера: {said}"
    );
}

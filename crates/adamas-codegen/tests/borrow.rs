//! Счётчик одолженного массива, пока внутри чужого вызова бежит наш колбэк
//! (§10 вопрос 184).
//!
//! Вопрос 184 назвал обстоятельство, на котором держится безопасность
//! `rc == 0`: «`Expr::Foreign` не точка приостановки, между входом и возвратом
//! ничего нашего не бежит». Колбэк это обстоятельство снимает. Свидетель
//! измеряет, что после снятия остаётся.
//!
//! Утверждений два, и второе сильнее первого:
//!
//! 1. предусловие 184 **переживает** колбэк: у массива, одолженного владением,
//!    счётчик равен нулю в тот самый момент, когда бежит наш код;
//! 2. следствие 184 - нет: назвать одолженный массив изнутри колбэка можно
//!    только захватом, а захват берёт ссылку, и счётчик становится единицей.
//!
//! Обе половины меряются **одной** программой и одной чужой функцией:
//! различаются они ровно тем, называет ли замыкание одолженный массив.
//!
//! Машины здесь нет по той же причине, что у `lending.rs`: чужая сторона -
//! объектник этого теста, а `adamas eval` ищет символ `dlopen`'ом.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::{Path, PathBuf};
use std::process::Command;

use adamas_codegen::llvm::Pipeline;

/// Ответ программы.
///
/// Младшие три разряда - первая половина: счётчик `0` до колбэка, `0` после,
/// тег сверен (`001`). Старшие - вторая: счётчик `1` до, `1` после, тег сверен
/// (`111`).
///
/// Ноль в первой половине и есть предусловие вопроса 184, а единица во второй -
/// ответ ему: захват, без которого одолженный массив изнутри колбэка не
/// назвать, счётчик и поднимает.
const ANSWER: &str = "111001";

fn source() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/programs/borrow-under-a-callback.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Текст чужой стороны: он же собирается отдельным объектником для C-пути.
fn shim() -> String {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/borrow.c");
    std::fs::read_to_string(&source).expect("исходник чужой библиотеки на месте")
}

/// Чужая сторона отдельной единицей трансляции.
fn shim_object() -> PathBuf {
    let dir = harness::scratch();
    let object = dir.join("borrow-probe.o");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/borrow.c");
    let built = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1", "-Wall", "-c"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "чужая библиотека не собралась:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    object
}

/// Счётчик, прочитанный чужой стороной, пока бежит наш колбэк.
#[test]
fn the_counter_is_read_while_our_code_runs() {
    let text = harness::text(&source()).expect("понижение обязано взять заём под колбэком");
    let object = shim_object();
    let (stdout, stderr) = harness::built_with(
        "borrow",
        &text,
        &[object.to_str().expect("путь объектника не UTF-8")],
    );
    assert_eq!(stdout.trim_end(), ANSWER, "C посчитал не то");
    let (_, live) = harness::blocks("borrow", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// То же обеими цепочками LLVM.
#[test]
fn both_llvm_toolchains_read_the_same_counter() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let mut artefacts =
        harness::llvm_text("borrow", &source()).expect("понижение обязано взять заём под колбэком");
    artefacts.support.push_str(&shim());
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("borrow-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), ANSWER, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("borrow", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Обе половины - **займы**, а не копии.
///
/// Без этой строки числа выше читались бы иначе: счётчик, прочитанный по адресу
/// копии, сказал бы про копию, и разница `0` против `1` означала бы что угодно.
/// Займов ровно два, копирующего `adamas_array_writable` нет ни одного.
#[test]
fn both_halves_lend_and_do_not_copy() {
    let text = harness::text(&source()).expect("понижение обязано взять заём под колбэком");
    let loans = text.matches("adamas_array_data(").count();
    assert_eq!(loans, 2, "займов напечатано {loans}, а не два");
    assert!(
        !text.contains("adamas_array_writable("),
        "заём скопировал блок: в тексте есть `adamas_array_writable`"
    );
}

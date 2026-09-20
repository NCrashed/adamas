//! Владение одолженным буфером, наблюдаемое **с той стороны** границы
//! (§5.3, §5.1, §10 вопрос 149; трек A волны 2 Фазы 8).
//!
//! Свидетель существует потому, что на вопрос «что со счётчиком, пока чужая
//! сторона держит указатель» нельзя ответить чтением кода: ответ зависит от
//! того, нужен ли массив после займа, и обе ветки надо предъявить числом.
//! Читает его чужая сторона у нашего заголовка - спутник
//! `tests/shim/ownership.c` про смещение нагрузки знает нарочно.
//!
//! Печать здесь не спрашивается ни разу: `dup` перед вызовом и дроп после него
//! в тексте видно, но видно и то, что текст **можно прочесть неверно**. Число,
//! прочитанное из заголовка в тот самый момент, когда чужая сторона в него
//! смотрит, прочесть неверно нельзя.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::{Path, PathBuf};
use std::process::Command;

use adamas_codegen::llvm::Pipeline;

/// Ответ программы, поразрядно.
///
/// * единицы - `rc` массива, который нужен и после займа: **1**, лишняя ссылка;
/// * десятки - тег блока по одолженному адресу сошёлся: **1**;
/// * сотни - `rc` массива, чьё последнее употребление есть заём: **0**, то есть
///   рантайм зовёт его уникальным, пока чужая сторона в него пишет;
/// * тысячи - чужая сторона удержала адрес: **1**;
/// * десятки тысяч - следующий `arrayNew` той же длины получил **тот же блок**,
///   и удержанный адрес теперь адресует другое значение Adamas: **1**.
const ANSWER: &str = "11011";

fn source() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/programs/extern-buffer-owned.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

fn shim() -> String {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/ownership.c");
    std::fs::read_to_string(&source).expect("исходник чужой библиотеки на месте")
}

fn shim_object() -> PathBuf {
    let dir = harness::scratch();
    let object = dir.join("ownership-probe.o");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/ownership.c");
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

/// Счётчик, тег и удержанный адрес, прочитанные чужой стороной, - C-понижение.
#[test]
fn the_far_side_reads_our_counter() {
    let text = harness::text(&source()).expect("понижение обязано взять одолженный буфер");
    let object = shim_object();
    let (stdout, stderr) = harness::built_with(
        "ownership",
        &text,
        &[object.to_str().expect("путь объектника не UTF-8")],
    );
    assert_eq!(stdout.trim_end(), ANSWER, "C посчитал не то");
    let (_, live) = harness::blocks("ownership", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// То же у текстового `.ll`, обеими цепочками.
///
/// Обязательно врозь: владение считает один проход на оба понижения
/// (`perceus`), но **печатают** дроп после чужого вызова два разных эмиттера, и
/// разъехаться им есть где.
#[test]
fn both_llvm_toolchains_keep_the_same_ownership() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let mut artefacts =
        harness::llvm_text("ownership", &source()).expect("понижение обязано взять буфер");
    artefacts.support.push_str(&shim());
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("ownership-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), ANSWER, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("ownership", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Лишняя ссылка берётся ровно там, где массив нужен после займа.
///
/// Форму спрашиваем **в дополнение** к числу: число говорит, каков `rc`, а эта
/// строка - что он таков не случайно. Пара `dup`/`drop` вокруг займа стоит
/// денег (две записи счётчика на пересечение), и молча появившаяся третья
/// осталась бы незамеченной.
#[test]
fn the_extra_reference_is_taken_once_per_kept_loan() {
    let text = harness::text(&source()).expect("понижение обязано взять одолженный буфер");
    // Займов пять, а `dup` - один: четыре массива из пяти уезжают владением.
    let loans = text.matches("adamas_array_data(").count();
    assert_eq!(loans, 5, "займов напечатано {loans}, а не пять");
    let duplicated = text.matches("adamas_dup(").count();
    assert_eq!(
        duplicated, 1,
        "лишних ссылок {duplicated}, а ожидалась одна - у массива, нужного после займа"
    );
}

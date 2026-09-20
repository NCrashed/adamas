//! Буфер, одолженный чужой стороне, доходит до ответа обоими понижениями
//! (§5.3, §4.11; трек A волны 2 Фазы 8).
//!
//! Свидетель отвечает на один вопрос: **есть ли то, что едет через границу,
//! адрес нагрузки нашего блока**. Ответ «да» нельзя подделать ни копией, ни
//! перекладкой чисел, и потому наблюдений три, каждое своим способом:
//!
//! 1. чужая сторона **пишет** в наш блок, и наша сторона читает написанное
//!    обычным `arrayIndex` (копия этого не дала бы);
//! 2. чужая сторона **читает** наш блок и кладёт ответ во второй наш блок -
//!    out-параметр, то есть `uLongf *destLen` у zlib;
//! 3. чужая сторона запоминает адрес и сверяет его со вторым займом того же
//!    массива (копия дала бы разные адреса).
//!
//! Проверяется **прогоном до линковки и до ответа**, а не чтением `.ll`: жанр
//! назван треком A волны 1 - неизвестное имя восемнадцатая версия принимает
//! молча, - и для одолженного буфера он опаснее обычного, потому что ошибка в
//! адресе даёт не отказ, а чтение чужой памяти с правдоподобным числом.
//!
//! Чего здесь нет: машины, и не потому, что она не умеет. Умеет с трека B
//! волны 2: массив у неё теперь плоский блок с адресом
//! (`adamas_core::value::Block`). Нет её здесь потому, что чужая сторона -
//! объектник этого теста, а `adamas eval` ищет символ `dlopen`'ом по
//! связанным библиотекам. Программа, которую считают все трое, стоит в корпусе
//! `eval/extern-buffer.adamas` и написана на символах libc.
//!
//! # Мутанты, которыми это мерено (2026-09-20)
//!
//! Снято на каждой правке порознь, с возвратом между ними; счёт - упавших
//! свидетелей этого файла. Полная таблица - `docs/phase8-w2-trackA-notes.md`.

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
/// `68` - сумма байт `5..=12`, которые чужая сторона написала в наш блок;
/// `12` - максимум оттуда же, приехавший out-параметром; две единицы - третий
/// байт равен семи и второй заём дал тот же адрес; `5` - число пересечений.
///
/// Число записано здесь, а не взято у машины: машина эту программу не считает
/// вовсе (см. шапку). Зато каждая его цифра - **арифметика чужой стороны** над
/// нашей памятью, и подменить её нечем: потеряй заём адрес, и сумма станет
/// нулём, а сверка адресов - нулём тем более.
const ANSWER: &str = "51112068";

/// Программа корпуса, а не строка здесь.
fn source() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/programs/extern-buffer-probe.adamas");
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Текст чужой стороны: он же собирается отдельным объектником для C-пути.
fn shim() -> String {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/buffer.c");
    std::fs::read_to_string(&source).expect("исходник чужой библиотеки на месте")
}

/// Чужая сторона: собирается **отдельной единицей трансляции**.
fn shim_object() -> PathBuf {
    let dir = harness::scratch();
    let object = dir.join("lending-buffer.o");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/shim/buffer.c");
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

/// Понижение в C доходит до ответа, и блоков живыми не остаётся.
///
/// Вторая половина не украшение: одолженный массив держится живым **до конца
/// вызова**, и держит его лишняя ссылка. Забудь вставка RC отдать её после
/// возврата - блок остался бы живым, и счётчик это назовёт.
#[test]
fn the_c_lowering_lends_the_buffer() {
    let text = harness::text(&source()).expect("понижение обязано взять одолженный буфер");
    let object = shim_object();
    let (stdout, stderr) = harness::built_with(
        "lending",
        &text,
        &[object.to_str().expect("путь объектника не UTF-8")],
    );
    assert_eq!(stdout.trim_end(), ANSWER, "C посчитал не то");
    let (_, live) = harness::blocks("lending", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Понижение в текстовый `.ll` доходит до того же ответа - обеими цепочками.
#[test]
fn both_llvm_toolchains_lend_the_buffer() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let mut artefacts =
        harness::llvm_text("lending", &source()).expect("понижение обязано взять одолженный буфер");
    artefacts.support.push_str(&shim());
    for (tag, tools) in [("cur", &current), ("min", &minimum)] {
        let (stdout, stderr) = harness::llvm_built(
            &format!("lending-{tag}"),
            &artefacts,
            tools,
            &Pipeline::optimised(),
        );
        assert_eq!(stdout.trim_end(), ANSWER, "{tag}: LLVM посчитал не то");
        let (_, live) = harness::blocks("lending", &stderr);
        assert_eq!(live, 0, "{tag}: прогон оставил блоки живыми");
    }
}

/// Заём печатается **вычислением адреса**, а не копией блока.
///
/// Спрашивается форма, а не поведение, и спрашивается потому, что поведение у
/// копии было бы то же самое у первых двух наблюдений: копия, отданная чужой
/// стороне и прочитанная обратно, дала бы ту же сумму. Различает их третье
/// наблюдение прогоном, а эта строка - печатью: `memcpy` у займа нет ни
/// одного, а `adamas_array_data` есть по одному на каждый одолженный буфер.
#[test]
fn the_loan_is_an_address_and_not_a_copy() {
    let text = harness::text(&source()).expect("понижение обязано взять одолженный буфер");
    // Пять займов: `fill`, `digest` (два - байты и out), `note`, `same`.
    let loans = text.matches("adamas_array_data(").count();
    assert_eq!(loans, 5, "займов напечатано {loans}, а не пять");
    // Копии блока под заём нет: `adamas_array_writable` зовёт только запись
    // ячейки, а её в фикстуре нет вовсе.
    assert!(
        !text.contains("adamas_array_writable("),
        "заём скопировал блок: в тексте есть `adamas_array_writable`"
    );
}

/// Одолженный массив переживает чужой вызов: дроп стоит **после** него.
///
/// Наблюдается порядком строк в порождённом C, а не ответом: ответ у
/// преждевременного дропа был бы тем же самым на этой платформе - блок
/// освобождённый, но ещё не переписанный, читается прежними байтами. Жанр тот
/// же, ради которого гоняются мутанты: правильный ответ из неверного порядка.
#[test]
fn the_lent_array_outlives_the_call() {
    let text = harness::text(&source()).expect("понижение обязано взять одолженный буфер");
    let lines: Vec<&str> = text.lines().collect();
    // Не первое вхождение: первым идёт **прототип**, а вызов стоит в теле.
    let call = lines
        .iter()
        .position(|line| {
            line.contains("adamas_foreign_adamas_probe_fill(") && !line.starts_with("extern ")
        })
        .expect("вызов `fill` напечатан");
    let released = lines[call + 1..]
        .iter()
        .take(4)
        .any(|line| line.contains("adamas_drop"));
    assert!(
        released,
        "после чужого вызова нет отдачи одолженного: строки {:?}",
        &lines[call..(call + 5).min(lines.len())]
    );
}

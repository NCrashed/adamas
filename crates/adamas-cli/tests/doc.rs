//! `adamas doc`: что попадает в документацию и что из неё выпадает (§7.1, §4.8).
//!
//! # Чем этот свидетель ломается
//!
//! Жанр подделки здесь ровно один и назван заранее (лог 2026-09-23): **маркер
//! без потребителя, который на нём краснеет**, ложится туда же, куда легло
//! существующее различение комментариев - пять упоминаний в дереве и ноль
//! разборов. Свидетель, спрашивающий «вывод непустой», зелен и у генератора,
//! который печатает всё подряд; поэтому здесь сверяется **множество
//! заголовков целиком**, и у каждого правила есть пара.
//!
//! Правил три, и все три отрицательные - то есть проверяются тем, чего в
//! выводе быть не должно:
//!
//! 1. Комментарий **без** маркера документацией не является.
//! 2. Блок, **отбитый пустой строкой**, не относится ни к чему.
//! 3. Имя, **скрытое `:>`**, снаружи не пишется, и документации у него нет,
//!    сколько бы её ни написал автор.
//!
//! Драйвер запускается **процессом**: `doc` обязан работать у того, кто его
//! вызывает из терминала, а не только у внутреннего вызова.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Корень корпуса.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

/// Фикстура, написанная под этот прогон.
fn documented() -> PathBuf {
    corpus().join("programs").join("documented.adamas")
}

/// Запускает `adamas doc` и отдаёт вывод без пути к файлу: путь зависит от
/// того, откуда запущен тест, а сверка - не должна.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn documentation(path: &Path) -> String {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .arg("doc")
        .arg(path)
        .env_remove("RUST_BACKTRACE")
        .env_remove("RUST_LIB_BACKTRACE")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "`doc` отказал: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    String::from_utf8(output.stdout)
        .unwrap()
        .replace(&path.display().to_string(), &name)
}

/// Заголовки разделов в порядке появления.
fn headings(text: &str) -> Vec<&str> {
    text.lines()
        .filter_map(|line| line.strip_prefix("## "))
        .collect()
}

#[test]
fn documentation_says_exactly_what_was_marked() {
    let text = documentation(&documented());
    assert_eq!(
        headings(&text),
        [
            "`data Nat`",
            "`Zero : Nat`",
            "`Succ : Nat -> Nat`",
            "`add : Nat -> Nat -> Nat`",
            "`Sealed.zero : T`",
            "`Sealed.next : T -> T`",
        ],
        "вывод целиком:\n{text}"
    );
}

#[test]
fn a_comment_without_the_marker_is_not_documentation() {
    // `double` в фикстуре несёт обычный `--` сверху. Правило «комментарий над
    // объявлением и есть документация» выдало бы его - и с ним шесть седьмых
    // корпуса, где сверху стоят ожидаемый ответ прогона, история правки и
    // ссылка в §10.
    let text = documentation(&documented());
    assert!(
        !text.contains("double"),
        "комментарий без маркера попал в документацию:\n{text}"
    );
}

#[test]
fn a_block_torn_off_by_a_blank_line_documents_nothing() {
    // Шапка фикстуры отбита от первого объявления пустой строкой. Прочти `doc`
    // блок поверх неё - и шапка стала бы документацией `data Nat`.
    let text = documentation(&documented());
    assert!(
        !text.contains("Эта шапка"),
        "шапка файла попала в документацию первого объявления:\n{text}"
    );
}

#[test]
fn a_name_hidden_by_sealing_has_no_documentation() {
    // `Sealed.twice` документирован автором и скрыт `:>` (§4.8). Снаружи его
    // имя не пишется вовсе, и документация о нём рассказывала бы читателю про
    // имя, которого у него нет.
    let text = documentation(&documented());
    assert!(
        !text.contains("twice"),
        "скрытое запечатыванием имя попало в документацию:\n{text}"
    );
    // Парный: сам модуль при этом документирован - иначе проверка выше была бы
    // зелена и у генератора, который пропускает запечатанные модули целиком.
    assert!(
        text.contains("Sealed.next"),
        "публичный член запечатанного модуля пропал:\n{text}"
    );
}

#[test]
fn the_headline_is_written_the_way_the_reader_writes_it() {
    // Написанный тип, а не элаборированный: ядро знает `add` как
    // `(ω _ : Nat) -> {| e0} (ω _ : Nat) -> {| e0} Nat`, и это верно, но
    // отвечает на другой вопрос. Читатель документации пишет `Nat -> Nat -> Nat`.
    let text = documentation(&documented());
    assert!(
        text.contains("`add : Nat -> Nat -> Nat`"),
        "заголовок обязан звучать так, как автор написал тип:\n{text}"
    );
}

#[test]
fn a_module_of_the_program_gets_its_own_section() {
    // Документируется программа, а не файл: подключённый модуль - такой же
    // предмет документации, и раздел у него свой, со своим путём.
    let text = documentation(&corpus().join("project").join("main.adamas"));
    assert!(
        text.contains("# Модуль `Std.Base`"),
        "подключённый модуль не получил раздела:\n{text}"
    );
}

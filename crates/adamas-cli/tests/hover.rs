//! Тип в подсказке и тип в терминале - один тип.
//!
//! §7.2 называет hover первой возможностью и требует **полного** типа. Обещание
//! «то же, что в терминале» держится тем, что путь один
//! ([`adamas_elab::cursor::described`]), но «держится по построению» -
//! не свидетель: вторая запись заводится незаметно, и проект платил за такие
//! пары четырежды за две волны.
//!
//! Поэтому драйвер **запускается процессом** на всём принятом корпусе, и
//! спрашивают у него ровно те имена, на которые ответила подсказка: **3290
//! имён в 137 фикстурах**. Совпало - значит в редакторе нет ни лишнего знака,
//! ни потерянного. (Было 3322: имена ищутся по тексту фикстуры, а
//! `eval/prelude.adamas` после выноса прелюдии в модуль пишет из неё только то,
//! чем считает.)
//!
//! # Программа, а не файл
//!
//! Проход здесь идёт по [`adamas_elab::program`] - тем же, каким идёт драйвер.
//! Иначе многофайловая фикстура выпадала бы из сверки целиком: имена, которые
//! `prelude.adamas` берёт из `Std/Prelude.adamas`, однофайловому проходу
//! неизвестны, и подсказка над ними молчит. Волна 2 Фазы 9 приспускала порог
//! корпуса со 137 до 136 ровно за это; здесь он вернулся.
//!
//! # Чего этот прогон **не** ловит
//!
//! Перевод позиций: имена сюда попадают уже найденными. Его ловят записанные
//! руками колонки в `crates/adamas-lsp/tests/protocol.rs`; разделение то же,
//! что у диагностики в `lsp.rs`.
//!
//! # Почему у `adamas check` появился `--type`
//!
//! Потому что печатать тип драйвер не умел вовсе: `check` печатал счёт
//! объявлений, а типы в сообщениях об отказе - **инстанцированные** местом
//! использования (`{| e0}` там приходит дыркой `?0`), то есть не те, что
//! показывает подсказка. Критерий «совпадает с тем, что печатает `adamas
//! check`» без этого флага нечем было бы взять.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str::FromStr as _;

use adamas_core::sig::DefinitionKind;
use adamas_core::source::SourceFile;
use adamas_elab::program::Program;
use adamas_lsp::Encoding;
use adamas_lsp::lsp_types::{HoverContents, Position, Uri};

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус либо окружение, и падать он должен громко"
)]
mod harness {
    use super::{Command, HoverContents, Path, PathBuf, Position, Program, SourceFile, corpus};
    use adamas_lsp::project::Buffers;

    pub(crate) fn fixtures(kind: &str) -> Vec<PathBuf> {
        let dir = corpus().join(kind);
        let mut found: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
            .collect();
        found.sort();
        assert!(!found.is_empty(), "корпус {} пуст", dir.display());
        found
    }

    pub(crate) fn source(path: &Path) -> SourceFile {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        SourceFile::new(name, std::fs::read_to_string(path).unwrap())
    }

    /// Проект фикстуры: корень поиска модулей - её каталог, как у драйвера.
    pub(crate) fn project(path: &Path) -> Buffers<'static> {
        Buffers::on_disk(path.parent().unwrap_or_else(|| Path::new(".")))
    }

    /// Проход по программе фикстуры - тот же, каким идёт `adamas check`.
    pub(crate) fn analysed(path: &Path, file: &SourceFile) -> Program {
        let entry = SourceFile::new(file.name(), file.text());
        adamas_elab::program::analyze(entry, &project(path))
    }

    /// Запрашивает у драйвера типы перечисленных имён - процессом.
    pub(crate) fn driven(path: &Path, names: &[String]) -> Vec<String> {
        let mut command = Command::new(env!("CARGO_BIN_EXE_adamas"));
        command.arg("check").arg(path);
        for name in names {
            command.arg("--type").arg(name);
        }
        let output = command
            .env_remove("RUST_BACKTRACE")
            .env_remove("RUST_LIB_BACKTRACE")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}: драйвер отказал\n{}",
            path.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .map(ToOwned::to_owned)
            .collect()
    }

    /// Текст подсказки над позицией - тем же вызовом, каким её шлёт сервер.
    ///
    /// Стоит он **полного прохода по файлу**, поэтому корпусная сверка ходит
    /// не им, а [`adamas_elab::cursor`] по одному разбору на фикстуру: 23 093
    /// проходов вместо 137 - это шесть минут против шести секунд. Что обёртка
    /// сервера к тексту ничего не добавляет, проверяется на каждой фикстуре
    /// отдельно (`the_server_adds_nothing_to_the_text`) и на записанных руками
    /// позициях в `crates/adamas-lsp/tests/protocol.rs`.
    pub(crate) fn hovered(path: &Path, file: &SourceFile, at: Position) -> Option<String> {
        let hover = adamas_lsp::hover(file, at, super::Encoding::Utf16, &project(path))?;
        match hover.contents {
            HoverContents::Markup(markup) => Some(markup.value),
            other => panic!("подсказка обязана быть разметкой: {other:?}"),
        }
    }

    /// Всё, что подсказка сказала бы о файле: имя -> строка `имя : тип`.
    ///
    /// Имена, которых драйверу не назвать, отсеиваются здесь же: сорт
    /// объявления не имеет, а поднятый имплисит живёт внутри чужого телескопа,
    /// и одноимённые в разных телескопах значат разное.
    pub(crate) fn everything(path: &Path, file: &SourceFile) -> super::BTreeMap<String, String> {
        let program = analysed(path, file);
        let (Some(unit), Some(signature)) = (program.units.first(), &program.signature) else {
            panic!("принятая фикстура отдаёт и дерево, и сигнатуру");
        };
        let Some(module) = &unit.module else {
            panic!("принятая фикстура разбирается");
        };
        let tokens = adamas_parser::tokenize(file.text()).expect("фикстура разбирается");
        let mut shown = super::BTreeMap::new();
        for token in &tokens.tokens {
            let Some(found) = adamas_elab::cursor::at(file.text(), module, token.span.start())
            else {
                continue;
            };
            let Some(value) = adamas_elab::cursor::shown(signature, &found) else {
                continue;
            };
            let (name, _) = value.split_once(" : ").unwrap_or((value.as_str(), ""));
            if signature.lookup(name).is_none() && adamas_core::prim::Prim::named(name).is_none() {
                continue;
            }
            if let Some(earlier) = shown.insert(name.to_owned(), value.clone()) {
                assert_eq!(earlier, value, "два ответа об имени `{name}`");
            }
        }
        shown
    }
}

use harness::{analysed, driven, everything, fixtures, hovered, source};

/// Всё, что подсказка сказала о корпусе, терминал повторяет дословно.
#[test]
fn every_hover_matches_the_driver() {
    let mut names = 0;
    let mut files = 0;
    for kind in ["programs", "eval"] {
        for path in fixtures(kind) {
            let file = source(&path);
            let shown = everything(&path, &file);
            let asked: Vec<String> = shown.keys().cloned().collect();
            if asked.is_empty() {
                continue;
            }
            let printed = driven(&path, &asked);
            assert_eq!(
                printed.len(),
                asked.len(),
                "{}: строк не столько, сколько имён",
                path.display()
            );
            for (name, line) in asked.iter().zip(&printed) {
                assert_eq!(line, &shown[name], "{}: имя `{name}`", path.display());
            }
            names += asked.len();
            files += 1;
        }
    }
    // Сто тридцать семь: многофайловая `eval/prelude.adamas` вернулась в
    // сверку вместе с проходом по программе. Приспущен порог был ровно на ней
    // и ровно на одну фикстуру.
    assert!(files >= 137, "корпус принятых усох до {files}");
    assert!(names >= 3260, "сверено имён всего {names}, а было 3290");
}

/// Тип в подсказке - **тот самый**, а не какой-нибудь.
///
/// Сверка с драйвером выше этого не ловит: обе стороны зовут одну функцию, и
/// сломай её - они сломаются вместе (проверено мутантом: `described`, всегда
/// печатающая `Nat`, оставляет ту сверку зелёной). Поэтому здесь свойство
/// **самого языка**, а не пути к нему: конструктор возвращает своё семейство,
/// значит его тип обязан это семейство упоминать. Роль конструктора берётся у
/// сигнатуры (`DefinitionKind`), а не у напечатанного типа.
#[test]
fn a_constructor_names_its_family_in_its_type() {
    let mut checked = 0;
    for kind in ["programs", "eval"] {
        for path in fixtures(kind) {
            let file = source(&path);
            let shown = everything(&path, &file);
            let signature = analysed(&path, &file)
                .signature
                .expect("принятая фикстура отдаёт сигнатуру");
            for name in signature.names() {
                let DefinitionKind::Constructor { data } = &signature
                    .lookup(&name)
                    .expect("имя из перечня объявлено")
                    .kind
                else {
                    continue;
                };
                let Some(value) = shown.get(&*name) else {
                    continue;
                };
                assert!(
                    value.contains(&**data),
                    "{}: `{name}` строит `{data}`, а подсказка говорит `{value}`",
                    path.display()
                );
                checked += 1;
            }
        }
    }
    assert!(checked >= 400, "конструкторов сверено всего {checked}");
}

/// Обёртка сервера к тексту ничего не добавляет и ничего не теряет.
///
/// На каждой фикстуре берётся первое имя, о котором есть что сказать, и
/// спрашивается **позицией**, как спрашивает редактор. Совпало с тем, что
/// сверял прогон выше, - значит корпусная сверка мерила то же, что увидит
/// человек.
#[test]
fn the_server_adds_nothing_to_the_text() {
    let mut checked = 0;
    for kind in ["programs", "eval"] {
        for path in fixtures(kind) {
            let file = source(&path);
            let program = analysed(&path, &file);
            let (Some(unit), Some(signature)) = (program.units.first(), &program.signature) else {
                panic!("{}: принятая фикстура молчит", path.display());
            };
            let Some(module) = &unit.module else {
                panic!("{}: принятая фикстура разбирается", path.display());
            };
            let tokens = adamas_parser::tokenize(file.text()).expect("фикстура разбирается");
            let first = tokens.tokens.iter().find_map(|token| {
                let found = adamas_elab::cursor::at(file.text(), module, token.span.start())?;
                let value = adamas_elab::cursor::shown(signature, &found)?;
                Some((token.span.start(), value))
            });
            let Some((offset, value)) = first else {
                continue;
            };
            let at = adamas_lsp::position::position(&file, offset, Encoding::Utf16)
                .expect("граница знака переводится");
            assert_eq!(
                hovered(&path, &file, at).as_deref(),
                Some(value.as_str()),
                "{}",
                path.display()
            );
            checked += 1;
        }
    }
    // Та же фикстура и тот же счёт, что у порога выше.
    assert!(checked >= 137, "фикстур сверено всего {checked}");
}

/// Подсказка на пустом месте молчит, а не отвечает пустой строкой.
#[test]
fn a_hover_off_a_name_says_nothing() {
    let path = Path::new("t.adamas");
    let file = SourceFile::new("t.adamas", "data Nat where\n  Zero : Nat\n");
    assert_eq!(hovered(path, &file, Position::new(0, 4)), None, "пробел");
    assert_eq!(
        hovered(path, &file, Position::new(0, 0)),
        None,
        "ключевое слово"
    );
    assert_eq!(
        hovered(path, &file, Position::new(9, 9)),
        None,
        "позиция за концом файла"
    );
    assert_eq!(
        hovered(path, &file, Position::new(1, 2)).as_deref(),
        Some("Zero : Nat")
    );
}

/// Подсказка над именем из **другого** файла называет его тип.
///
/// Свидетель различает по построению: ни `maximum`, ни `collected` в
/// `prelude.adamas` не объявлены - они приходят из `Std/Prelude.adamas`, и
/// однофайловый проход о них молчал (порог сверки выше был из-за этого
/// приспущен со 137 до 136).
#[test]
fn a_hover_reads_a_name_from_another_file() {
    let path = corpus().join("eval").join("prelude.adamas");
    let file = source(&path);
    let offset = file
        .text()
        .find("maximum Zero")
        .expect("`maximum` в фикстуре написан");
    let at = adamas_lsp::position::position(&file, offset, Encoding::Utf16)
        .expect("граница знака переводится");
    assert_eq!(
        hovered(&path, &file, at).as_deref(),
        Some(
            "Std.Prelude.maximum : {0 a : Type u0} -> {ω _ : Ord{u0} #0} -> \
             {| e0} (ω _ : #1) -> {| e0} (ω _ : Std.Prelude.List{u0} #2) -> {| e0} #3"
        )
    );
}

/// Переход к определению отвечает местом, а не отсутствием ответа.
#[test]
fn a_definition_answers_inside_the_file() {
    let uri = Uri::from_str("file:///probe.adamas").expect("URI разбирается");
    let file = SourceFile::new(
        "probe.adamas",
        "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\nдва : Nat\nдва = Succ (Succ Zero)\n",
    );
    let at = adamas_lsp::definition(&uri, &file, Position::new(5, 6), Encoding::Utf16)
        .expect("`Succ` объявлен в этом же файле");
    assert_eq!(at.range.start, Position::new(2, 2));
    assert_eq!(at.range.end, Position::new(2, 6));
    assert_eq!(
        adamas_lsp::definition(&uri, &file, Position::new(5, 4), Encoding::Utf16),
        None,
        "с пробела идти некуда"
    );
}

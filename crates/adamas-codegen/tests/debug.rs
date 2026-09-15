//! Отладочная информация: DWARF с именами и строками Adamas (§9 Фаза 7, трек E).
//!
//! Критерий плана - утверждение про **сеанс**: «в отладчике на точке останова
//! видно имя и значение adamas-переменной, а шаг идёт по строкам `.adamas`».
//! Проверяется он поэтому отладчиком, а не чтением метаданных:
//! `!DILocalVariable` в тексте `.ll` доказывает, что узел написан, и ничего не
//! говорит о том, найдёт ли отладчик по нему значение.
//!
//! Номера строк тест **ищет в тексте фикстуры**, а не помнит числами: запиши
//! их числом, и правка фикстуры чинилась бы правкой ожидания, то есть молча.
//!
//! # Потолок мелкости назван здесь, а не в отчёте
//!
//! Позиция в backend IR лежит на **функции**, и мельче сегодня взять неоткуда:
//! у термов ядра спанов нет вовсе, а узел терма держится на 48 байтах.
//! Наблюдаемое следствие - шаг идёт между определениями `.adamas`, а не между
//! выражениями внутри одного; поэтому фикстура ниже написана из нескольких
//! коротких определений, и наблюдается переход между их строками.

mod harness;

use std::path::Path;
use std::process::Command;

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::llvm::{
    MINIMUM_MAJOR, MINIMUM_TOOLS_VARIABLE, Pipeline, Stage, TOOLS_VARIABLE, Toolchain,
};

/// Фикстура: определения короткие и на разных строках - это и наблюдается.
///
/// Ответ `47` нетривиален по построению: `twice 21` даёт `42`, `bump` добавляет
/// `5`. Ноль и единица сюда не годятся - ими отвечает и не считавшая программа.
const PROGRAM: &str = "\
-- Фикстура трека E. Номера строк здесь наблюдаемы, и тест ищет их сам.

twice : Int64 -> Int64
twice x = mulInt64 x 2

bump : Int64 -> Int64 -> Int64
bump y step = addInt64 y step

main : Int64
main =
  let doubled : Int64 = twice 21
  bump doubled 5
";

/// Что программа обязана напечатать.
const ANSWER: &str = "47";

/// Клауза, на которой ставится точка останова.
const STOP: &str = "twice x = mulInt64 x 2";

/// Имя файла, под которым фикстура ложится на диск, - его называет DWARF.
const FIXTURE: &str = "session.adamas";

/// Строка, на которой написана клауза определения. 1-based, как в отладчике.
///
/// Ищется по тексту, а не помнится числом: фикстура правится, и ожидание,
/// записанное числом, чинилось бы вместе с ней - то есть переставало бы что-то
/// утверждать.
fn line_of(clause: &str) -> u32 {
    let at = PROGRAM
        .lines()
        .position(|line| line == clause)
        .unwrap_or_else(|| panic!("в фикстуре нет клаузы `{clause}`"));
    u32::try_from(at + 1).unwrap_or(u32::MAX)
}

/// Клаузы, чьи строки наблюдаются, вместе с именем определения.
const OBSERVED: [(&str, &str); 3] = [
    ("twice", "twice x = mulInt64 x 2"),
    ("bump", "bump y step = addInt64 y step"),
    ("main", "main ="),
];

/// Позиции доезжают до backend IR - и это первая клауза, а не сигнатура.
///
/// Инструментов не спрашивает: тут только понижение, и потому идёт везде,
/// включая машину без LLVM. Без него отсутствие DWARF читалось бы как
/// отсутствие отладчика, а не как разорванная цепочка позиций.
#[test]
fn positions_reach_the_backend_ir() {
    let (path, program) = harness::located("positions", PROGRAM);
    let source = program.source.as_ref().expect("исходник назван");
    assert_eq!(
        Path::new(&source.directory).join(&source.file),
        path,
        "IR называет не тот файл, который понижался"
    );

    for (name, clause) in OBSERVED {
        let function = program
            .functions
            .iter()
            .find(|it| it.name == name)
            .unwrap_or_else(|| panic!("в IR нет функции `{name}`"));
        let position = function
            .position
            .unwrap_or_else(|| panic!("`{name}` приехал без позиции"));
        assert_eq!(
            u32::try_from(position.line).unwrap_or(u32::MAX),
            line_of(clause),
            "`{name}` показывает не свою клаузу"
        );
    }
}

/// Понижение **без** исходника DWARF не получает.
///
/// Свидетель того, что отладочная информация приходит от текста, а не заводится
/// сама. Он же держит обещание «выход прежний»: корпус `llvm.rs` сверяет
/// порождённый `.ll` подстроками, и появись там DWARF молча - мутанты того
/// теста перестали бы применяться.
#[test]
fn without_a_source_there_is_no_dwarf() {
    let plain = harness::llvm_text("plain", PROGRAM).expect("фрагмент обязан брать фикстуру");
    for node in [
        "DICompileUnit",
        "DILocalVariable",
        "llvm.dbg.declare",
        "!dbg",
    ] {
        assert!(
            !plain.ll.contains(node),
            "`{node}` появился там, где исходника не называли"
        );
    }
}

/// Цепочки инструментов, либо объявленное отсутствие LLVM.
///
/// Правило то же, что у `llvm.rs`: инструмент, которого нет, обязан ронять
/// прогон, а не молчать. Исключение одно и объявлено переменной.
fn toolchains() -> Option<(Toolchain, Toolchain)> {
    if std::env::var("ADAMAS_LLVM").is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим (ADAMAS_LLVM=absent): сеанс не проверялся");
        return None;
    }
    Some((
        Toolchain::from_variable(TOOLS_VARIABLE),
        Toolchain::from_variable(MINIMUM_TOOLS_VARIABLE),
    ))
}

/// Конвейер отладочной сборки: без `opt` и с `llc -O0`.
///
/// `-O2` здесь не годится, и это свойство отладки, а не недоделка: значение
/// переменной наблюдаемо ровно пока она лежит в кадре, а оптимизатор её оттуда
/// убирает вместе с ячейкой. Тот же размен делает всякий компилятор на `-g`.
fn debuggable() -> Pipeline {
    Pipeline {
        stages: vec![
            Stage::new("llvm-as", &[], "bc"),
            Stage::new(
                "llc",
                &["-O0", "-filetype=obj", "-relocation-model=pic"],
                "o",
            ),
        ],
    }
}

/// Сеанс `gdb --batch` над собранной программой. Отдаёт вывод целиком.
///
/// Вывод берётся вместе со stderr: отказ поставить точку останова gdb печатает
/// именно туда, и потеряй тест эту половину - мутант выглядел бы как успех с
/// пустым результатом.
fn session(binary: &Path, commands: &[&str]) -> String {
    let mut gdb = Command::new("gdb");
    gdb.arg("--batch");
    for command in commands {
        gdb.arg("-ex").arg(command);
    }
    let done = gdb
        .arg(binary)
        .output()
        .unwrap_or_else(|why| panic!("gdb не запустился ({why}); в dev-shell он есть"));
    format!(
        "{}{}",
        String::from_utf8_lossy(&done.stdout),
        String::from_utf8_lossy(&done.stderr)
    )
}

/// Собирает `.ll` отладочным конвейером и ведёт сеанс на точке останова.
///
/// Останов ставится **по строке `.adamas`**, а не по имени символа, и в этом
/// половина утверждения: сумей отладчик найти строку - значит таблица строк
/// говорит про `.adamas`. Вторая половина - что он покажет на ней.
fn stopped_at_stop(stem: &str, artefacts: &Artefacts, tools: &Toolchain) -> String {
    let binary = harness::llvm_binary(stem, artefacts, tools, &debuggable());
    session(
        &binary,
        &[
            &format!("break {FIXTURE}:{}", line_of(STOP)),
            "run",
            "info args",
            "backtrace",
            "continue",
        ],
    )
}

/// В отладчике видно имя и значение adamas-переменной, и строка - из `.adamas`.
///
/// Это и есть критерий трека, записанный прогоном. Наблюдается всё, что он
/// называет, и каждое - отдельным утверждением:
///
/// - остановка называет **файл `.adamas`** и строку клаузы;
/// - на этой строке gdb показывает **написанный текст клаузы**, а не какой-то
///   другой: номер и текст сверяются друг с другом, а не по отдельности;
/// - в кадре стоит **имя Adamas** (`twice`), а не `fn_1`;
/// - `info args` печатает **имя параметра** и его значение (`x = 21`);
/// - стек показывает **две разные** строки `.adamas` - это и есть «шаг идёт по
///   строкам `.adamas`, не по строкам C»;
/// - программа досчитывает и печатает свой ответ, то есть отладочная сборка
///   считает то же.
#[test]
fn the_debugger_shows_an_adamas_name_and_value() {
    let Some((tools, _)) = toolchains() else {
        return;
    };
    let (_, artefacts) = harness::llvm_located("session", PROGRAM);
    let printed = stopped_at_stop("dwarf.session", &artefacts, &tools);
    eprintln!("{printed}");

    for claim in named_lines() {
        assert!(
            printed.contains(&claim),
            "сеанс не показал `{claim}`:\n{printed}"
        );
    }
    assert!(
        printed.contains("twice (x=21)"),
        "в кадре нет имени Adamas с его аргументом:\n{printed}"
    );
    assert!(
        printed.contains("x = 21"),
        "`info args` не показал имени и значения переменной:\n{printed}"
    );
    assert!(
        printed.contains(ANSWER),
        "отладочная сборка не досчитала до {ANSWER}:\n{printed}"
    );
}

/// Что сеанс обязан напечатать про строки - и чего мутант печатать не должен.
///
/// Три утверждения, и третье самое сильное: gdb печатает остановленную строку
/// **текстом**, вычитав его из `.adamas` по номеру из DWARF. Совпади текст с
/// клаузой - значит номер указывает туда, куда написано, а не просто существует.
///
/// Проверять «переменной не видно» здесь нельзя, и это измерено: gdb **сдвигает**
/// точку останова на ближайшую следующую строку с кодом, поэтому у мутанта она
/// встаёт на тот же адрес и `x = 21` печатается по-прежнему. Различает только
/// названная строка.
fn named_lines() -> Vec<String> {
    vec![
        // Кадр остановки: файл и строка клаузы.
        format!("twice (x=21) at {FIXTURE}:{}", line_of(STOP)),
        // Вызывающий: **своя** строка, отличная от предыдущей.
        format!("main () at {FIXTURE}:{}", line_of("main =")),
        // Номер и текст рядом - так gdb печатает остановленную строку.
        format!("{}\t{STOP}", line_of(STOP)),
    ]
}

/// Мутант: сдвиг всех строк DWARF на единицу обязан уронить сеанс.
///
/// Главная проверка трека, и без неё соседняя ничего не стоит: тест, зелёный
/// при сдвинутых номерах, проверяет **наличие** метаданных, а не их
/// правильность. Сдвиг не трогает ни одной инструкции - программа считает то же
/// и печатает то же, - поэтому отличить его может только проверка, которая
/// смотрит на строки.
#[test]
fn shifted_lines_break_the_session() {
    let Some((tools, _)) = toolchains() else {
        return;
    };
    let (_, honest) = harness::llvm_located("session", PROGRAM);
    let artefacts = Artefacts {
        ll: shifted(&honest.ll),
        support: honest.support.clone(),
    };
    let printed = stopped_at_stop("dwarf.shifted", &artefacts, &tools);
    eprintln!("{printed}");

    // Считает мутант по-прежнему верно - сдвинуты только строки, - и это
    // существенно: развались он вычислением, проверка ловила бы не то.
    assert!(
        printed.contains(ANSWER),
        "мутант перестал считать, и сдвиг строк тут ни при чём:\n{printed}"
    );
    for claim in named_lines() {
        assert!(
            !printed.contains(&claim),
            "сдвинутые строки всё ещё дают `{claim}`: проверка не различает:\n{printed}"
        );
    }
}

/// Текст `.ll` со сдвинутыми на единицу номерами строк DWARF.
///
/// Строка нуль не сдвигается: она означает «код написан не человеком», и её
/// сдвиг сместил бы разметку пролога, а не соответствие строк - то есть ломал
/// бы не то, что проверяется.
fn shifted(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    let mut moved = 0_usize;
    while let Some(at) = rest.find("line: ") {
        let (before, tail) = rest.split_at(at + "line: ".len());
        out.push_str(before);
        let digits: String = tail.chars().take_while(char::is_ascii_digit).collect();
        rest = &tail[digits.len()..];
        let number: u32 = digits.parse().unwrap_or(0);
        if number == 0 {
            out.push_str(&digits);
        } else {
            out.push_str(&(number + 1).to_string());
            moved += 1;
        }
    }
    out.push_str(rest);
    assert!(moved > 0, "мутант не применился: строк в DWARF нет вовсе");
    out
}

/// Минимальная версия читает те же отладочные метаданные.
///
/// Отдельно от `llvm.rs`, потому что проверяет другое: там треугольник стоял на
/// арифметике, здесь - на узлах `!DI*`, чей формат между мажорами **менялся**.
/// Восемнадцатая не знает отладочных записей, которыми двадцать первая печатает
/// то же; общий язык у них - вызовы `llvm.dbg.*`, и проверяется это прогоном, а
/// не таблицей совместимости.
///
/// Наблюдается не только ответ: DWARF обеих сборок читается `llvm-dwarfdump`, и
/// имена с строками обязаны найтись в обеих. Сойдись только ответ - и версия,
/// молча выбросившая метаданные, прошла бы.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_minimum_llvm_reads_the_debug_metadata() {
    let Some((tools, minimum)) = toolchains() else {
        return;
    };
    let current = tools
        .major()
        .unwrap_or_else(|error| panic!("штатная цепочка LLVM недоступна: {error}"));
    let oldest = minimum.major().unwrap_or_else(|error| {
        panic!("минимальная цепочка LLVM недоступна (`{MINIMUM_TOOLS_VARIABLE}`): {error}")
    });
    assert!(
        oldest <= MINIMUM_MAJOR,
        "минимальной названа {oldest}, а объявлено {MINIMUM_MAJOR}"
    );
    if current == oldest {
        eprintln!("обе цепочки {current}: треугольник этим прогоном не проверен");
    } else {
        eprintln!("штатная LLVM {current}, минимальная {oldest}");
    }

    let (_, artefacts) = harness::llvm_located("session", PROGRAM);
    for (stem, chain) in [("new", &tools), ("old", &minimum)] {
        let object = harness::llvm_object(
            &format!("dwarf.triangle.{stem}"),
            &artefacts,
            chain,
            &debuggable(),
        );
        let dumped = Command::new(tools.tool("llvm-dwarfdump"))
            .arg("--debug-info")
            .arg(&object)
            .output()
            .unwrap();
        let text = String::from_utf8_lossy(&dumped.stdout);
        for (name, clause) in OBSERVED {
            assert!(
                text.contains(&format!("DW_AT_name\t(\"{name}\")")),
                "LLVM {stem}: в DWARF нет имени `{name}`:\n{text}"
            );
            assert!(
                text.contains(&format!("DW_AT_decl_line\t({})", line_of(clause))),
                "LLVM {stem}: в DWARF нет строки `{name}`:\n{text}"
            );
        }
        let binary = harness::llvm_linked(
            &format!("dwarf.triangle.{stem}"),
            &object,
            &artefacts.support,
            true,
        );
        let run = Command::new(&binary).output().unwrap();
        assert!(run.status.success(), "LLVM {stem}: прогон оборвался");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim_end_matches('\n'),
            ANSWER,
            "LLVM {stem} посчитала не то с отладочной информацией"
        );
    }
}

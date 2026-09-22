//! Вариадический вызов обещает чужой стороне число векторных регистров (§5.3,
//! §10 вопрос 194).
//!
//! # Зачем свидетель по ассемблеру, а не по ответу
//!
//! Неверный вариадический прототип **не наблюдается ответом ни у одного из трёх
//! вычислителей**, и это измерено дважды: треком B волны 5 на `snprintf` из
//! libc и треком C волны 5 на библиотеке милестоуна, где оба мутанта - объявить
//! `curl_easy_setopt` и `curl_easy_getinfo` невариадическими - зелены целиком.
//! Договор трёх (§9) здесь не свидетельствует ни о чём: все трое читают одну
//! написанную сигнатуру и ошибаются одинаково.
//!
//! Правильность при этом держится **случайностью**. `SysV` AMD64 требует, чтобы
//! вызывающий положил в `al` число использованных векторных регистров;
//! невариадический прототип его не ставит, и в `al` остаётся младший байт того,
//! что вернул предыдущий вызов. У порождённого кода предыдущим стоит
//! `adamas_array_data`, отдающий адрес нагрузки, - байт этот ненулевой, и
//! вариадическая функция спасает `xmm` «по ошибке», то есть отвечает верно.
//!
//! Мерено треком C волны 6: мутантный бинарь (`snprintf` объявлена
//! невариадической, аргумент `Float64`) напечатал верный ответ **300 раз из
//! 300**. Ответ здесь не просто ненадёжный свидетель - он устойчиво зелёный,
//! и никакая перестановка фикстур этого не меняет.
//!
//! # Что проверяется
//!
//! Инструкция, записавшая `al` последней перед вызовом. Её наличие и есть
//! вариадический ABI; её отсутствие и есть неверный прототип. Читается она в
//! листинге **обоих** понижений, и оба листинга порождены тем же конвейером,
//! каким корпус собирает программы: `C_FLAGS` у C, [`Pipeline::optimised`] с
//! подменённым `-filetype` у `.ll`.
//!
//! # Чего свидетель не покрывает, и это названо
//!
//! * **Машину.** У `dlsym`-вызова ассемблера нет: форму выбирает таблица
//!   `adamas-interp`, и правило «вариадический символ зовётся вариадическим
//!   типом Rust» держится доводом (тип при вызове есть ABI), а не этим
//!   свидетелем. Частично машину прикрывает сама таблица: невариадическая форма
//!   с плавающим хвостом в ней отсутствует, и мутант на `extern-varargs-float`
//!   роняет корпус отказом «сигнатура вне таблицы вызова». На целом хвосте
//!   (`extern-varargs`, `curl`) такой формы не отсутствует, и машина молчит.
//! * **Не x86-64.** `al` есть свойство `SysV` AMD64. Вторая нога CI - `macos-14`,
//!   то есть aarch64-darwin, где вариадическая часть уезжает на стек и
//!   наблюдается, **вероятно**, прямо ответом; проверить это отсюда нечем, и
//!   свидетель там не запускается вовсе.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

mod harness;

use std::path::Path;

/// Вариадические символы корпусных программ.
///
/// Счёт вызовов не назван намеренно: обёртка над `libcurl` растёт (волна 6,
/// трек B ставит `CURLOPT_WRITEFUNCTION`), и число `curl_easy_setopt` - её
/// дело, а не дело свидетеля ABI. Утверждается «ни одного вызова без
/// обещания», и утверждение это от числа опций не зависит.
const VARIADIC: [(&str, &[&str]); 3] = [
    ("extern-varargs-float", &["snprintf"]),
    ("extern-varargs", &["snprintf", "sscanf"]),
    (
        "curl",
        &["curl_easy_setopt", "curl_easy_getinfo", "snprintf"],
    ),
];

/// Сколько векторных регистров обязан обещать вызов у каждой программы.
///
/// Плавающее в вариадической части - единственное место, где число не ноль, и
/// единственное, где оно наблюдаемо меняет поведение чужой стороны.
const VECTORS: [(&str, u64); 3] = [
    ("extern-varargs-float", 1),
    ("extern-varargs", 0),
    ("curl", 0),
];

/// Невариадические чужие символы: контроль.
///
/// Без него «обещание есть» проходило бы и у правки «печатать `...` у всякого
/// символа»: обещание у невариадического вызова - то же неопределённое
/// поведение `SysV`, что и его отсутствие у вариадического.
const ORDINARY: [(&str, &[&str]); 1] = [("extern-c", &["cbrt", "pow", "labs", "malloc"])];

/// Строка листинга: инструкция, метка либо то, что обещания не трогает.
#[derive(Debug)]
enum Line<'a> {
    /// Мнемоника и операнды через запятую.
    Instruction(&'a str, Vec<&'a str>),
    /// Начало блока: дальше назад читать нельзя - управление приходит извне.
    Label,
    /// Директива, комментарий, пустое.
    Skip,
}

/// Разбор листинга построчно.
fn read(listing: &str) -> Vec<Line<'_>> {
    listing.lines().map(line).collect()
}

/// Что за строка.
fn line(raw: &str) -> Line<'_> {
    // Комментарий у обоих ассемблеров один - решётка; у LLVM за ней едет
    // расшифровка непосредственного операнда, и без снятия она попала бы в
    // операнды.
    let text = raw.split('#').next().unwrap_or("").trim();
    if text.is_empty() {
        return Line::Skip;
    }
    if text.ends_with(':') {
        return Line::Label;
    }
    if text.starts_with('.') {
        return Line::Skip;
    }
    let mut parts = text.splitn(2, char::is_whitespace);
    let Some(mnemonic) = parts.next() else {
        return Line::Skip;
    };
    let operands = parts
        .next()
        .map_or_else(Vec::new, |rest| rest.split(',').map(str::trim).collect());
    Line::Instruction(mnemonic, operands)
}

/// Места вызова названного символа.
fn call_sites(lines: &[Line<'_>], symbol: &str) -> Vec<usize> {
    lines
        .iter()
        .enumerate()
        .filter_map(|(at, line)| {
            let Line::Instruction(mnemonic, operands) = line else {
                return None;
            };
            if !mnemonic.starts_with("call") {
                return None;
            }
            let target = operands.first()?.trim_start_matches('*');
            let name = target.split('@').next().unwrap_or(target);
            // Подчёркивание - Darwin: там символ у компоновщика пишется с
            // префиксом. Свидетель туда не доезжает (см. шапку), но правило
            // чтения от этого не зависит.
            (name == symbol || name.strip_prefix('_') == Some(symbol)).then_some(at)
        })
        .collect()
}

/// Мнемоники, у которых последний операнд - **не** назначение.
///
/// Список, а не белый список пишущих: неизвестная пишущая инструкция обязана
/// обрывать чтение, а не пропускаться. Пропусти её - и свидетель принял бы за
/// обещание константу, записанную до неё и с тех пор затёртую.
const READERS: [&str; 3] = ["cmp", "test", "push"];

/// Что вызывающий обещал про векторные регистры у вызова в позиции `at`.
///
/// `Some(n)` - последняя запись в `al` перед вызовом есть константа `n`, то
/// есть обещание дано. `None` - записи нет вовсе: `al` достался от предыдущего
/// вызова либо из другого блока, и обещания нет.
fn promise(lines: &[Line<'_>], at: usize) -> Option<u64> {
    for index in (0..at).rev() {
        match &lines[index] {
            Line::Skip => {}
            // Блок начался: что в `al`, решает не этот путь.
            Line::Label => return None,
            Line::Instruction(mnemonic, operands) => {
                // Предыдущий вызов и есть то, чем «верный по случайности»
                // прототип живёт: `al` остаётся младшим байтом его ответа.
                if mnemonic.starts_with("call") {
                    return None;
                }
                if READERS.iter().any(|it| mnemonic.starts_with(it)) {
                    continue;
                }
                let Some(destination) = operands.last() else {
                    continue;
                };
                if !matches!(*destination, "%al" | "%ax" | "%eax" | "%rax") {
                    continue;
                }
                return if mnemonic.starts_with("mov") {
                    operands
                        .first()
                        .and_then(|it| it.strip_prefix('$'))
                        .and_then(|it| it.parse().ok())
                } else if mnemonic.starts_with("xor") {
                    (operands.len() == 2 && operands[0] == *destination).then_some(0)
                } else {
                    None
                };
            }
        }
    }
    None
}

/// Программа корпуса.
fn source(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval")
        .join(format!("{name}.adamas"));
    std::fs::read_to_string(&path)
        .unwrap_or_else(|why| panic!("фикстуры {} нет: {why}", path.display()))
}

/// Ассемблер C-понижения.
fn c_listing(name: &str) -> String {
    let text = harness::text(&source(name)).expect("понижение обязано брать программу корпуса");
    harness::assembled(&format!("abi-{name}"), &text)
}

/// Каждый вызов символа обещает число векторных регистров.
fn promised(listing: &str, program: &str, path: &str, symbol: &str, wanted: Option<u64>) {
    let lines = read(listing);
    let sites = call_sites(&lines, symbol);
    assert!(
        !sites.is_empty(),
        "{path}/{program}: вызовов `{symbol}` в листинге нет вовсе - свидетель пуст"
    );
    for at in sites {
        let given = promise(&lines, at);
        assert!(
            given.is_some(),
            "{path}/{program}: вызов `{symbol}` не обещает векторных регистров - \
             `al` достался от предыдущего вызова, то есть прототип невариадический"
        );
        if let Some(wanted) = wanted {
            assert_eq!(
                given,
                Some(wanted),
                "{path}/{program}: вызов `{symbol}` обещал не то число векторных регистров"
            );
        }
    }
}

/// Ни один вызов символа обещания не даёт.
fn silent(listing: &str, program: &str, path: &str, symbol: &str) {
    let lines = read(listing);
    let sites = call_sites(&lines, symbol);
    assert!(
        !sites.is_empty(),
        "{path}/{program}: вызовов `{symbol}` в листинге нет вовсе - контроль пуст"
    );
    for at in sites {
        assert_eq!(
            promise(&lines, at),
            None,
            "{path}/{program}: невариадический вызов `{symbol}` обещает векторные регистры"
        );
    }
}

/// Понижение в C ставит `al` перед каждым вариадическим вызовом.
///
/// Тот самый свидетель, ради которого заведён файл: мутант «объявить символ
/// невариадической» убирает `movl $0, %eax` (и `movl $1, %eax` у плавающего) -
/// и краснеет здесь, оставаясь зелёным у всех трёх ответов.
///
/// Числа здесь не сверяются: порождённый C несёт печать плавающего
/// (`adamas_show_real`), а та зовёт `snprintf` системным прототипом со своим
/// числом. Числа сверяет `.ll`, где чужого кода нет ни строки.
#[test]
fn the_c_lowering_promises_a_vector_count_at_every_variadic_call() {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("не x86-64: `al` здесь не ABI, и свидетель не запускался");
        return;
    }
    for (program, symbols) in VARIADIC {
        let listing = c_listing(program);
        for symbol in symbols {
            promised(&listing, program, "C", symbol, None);
        }
    }
}

/// Понижение в `.ll` ставит `al`, и ставит его **числом использованных
/// векторных регистров**.
///
/// Обе цепочки: правило консервативного подмножества (`emit_llvm.rs`, шапка)
/// держится прогоном, а не грепом по формам, и ABI - его часть наравне с
/// разбором.
#[test]
fn both_llvm_toolchains_promise_the_vector_count() {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("не x86-64: `al` здесь не ABI, и свидетель не запускался");
        return;
    }
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    for (program, symbols) in VARIADIC {
        let wanted = VECTORS
            .iter()
            .find(|(it, _)| *it == program)
            .map(|(_, count)| *count)
            .expect("у каждой вариадической программы названо число регистров");
        let artefacts = harness::llvm_text(program, &source(program))
            .expect("скалярный фрагмент обязан брать программу корпуса");
        for (tag, tools) in [("cur", &current), ("min", &minimum)] {
            let listing =
                harness::llvm_assembled(&format!("abi-{program}-{tag}"), &artefacts, tools);
            for symbol in symbols {
                promised(&listing, program, tag, symbol, Some(wanted));
            }
        }
    }
}

/// Невариадический чужой вызов обещания не даёт - ни у одного из двух.
///
/// Вторая половина свидетеля. Без неё правка «печатать `...` у всякого
/// символа» проходила бы: обещание там, где чужая сторона его не читает, - то
/// же неопределённое поведение, что и его отсутствие там, где читает.
#[test]
fn an_ordinary_foreign_call_promises_nothing() {
    if !cfg!(target_arch = "x86_64") {
        eprintln!("не x86-64: `al` здесь не ABI, и свидетель не запускался");
        return;
    }
    for (program, symbols) in ORDINARY {
        let listing = c_listing(program);
        for symbol in symbols {
            silent(&listing, program, "C", symbol);
        }
        let Some((current, _)) = harness::llvm_toolchains() else {
            continue;
        };
        let artefacts = harness::llvm_text(program, &source(program))
            .expect("скалярный фрагмент обязан брать программу корпуса");
        let listing = harness::llvm_assembled(&format!("abi-{program}-cur"), &artefacts, &current);
        for symbol in symbols {
            silent(&listing, program, "cur", symbol);
        }
    }
}

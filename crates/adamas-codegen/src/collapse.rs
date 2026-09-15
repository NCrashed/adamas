//! Схлопывание пары `dup`/`drop` после инлайнинга (§9 Фаза 7, волна 1, трек C).
//!
//! Проход **текст `.ll` → текст `.ll`**, стоящий в конвейере
//! ([`llvm::Pipeline`](crate::llvm::Pipeline)) сразу за `opt`, то есть за
//! инлайнингом. Что он снимает, сказано одной фразой: пару, в которой `dup`
//! стоит у **вызывающего**, а `drop` — внутри **вызываемого**, и до инлайнинга
//! их разделяет граница функции.
//!
//! # Почему этого не делает Perceus
//!
//! [`perceus`](crate::perceus) — проход по функциям поодиночке
//! (`functions.into_iter().map(...)`), и это не недоделка, а его договор:
//! «аргумент приходит владением, ответ уходит владением». Вызывающий, у
//! которого значение живёт дальше вызова, обязан взять лишнюю ссылку; вызываемый
//! обязан её отдать. Обе половины верны по отдельности и избыточны вместе, но
//! увидеть их вместе можно только там, где тело вызываемого уже подставлено, —
//! то есть после инлайнинга. Отсюда и критерий трека: на C-бэкенде та же пара
//! остаётся, потому что там между `dup` и `drop` стоит вызов в другую единицу
//! трансляции.
//!
//! # Почему текст, а не плагин `opt`
//!
//! Измерено 2026-09-15, обеими цепочками dev-shell. Плагин собирается против
//! конкретного мажора: минимальный пустой плагин, собранный против 21.1.8,
//! принимается `opt` 21.1.8 (код 0) и **молча не грузится** в `opt` 18.1.8 —
//! ошибки загрузки нет вовсе, есть `unknown pass name` и код 1. То есть цена
//! плагина — не «собрать дважды», а «сломаться тихо на минимальной версии»,
//! ровно тот жанр отказа, против которого заведено правило консервативного
//! подмножества. Вдобавок собрать его в dev-shell нечем: у LLVM там ровно `bin`
//! и `share`, ни заголовков, ни `llvm-config`.
//!
//! Текстовый проход версии не знает вовсе — он не линкуется с LLVM ни на каком
//! шаге, — и это проверено прогоном на обеих цепочках, а не выведено.
//!
//! # Что считается наблюдением счётчика
//!
//! Снять пару можно, когда между `dup` и `drop` **никто не смотрит на
//! счётчик**. Ошибка здесь не видна ответом: снятая лишняя пара и снятая нужная
//! дают одно и то же число на выходе, а различает их счётчик живых блоков и
//! обрыв на длинном прогоне. Поэтому правило выбрано грубое и проверяемое:
//! между парой допускаются только инструкции **без памяти и без управления** —
//! арифметика, сравнение, `getelementptr`, приведения, `select`. Всё прочее —
//! вызов, `load`, `store`, любой терминатор — барьер, и пара не снимается.
//!
//! Из барьера на терминаторе следует, что пара обязана лежать в одном базовом
//! блоке; отдельной проверки блока поэтому нет.
//!
//! Что именно покупает это правило, показано [`Between::Ignored`]: тот же
//! проход без проверки середины. Он снимает пару, разделённую
//! `adamas_is_unique`, — а это ровно тот вопрос, ответ на который `dup` и
//! менял, — и прогон на таком коде обрывается. Свидетель — `tests/collapse.rs`.
//!
//! # Границы прохода
//!
//! Он не читает ни ядра, ни [`ir`](crate::ir): на вход ему приходит текст,
//! которого не было при эмиссии — его написал `opt`. Уникальность, кратность и
//! прочие факты сюда не доезжают и не должны: всё, на чём стоит снятие пары, —
//! арифметика счётчика, `rc + 1 - 1 = rc`.
//!
//! Переполнение счётчика проход игнорирует ровно так же, как рантайм
//! (`object.c`): 2³² лишних ссылок на один объект — не тот режим, который эта
//! стадия обслуживает.

use std::collections::BTreeSet;

/// Имя точки входа рантайма, берущей лишнюю ссылку.
const DUP: &str = "adamas_dup";

/// Имя точки входа, отдающей её обратно.
const DROP: &str = "adamas_drop";

/// Что проход считает допустимым между `dup` и `drop`.
///
/// Двух значений хватает, потому что вопрос один: проверять середину или нет.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Between {
    /// Штатный режим: между парой только инструкции без памяти и управления.
    Watched,

    /// **Мутант**, и в конвейере ему делать нечего.
    ///
    /// Середина не смотрится вовсе: `dup` схлопывается с первым же `drop` того
    /// же регистра **где угодно в функции**. Это наивная реализация того же
    /// прохода, и написать её ничего не стоит — тем она и опасна: на корпусе
    /// она даёт те же ответы, а роняет ровно те программы, где между парой
    /// стоит `adamas_is_unique`. Заведена затем, чтобы проверка отличала
    /// осторожный проход от неосторожного не на словах.
    Ignored,
}

/// Что проход сделал. Печатается свидетелями, а не читается кодом.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Report {
    /// Вызовов `adamas_dup` на входе.
    pub dups: usize,
    /// Вызовов `adamas_drop` на входе.
    pub drops: usize,
    /// Снятых пар.
    pub cancelled: usize,
    /// Пар, которые проход увидел и **отказался** снимать: `dup` того же
    /// регистра в этой функции был, а между ним и `drop` стоял барьер.
    pub refused: usize,
    /// Пар, не снятых потому, что значение `dup` кто-то читает.
    pub live: usize,
}

/// Штатный проход: та форма, что стоит в конвейере.
///
/// Отдельной функцией, а не замыканием, потому что [`Stage`](crate::llvm::Stage)
/// хранит указатель на функцию.
#[must_use]
pub fn watched(text: &str) -> String {
    collapse(text, Between::Watched).0
}

/// Он же без проверки середины — **мутант**, см. [`Between::Ignored`].
#[must_use]
pub fn reckless(text: &str) -> String {
    collapse(text, Between::Ignored).0
}

/// Снимает пары и отдаёт текст вместе с отчётом.
#[must_use]
pub fn collapse(text: &str, between: Between) -> (String, Report) {
    let lines: Vec<&str> = text.lines().collect();
    let mut removed = BTreeSet::new();
    let mut report = Report::default();

    let mut at = 0;
    while at < lines.len() {
        if lines[at].starts_with("define ") {
            let start = at + 1;
            let mut end = start;
            while end < lines.len() && lines[end] != "}" {
                end += 1;
            }
            scan(
                &lines[start..end],
                start,
                between,
                &mut removed,
                &mut report,
            );
            at = end + 1;
        } else {
            at += 1;
        }
    }

    let mut out = String::with_capacity(text.len());
    for (index, line) in lines.iter().enumerate() {
        if removed.contains(&index) {
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    (out, report)
}

/// Тело одной функции: ищет пары и помечает строки к снятию.
///
/// `offset` - номер первой строки тела в файле целиком: пометки нумеруются по
/// файлу, а не по телу.
fn scan(
    body: &[&str],
    offset: usize,
    between: Between,
    removed: &mut BTreeSet<usize>,
    report: &mut Report,
) {
    // Ожидающие `dup`: строка в файле и регистр, по которому взята ссылка.
    let mut pending: Vec<(usize, &str)> = Vec::new();
    // Регистры, по которым `dup` в этой функции был вообще. Нужно только
    // отчёту: без них «отказался снимать» не отличить от «пары не было».
    let mut seen: BTreeSet<&str> = BTreeSet::new();

    for (index, line) in body.iter().enumerate() {
        let text = line.trim();
        if text.is_empty() || text.starts_with(';') {
            continue;
        }

        if let Some(arguments) = call_to(text, DUP) {
            report.dups += 1;
            let Some(register) = first_register(arguments) else {
                continue;
            };
            // Значение `dup` эмиттер не читает (`emit_llvm.rs`), и `opt`
            // читателя не заводит: подставить `%p` вместо результата он не
            // может, потому что про `returned` у объявления не знает. Но
            // держаться это должно на проверке, а не на вере в соседний модуль.
            if assigned(text).is_some_and(|result| used_elsewhere(body, index, result)) {
                report.live += 1;
                continue;
            }
            seen.insert(register);
            pending.push((offset + index, register));
            continue;
        }

        if let Some(arguments) = call_to(text, DROP) {
            report.drops += 1;
            let register = top_level(arguments).next().and_then(first_register);
            if let Some(register) = register {
                if let Some(position) = pending.iter().rposition(|(_, it)| *it == register) {
                    let (dup, _) = pending.remove(position);
                    removed.insert(dup);
                    removed.insert(offset + index);
                    report.cancelled += 1;
                    continue;
                }
                if seen.contains(register) {
                    report.refused += 1;
                }
            }
            // Несхлопнутый `drop` - барьер: он вправе освободить блок и позвать
            // дроп детей, а тот трогает счётчики чужих объектов.
            if between == Between::Watched {
                pending.clear();
            }
            continue;
        }

        if between == Between::Watched && !harmless(text) {
            pending.clear();
        }
    }
}

/// Аргументы вызова названной точки входа, если строка её зовёт.
///
/// Ищется `@имя(`, а не разбирается вся инструкция: имена рантайма в
/// порождённом IR встречаются только в позиции вызова, а объявление
/// (`declare ptr @adamas_dup(ptr)`) лежит вне тела функции и сюда не попадает.
fn call_to<'a>(text: &'a str, name: &str) -> Option<&'a str> {
    let needle = format!("@{name}(");
    let at = text.find(&needle)?;
    let rest = &text[at + needle.len()..];
    let end = closing(rest)?;
    Some(&rest[..end])
}

/// Смещение скобки, закрывающей уже открытую.
fn closing(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (at, character) in text.char_indices() {
        match character {
            '(' => depth += 1,
            ')' if depth == 0 => return Some(at),
            ')' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// Аргументы, разделённые запятыми **верхнего** уровня.
///
/// Скобки считаются: константное выражение `inttoptr (i64 1 to ptr)` запятых не
/// несёт, а `getelementptr (i8, ptr @x, i64 8)` несёт, и разрезать его по ним
/// значило бы получить не тот операнд.
fn top_level(arguments: &str) -> impl Iterator<Item = &str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (at, character) in arguments.char_indices() {
        match character {
            '(' | '[' | '{' | '<' => depth += 1,
            ')' | ']' | '}' | '>' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(&arguments[start..at]);
                start = at + 1;
            }
            _ => {}
        }
    }
    parts.push(&arguments[start..]);
    parts.into_iter()
}

/// Регистр первого аргумента, если он именно регистр.
///
/// Тип и атрибуты параметра (`ptr noundef nonnull %v1`) отбрасываются тем, что
/// берётся **последнее** слово: атрибуты стоят перед операндом всегда. Операнд,
/// не начинающийся с `%`, отвергается - непосредственное значение и
/// константное выражение проход не трогает вовсе.
fn first_register(argument: &str) -> Option<&str> {
    let last = argument.split_whitespace().next_back()?;
    last.starts_with('%').then_some(last)
}

/// Имя, которому инструкция присваивает результат.
fn assigned(text: &str) -> Option<&str> {
    let (left, _) = text.split_once(" = ")?;
    left.trim().starts_with('%').then(|| left.trim())
}

/// Читает ли имя кто-нибудь, кроме строки, которая его завела.
fn used_elsewhere(body: &[&str], own: usize, name: &str) -> bool {
    body.iter()
        .enumerate()
        .any(|(index, line)| index != own && mentions(line, name))
}

/// Встречается ли имя в строке **целиком**, а не приставкой к длиннейшему.
fn mentions(line: &str, name: &str) -> bool {
    let mut from = 0;
    while let Some(at) = line[from..].find(name) {
        let after = from + at + name.len();
        if !line[after..].starts_with(identifier) {
            return true;
        }
        from = after;
    }
    false
}

/// Символ, которым имя LLVM вправе продолжиться.
fn identifier(character: char) -> bool {
    character.is_ascii_alphanumeric() || matches!(character, '_' | '.' | '$' | '-')
}

/// Инструкции, которые счётчика не видят: ни памяти, ни управления, ни вызова.
///
/// Список белый, а не чёрный, и это существенно: незнакомая инструкция обязана
/// считаться барьером. Чёрный список при появлении новой формы IR молча
/// разрешил бы снятие пары через неё.
const HARMLESS: [&str; 33] = [
    "add",
    "and",
    "ashr",
    "bitcast",
    "extractvalue",
    "fadd",
    "fcmp",
    "fdiv",
    "fmul",
    "fneg",
    "fpext",
    "fptosi",
    "fptoui",
    "fptrunc",
    "freeze",
    "fsub",
    "getelementptr",
    "icmp",
    "insertvalue",
    "inttoptr",
    "lshr",
    "mul",
    "or",
    "phi",
    "ptrtoint",
    "sdiv",
    "select",
    "sext",
    "shl",
    "sitofp",
    "srem",
    "sub",
    "trunc",
];

/// Не мешает ли инструкция снять пару.
fn harmless(text: &str) -> bool {
    let body = text.split_once(" = ").map_or(text, |(_, rest)| rest);
    let mut words = body.split_whitespace();
    let mut first = words.next().unwrap_or_default();
    while matches!(first, "tail" | "musttail" | "notail") {
        first = words.next().unwrap_or_default();
    }
    HARMLESS.contains(&first)
}

#[cfg(test)]
mod tests {
    use super::{Between, collapse, harmless};

    /// Соседние `dup` и `drop` одного регистра снимаются оба.
    #[test]
    fn a_neighbouring_pair_goes_away() {
        let text = "\
define i64 @f(ptr %v) {
entry:
  %t0 = call ptr @adamas_dup(ptr %v)
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret i64 7
}
";
        let (out, report) = collapse(text, Between::Watched);
        assert_eq!(report.cancelled, 1);
        assert!(!out.contains("adamas_dup"), "{out}");
        assert!(!out.contains("adamas_drop"), "{out}");
    }

    /// Пара, разделённая вызовом, не снимается, и отказ виден отчётом.
    #[test]
    fn a_call_between_them_keeps_the_pair() {
        let text = "\
define i64 @f(ptr %v) {
entry:
  %t0 = call ptr @adamas_dup(ptr %v)
  %t1 = call i32 @adamas_is_unique(ptr %v)
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret i64 7
}
";
        let (out, report) = collapse(text, Between::Watched);
        assert_eq!(report.cancelled, 0);
        assert_eq!(report.refused, 1);
        assert!(out.contains("adamas_dup"), "{out}");
    }

    /// Тот же текст без проверки середины: пара снимается, и это мутант.
    #[test]
    fn the_reckless_mode_takes_what_the_watched_one_refuses() {
        let text = "\
define i64 @f(ptr %v) {
entry:
  %t0 = call ptr @adamas_dup(ptr %v)
  %t1 = call i32 @adamas_is_unique(ptr %v)
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret i64 7
}
";
        let (out, report) = collapse(text, Between::Ignored);
        assert_eq!(report.cancelled, 1);
        assert!(out.contains("adamas_is_unique"), "{out}");
        assert!(!out.contains("adamas_dup"), "{out}");
    }

    /// Пара на **разных** регистрах не пара.
    #[test]
    fn different_registers_are_not_a_pair() {
        let text = "\
define i64 @f(ptr %v, ptr %w) {
entry:
  %t0 = call ptr @adamas_dup(ptr %w)
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret i64 7
}
";
        let (_, report) = collapse(text, Between::Watched);
        assert_eq!(report.cancelled, 0);
        assert_eq!(report.refused, 0);
    }

    /// Прочитанный результат `dup` снимать нечем: имя осталось бы висеть.
    #[test]
    fn a_read_result_holds_the_pair() {
        let text = "\
define ptr @f(ptr %v) {
entry:
  %t0 = call ptr @adamas_dup(ptr %v)
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret ptr %t0
}
";
        let (_, report) = collapse(text, Between::Watched);
        assert_eq!(report.cancelled, 0);
        assert_eq!(report.live, 1);
    }

    /// Объявление рантайма лежит вне тела и вызовом не считается.
    #[test]
    fn the_declaration_is_not_a_call() {
        let text = "declare ptr @adamas_dup(ptr)\ndeclare void @adamas_drop(ptr, ptr)\n";
        let (out, report) = collapse(text, Between::Watched);
        assert_eq!(report.dups, 0);
        assert_eq!(report.drops, 0);
        assert_eq!(out, text);
    }

    /// Имя-приставка не считается употреблением: `%t1` не читает `%t10`.
    #[test]
    fn a_longer_name_is_not_the_same_name() {
        let text = "\
define i64 @f(ptr %v) {
entry:
  %t1 = call ptr @adamas_dup(ptr %v)
  %t10 = add i64 1, 2
  call void @adamas_drop(ptr %v, ptr @adamas_release_extern)
  ret i64 %t10
}
";
        let (_, report) = collapse(text, Between::Watched);
        assert_eq!(report.live, 0);
        assert_eq!(report.cancelled, 1);
    }

    /// Незнакомая инструкция - барьер, а не «наверное можно».
    #[test]
    fn an_unknown_instruction_is_a_barrier() {
        assert!(harmless("%t0 = add i64 %a, %b"));
        assert!(harmless(
            "  %t1 = getelementptr inbounds nuw i8, ptr %v, i64 8"
        ));
        assert!(!harmless("%t2 = load i32, ptr %v"));
        assert!(!harmless("store i32 0, ptr %v"));
        assert!(!harmless("%t3 = tail call i64 @g()"));
        assert!(!harmless("br label %next"));
        assert!(!harmless("%t4 = atomicrmw add ptr %v, i32 1 seq_cst"));
    }
}

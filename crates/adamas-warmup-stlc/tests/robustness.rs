//! Свойства, которые обязаны держаться на любом входе.
//!
//! Anti-pattern из `CONTRIBUTING.md`: "Panic на user-facing путях. Compiler
//! crash от валидного (или невалидного, но с понятной ошибкой) кода -
//! серьёзный баг". Проверяется это единственным способом - генерацией входов,
//! которые никто не писал руками.

use adamas_core::source::SourceFile;
use adamas_warmup_stlc::check;
use proptest::prelude::*;

/// Куски, из которых собирается похожий на программу мусор. Чистый случайный
/// текст почти всегда падает уже в лексере и до вывода типов не доходит;
/// смесь из настоящих лексем пробивается глубже.
const FRAGMENTS: &[&str] = &[
    "let", "rec", "in", "if", "then", "else", "fix", "true", "false", "\\", "λ", "->", "=", "==",
    ":", "(", ")", "+", "-", "*", "<", "x", "y", "f", "Int", "Bool", "0", "1", "42", "--", "\n",
    " ", "@", "很",
];

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(proptest::sample::select(FRAGMENTS), 0..24)
        .prop_map(|parts| parts.join(" "))
}

/// Глубокая вложенность отдельной стратегией: двадцать четыре фрагмента
/// `soup` такой глубины не набирают, а рекурсивный спуск тратит стек ровно на
/// ней. Верхняя граница заведомо выше предела парсера, чтобы проверялся отказ,
/// а не только успешный разбор.
fn nested() -> impl Strategy<Value = String> {
    (0usize..600, 0usize..3).prop_map(|(depth, shape)| match shape {
        0 => format!("{}1{}", "(".repeat(depth), ")".repeat(depth)),
        1 => format!("{}1", "\\x -> ".repeat(depth)),
        _ => format!("(1 : {}Int)", "Int -> ".repeat(depth)),
    })
}

fn program() -> impl Strategy<Value = String> {
    prop_oneof![soup(), nested()]
}

proptest! {
    /// Компилятор либо принимает вход, либо возвращает ошибку. Третьего -
    /// паники, обрыва, зацикливания - быть не должно.
    #[test]
    fn checking_arbitrary_input_never_panics(text in program()) {
        let file = SourceFile::new("soup.stlc", text);
        let _ = check(&file);
    }

    /// Тот же вход обязан давать тот же ответ. Ловит утечку состояния между
    /// прогонами - например, метаконтекст, переживший свой вызов.
    #[test]
    fn checking_is_deterministic(text in program()) {
        let file = SourceFile::new("soup.stlc", text);
        let first = check(&file).map(|ty| ty.to_string());
        let second = check(&file).map(|ty| ty.to_string());
        prop_assert_eq!(first, second);
    }

    /// Спан ошибки обязан указывать внутрь файла. Спан за границами текста
    /// уронил бы рендерер диагностики на любом реальном входе.
    #[test]
    fn error_spans_stay_inside_the_file(text in program()) {
        let file = SourceFile::new("soup.stlc", text);
        if let Err(error) = check(&file) {
            if let Some(span) = error.span() {
                prop_assert!(span.end() <= file.len(), "спан {span:?} вне файла длиной {}", file.len());
                prop_assert!(file.location(span.start()).is_some(), "начало спана не разрешается");
            }
        }
    }
}

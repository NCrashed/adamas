//! Поверхностный язык Adamas: лексер, layout, парсер, печать (§4).
//!
//! # Состояние (Фаза 2)
//!
//! Готово: [`lexer`] - текст в токены и комментарии; [`layout`] - значимые
//! отступы в явные границы блоков. Дальше по плану Фазы 2: AST и recursive
//! descent, обратная печать с round-trip, элаборация в ядро.
//!
//! # Что этот крейт не делает
//!
//! Не знает о ядре ничего, кроме [`adamas_core::source::Span`]: поверхностный
//! язык и core-язык связаны элаборацией, а она живёт в `adamas-core`. Обратной
//! зависимости нет вовсе.
//!
//! Не разрешает фикситеты: `infixl 6 +` объявляется в prelude (§4.4), то есть
//! в программе, а не в компиляторе, и до разбора модуля таблица неизвестна.

pub mod layout;
pub mod lexer;
pub mod token;

pub use token::Tokens;

use token::{Comment, Token};

/// Ошибка на пути от текста до потока токенов.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// Лексическая.
    #[error(transparent)]
    Lex(#[from] lexer::LexError),
    /// Расстановки блоков.
    #[error(transparent)]
    Layout(#[from] layout::LayoutError),
}

impl Error {
    /// Где ошибка.
    #[must_use]
    pub fn span(self) -> adamas_core::source::Span {
        match self {
            Self::Lex(error) => error.span(),
            Self::Layout(error) => error.span(),
        }
    }
}

/// Текст -> токены: лексер и следом layout.
///
/// # Errors
///
/// Любая ошибка [`lexer::lex`] или [`layout::layout`].
pub fn tokenize(text: &str) -> Result<Tokens, Error> {
    let mut lexed = lexer::lex(text)?;
    let tokens = layout::layout(&lexed.tokens)?;
    remap_comments(&mut lexed.comments, &tokens);
    Ok(Tokens {
        tokens,
        comments: lexed.comments,
    })
}

/// Переводит привязку комментариев из лексического потока в поток с границами.
///
/// Инвариант [`Comment::token`] - «индекс в соседнем `tokens`», и layout его
/// сдвигает: виртуальные токены встают в том числе прямо перед тем, к кому
/// комментарий привязан. Без пересчёта первый же потребитель - `adamas fmt`
/// (§7.1) - взял бы по индексу не тот токен.
fn remap_comments(comments: &mut [Comment], tokens: &[Token]) {
    if comments.is_empty() {
        return;
    }
    let mut lexical: Vec<u32> = Vec::with_capacity(tokens.len());
    for (index, token) in tokens.iter().enumerate() {
        if !token.kind.is_virtual() {
            lexical.push(u32::try_from(index).unwrap_or(u32::MAX));
        }
    }
    for comment in comments {
        let moved = lexical.get(comment.token as usize);
        debug_assert!(moved.is_some(), "комментарий указывает мимо потока");
        if let Some(&index) = moved {
            comment.token = index;
        }
    }
}

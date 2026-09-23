//! Правило привязки документирующего блока (§7.1).
//!
//! # Чем этот свидетель ломается
//!
//! Привязка держится на двух условиях сразу - **написание** (`-- |`) и
//! **положение** (только пробел, без пустой строки), - и свидетель, знающий
//! одно из них, зелен при сломанном другом. Поэтому здесь у каждого условия
//! своя пара «привязалось / не привязалось», отличающаяся ровно этим условием
//! и ничем больше.
//!
//! Отдельно проверяется то, чего не видно из одной формы: блок не перепрыгивает
//! через **чужой текст**. Между комментарием и следующим объявлением бывает
//! целое определение без пустой строки после него, и правило «нет пустой
//! строки» в одиночку отдало бы документацию `f` соседу `g`.

use adamas_parser::docs;
use adamas_parser::token::{Comment, CommentKind};

/// Документация объявления номер `nth` (с нуля) в порядке написания.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: неразобравшийся текст здесь означает сломанную заготовку"
)]
fn documented(text: &str, nth: usize) -> Option<String> {
    let module = adamas_parser::parse(text).expect("заготовка обязана разбираться");
    let tokens = adamas_parser::tokenize(text).expect("заготовка обязана лексироваться");
    let decl = module.decls.get(nth).expect("объявление на месте");
    docs::attached(text, &tokens.comments, decl.span)
}

/// Комментарии текста вместе с их разновидностью.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: неразобравшийся текст здесь означает сломанную заготовку"
)]
fn comments(text: &str) -> Vec<Comment> {
    adamas_parser::tokenize(text)
        .expect("заготовка обязана лексироваться")
        .comments
}

#[test]
fn the_marker_is_what_makes_a_block_documentation() {
    let text = "-- | Складывает.\nadd : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Складывает."));
}

#[test]
fn a_comment_without_the_marker_is_not_documentation() {
    // Ровно тот же текст без `|`. Различие одно, и ответ обязан различаться.
    let text = "-- Складывает.\nadd : Nat\n";
    assert_eq!(documented(text, 0), None);
}

#[test]
fn a_blank_line_separates_the_block_from_the_declaration() {
    let text = "-- | Складывает.\n\nadd : Nat\n";
    assert_eq!(documented(text, 0), None);
}

#[test]
fn without_the_blank_line_the_same_block_attaches() {
    // Парный к предыдущему: различие - одна пустая строка.
    let text = "-- | Складывает.\nadd : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Складывает."));
}

#[test]
fn plain_lines_continue_the_block() {
    let text = "-- | Первая.\n-- Вторая.\nadd : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Первая.\nВторая."));
}

#[test]
fn a_bare_marker_line_separates_paragraphs() {
    // Голый `--` даёт пустую строку **текста**: так пишется абзац. Пустая
    // строка **исходника** тем временем блок кончает - это разные вещи, и
    // свидетель держит обе.
    let text = "-- | Первая.\n--\n-- Вторая.\nadd : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Первая.\n\nВторая."));
}

#[test]
fn a_blank_line_inside_the_run_cuts_it() {
    let text = "-- | Первая.\n\n-- Вторая.\nadd : Nat\n";
    // Верхняя половина отрезана пустой строкой, нижняя маркера не несёт.
    assert_eq!(documented(text, 0), None);
}

#[test]
fn a_note_written_above_the_marker_does_not_cancel_it() {
    // Блок открывает первый `-- |` **сверху**. Ищи его снизу - и заметка,
    // приписанная над готовой документацией, молча отменила бы её целиком.
    let text = "-- Заметка.\n-- | Складывает.\nadd : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Складывает."));
}

#[test]
fn a_block_does_not_jump_over_a_neighbouring_declaration() {
    // Между документацией `f` и объявлением `g` пустой строки нет - есть тело
    // `f`. Правило «только пробел» - не украшение: без него `g` получил бы
    // чужую документацию, и заметить это было бы нечем.
    let text = "-- | Про f.\nf : Nat\nf = Zero\ng : Nat\n";
    assert_eq!(documented(text, 0).as_deref(), Some("Про f."));
    assert_eq!(documented(text, 2), None);
}

#[test]
fn a_block_comment_is_never_documentation() {
    let text = "{- Складывает. -}\nadd : Nat\n";
    assert_eq!(documented(text, 0), None);
}

#[test]
fn a_block_comment_cuts_the_run() {
    // `{- … -}` документацией не бывает, и поглотить его строчным блоком
    // значило бы напечатать в документации то, чего автор в неё не писал.
    let text = "-- | Про f.\n{- врезка -}\nadd : Nat\n";
    assert_eq!(documented(text, 0), None);
}

#[test]
fn the_lexer_marks_the_marker_and_nothing_else() {
    // Разновидность - свойство **написания**: проверяется отдельно от привязки,
    // иначе поломка лексера пряталась бы за поломкой правила и наоборот.
    let found = comments("-- обычный\n-- | документирующий\n{- блочный -}\nx : Nat\n");
    let kinds: Vec<CommentKind> = found.iter().map(|it| it.kind).collect();
    assert_eq!(
        kinds,
        [CommentKind::Line, CommentKind::Doc, CommentKind::Block]
    );
}

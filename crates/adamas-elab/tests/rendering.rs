//! Сообщение об отказе целиком - снапшотами.
//!
//! Проверяется текст, который увидит автор программы: `tests/diagnostics.rs`
//! отвечает за то, **что** подчёркнуто, а здесь - как это выглядит. Снапшот
//! выбран потому, что предмет проверки и есть строка: любой bespoke assert
//! свёлся бы к её же кускам, но перестал бы ловить всё остальное.

use adamas_core::source::SourceFile;
use adamas_elab::{elaborate, report};
use adamas_parser::parse;

/// Сообщение об отказе. Успешная проверка - провал теста.
fn refusal(text: &str) -> String {
    let file = SourceFile::new("проба.adamas", text);
    let module = match parse(file.text()) {
        Ok(module) => module,
        Err(error) => panic!("не разобралось: {error}"),
    };
    match elaborate(&module) {
        Err(error) => report(&file, &error),
        Ok(_) => panic!("ожидался отказ"),
    }
}

const BASE: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Bool where
  True : Bool
  False : Bool

";

#[test]
fn a_type_mismatch_names_its_variables() {
    // Ради этого рендеринг и вынесен из ядра: `#1` в тексте читатель связывает
    // с телескопом счётом, а имя стоит в самом телескопе.
    let text = format!(
        "{BASE}data Even : Nat -> Type where
  EvenZero : Even Zero

f : (0 n : Nat) -> Even n -> Bool
f n e = e
"
    );
    insta::assert_snapshot!(refusal(&text));
}

#[test]
fn holes_are_numbered_from_zero_in_every_message() {
    // Идентификатор дырки сквозной по прогону, а в сообщении нумерация своя:
    // иначе объявление, добавленное выше, сдвигало бы номера в тексте ошибки,
    // ничего о ней не говоря. Два файла отличаются только соседями сверху.
    let alone = refusal("Q : Type -> Type\n\nf : Q -> Q\n");
    let crowded = refusal("A : Type\nB : Type\nC : Type\n\nQ : Type -> Type\n\nf : Q -> Q\n");
    assert_eq!(
        alone.replace("проба.adamas:3", "проба.adamas:7"),
        crowded,
        "номера дырок не зависят от соседних объявлений"
    );
    insta::assert_snapshot!(alone);
}

#[test]
fn the_caret_is_measured_in_characters() {
    // Спан меряется байтами, подчёркивание - символами. Юникодное имя ловит
    // разницу: каретки уезжали вправо на длину лишних байт.
    insta::assert_snapshot!(refusal(
        "data Число where\n  Ноль : Число\n\nf : Число Число\n"
    ));
}

#[test]
fn a_long_line_is_shown_by_a_window() {
    // Спайн применения пишется в одну строку, и печатать её целиком значит
    // спрятать под ней сообщение.
    let text = format!("{BASE}big : Nat\nbig = nope{}\n", " Zero".repeat(120));
    insta::assert_snapshot!(refusal(&text));
}

#[test]
fn a_detached_signature_shows_both_places() {
    let text = format!("{BASE}f : Nat -> Nat\ng : Nat -> Nat\ng x = x\nf x = x\n");
    insta::assert_snapshot!(refusal(&text));
}

#[test]
fn refusals_about_ownership_read_as_sentences() {
    // Владение - самая молодая часть среза, и её отказы автор видит чаще
    // прочих. Снапшот держит их текст целиком: подчёркнут написанный
    // фрагмент, а не объявление, и причина названа своя у каждого.
    const RESOURCE: &str = "\
resource File where
  Open : Bool -> File
  drop : File -> Bool
  drop (Open b) = True

";
    let refusals = [
        format!("{BASE}{RESOURCE}theFile : File\n"),
        format!("{BASE}{RESOURCE}use : (ω h : File) -> Bool\n"),
        format!(
            "{BASE}resource Socket where\n  Conn : Bool -> Socket\n  drop : Socket -> Socket\n  drop (Conn b) = Conn b\n"
        ),
        format!(
            "{BASE}{RESOURCE}resource Socket where\n  Conn : Bool -> Socket\n  drop : Socket -> Bool\n  drop (Conn b) = True\n"
        ),
    ];
    let shown: Vec<String> = refusals.iter().map(|text| refusal(text)).collect();
    insta::assert_snapshot!(shown.join("\n\n"));
}

#[test]
fn a_refusal_inside_a_clause_shows_the_route() {
    // Путь показывается всегда: он объясняет, почему подчёркнуто это место, а
    // когда маршрут уходит в дерево разбора - остаётся единственным указанием.
    let text = format!(
        "{BASE}f : Nat -> Bool
f Zero = True
f (Succ k) = k
"
    );
    insta::assert_snapshot!(refusal(&text));
}

//! Baseline для пути «текст -> дерево».
//!
//! Проход стоит первым на каждом запуске компилятора и на каждом нажатии
//! клавиши в LSP (§7.2), поэтому его baseline заводится вместе с ним, а не
//! тогда, когда станет заметно, что он медленный.
//!
//! Точки разделены намеренно:
//!
//! - `lex_module` - только лексика: посимвольный проход, ключевые слова,
//!   строки и колонки.
//! - `layout_module` - только офсайд, по уже готовому потоку. Видно, сколько
//!   стоит отдельный проход, ради которого парсер не знает про отступы.
//! - `tokenize_module` - оба вместе плюс пересчёт привязки комментариев, то
//!   есть то, что заплатит вызывающий.
//! - `parse_module` - только спуск, по готовому потоку. Полного пути «текст ->
//!   дерево» отдельной точкой нет: он есть сумма этой и `tokenize_module`, и
//!   мерить сумму дважды незачем.
//! - `print_module` - обратная печать. Мерится не ради компилятора - там она не
//!   на пути, - а ради `adamas fmt` (§7.1) и round-trip-тестов, где она стоит
//!   на каждом прогоне свойства.

#![allow(
    missing_docs,
    reason = "criterion_group! разворачивается в недокументированную pub fn"
)]
#![allow(
    clippy::expect_used,
    reason = "заготовка бенча - не пользовательский вход; отказ здесь означает \
              сломанный бенч, и падать он должен громко"
)]

use std::fmt::Write as _;

use adamas_parser::{layout::layout, lexer::lex, parser, print, tokenize};
use criterion::{Criterion, criterion_group, criterion_main};

/// Модуль из `copies` повторов примеров §4.1: ресурс с `where`, сигнатура с
/// effect row, индексированное семейство, разбор клаузами, тело-блок с `let`.
/// Синтетика, но по составу лексем - то же, что пишут в этом языке.
fn module(copies: usize) -> String {
    let mut text = String::new();
    for index in 0..copies {
        let _ = write!(
            text,
            "\
-- Ресурс {index}
resource File{index} where
  drop h = closeFile h

withFile{index} : String -> (File{index} -> {{IO}} a) -> {{IO, Except IOError}} a
withFile{index} path k =
  let h = openFile path
  k h

data Vect{index} : (0 n : Nat) -> Type -> Type where
  Nil  : Vect{index} 0 a
  Cons : a -> Vect{index} n a -> Vect{index} (n + 1) a

map{index} : (a -> b) -> Vect{index} n a -> Vect{index} n b
map{index} f Nil         = Nil
map{index} f (Cons x xs) = Cons (f x) (map{index} f xs)

counter{index} : {{State Int}} Int
counter{index} =
  let n = get
  put (n + 1)
  n

"
        );
    }
    text
}

/// Тот же модуль без форм Фаз 3-4: effect row парсер Фазы 2 отвергает (§9), а
/// бенчу спуска нужен вход, который разбирается целиком. Замена в тексте, а не
/// вторая фикстура: две копии одного модуля разъехались бы.
fn phase_two_module(copies: usize) -> String {
    module(copies)
        .replace("{IO, Except IOError} ", "")
        .replace("{IO} ", "")
        .replace("{State Int} ", "")
}

fn tokenizing(c: &mut Criterion) {
    let text = module(64);
    let lexed = lex(&text).expect("фикстура лексится");
    assert!(tokenize(&text).is_ok(), "фикстура проходит layout");

    c.bench_function("lex_module_64", |b| {
        b.iter(|| lex(&text));
    });

    c.bench_function("layout_module_64", |b| {
        b.iter(|| layout(&lexed.tokens));
    });

    c.bench_function("tokenize_module_64", |b| {
        b.iter(|| tokenize(&text));
    });
}

fn parsing(c: &mut Criterion) {
    let text = phase_two_module(64);
    let tokens = tokenize(&text).expect("фикстура токенизируется");
    assert!(
        parser::parse(&text, &tokens.tokens).is_ok(),
        "фикстура разбирается целиком"
    );

    c.bench_function("parse_module_64", |b| {
        b.iter(|| parser::parse(&text, &tokens.tokens));
    });
}

fn printing(c: &mut Criterion) {
    let text = phase_two_module(64);
    let tokens = tokenize(&text).expect("фикстура токенизируется");
    let module = parser::parse(&text, &tokens.tokens).expect("фикстура разбирается");

    c.bench_function("print_module_64", |b| {
        b.iter(|| print(&module));
    });
}

criterion_group!(benches, tokenizing, parsing, printing);
criterion_main!(benches);

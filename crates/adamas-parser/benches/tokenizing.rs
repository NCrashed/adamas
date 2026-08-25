//! Baseline для пути «текст -> токены с границами блоков».
//!
//! Лексер стоит первым на каждом запуске компилятора и на каждом нажатии
//! клавиши в LSP (§7.2), поэтому его baseline заводится вместе с ним, а не
//! тогда, когда станет заметно, что он медленный.
//!
//! Три точки, разделённые намеренно:
//!
//! - `lex_module` - только лексика: посимвольный проход, ключевые слова,
//!   строки и колонки.
//! - `layout_module` - только офсайд, по уже готовому потоку. Видно, сколько
//!   стоит отдельный проход, ради которого парсер не знает про отступы.
//! - `tokenize_module` - оба вместе плюс пересчёт привязки комментариев, то
//!   есть то, что заплатит вызывающий.

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

use adamas_parser::{layout::layout, lexer::lex, tokenize};
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

criterion_group!(benches, tokenizing);
criterion_main!(benches);

//! Пределы против стека: свидетели того, что записанное число не больше того,
//! что язык выдерживает (§10 вопрос 187).
//!
//! # Почему свидетели живут здесь
//!
//! Пределы записаны в разборе (`MAX_DEPTH`) и в элаборации (`UNARY_LIMIT`,
//! `STRING_LIMIT`), а срывается на глубине **понижение**, и раньше всех
//! прочих: в потоке с умолчательным стеком в два мегабайта спайн применений в
//! 125 звеньев проходит, в 126 роняет процесс. Проверка типов держит 208,
//! машина - больше 208, разбор голых скобок - 380 входов. Свидетель, который
//! останавливается на проверке, порога поэтому не видит.
//!
//! # Почему в потоке теста, а не в отдельном
//!
//! Поток теста - это и есть наименьшее окружение языка: `cargo test` порождает
//! его с умолчательным стеком в два мегабайта, и явно стек не задан нигде.
//! Главный поток `adamas` и `adamas-lsp` берёт восемь от `ulimit -s`, то есть
//! вчетверо больше. Ставить свидетелю свой `stack_size` значило бы мерить
//! окружение, которого у языка нет.
//!
//! # Почему формы именно такие
//!
//! Предел один, а мер две, и форма выбрана так, чтобы каждая мера
//! свидетельствовалась **порознь**. Список даёт звено на элемент и два входа
//! спуска на весь литерал; голые скобки дают два входа на скобку и ни одного
//! звена. Скобочная вложенность `(f (f …))` мерилась бы обеими сразу, и мутант,
//! снявший одну, оставался бы жив за счёт другой.
//!
//! # Как читается провал
//!
//! Программа **на** пределе обязана пройти оба понижения; она же на звено
//! глубже обязана получить **названный** отказ. Если кадры вырастут - от
//! другого rustc, от нового поля в узле, - эти тесты не покраснеют, а **уронят
//! процесс**: `fatal runtime error: stack overflow`. Это и есть сигнал, что
//! запас, на котором стоят числа, кончился, и мерить надо заново.

#![allow(
    clippy::expect_used,
    reason = "заготовка свидетеля: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::ElabError;
use adamas_parser::Error as ParseAnyError;
use adamas_parser::parser::ParseError;

/// Предел вложенности разбора и глубины терма.
const DEPTH: usize = 64;

/// Предел унарного литерала.
const UNARY: usize = 112;

/// Предел длины строкового литерала вместе с завершающим нулём.
const STRING: usize = 40;

/// Числа написаны, а не прочитаны из констант: свидетель, читающий предел
/// оттуда же, где тот объявлен, ехал бы вместе с ним и оставался зелёным при
/// любом его значении.
#[test]
fn past_every_limit_stands_a_named_refusal() {
    // Мера звеньев: список на элемент длиннее предела.
    let error = refused(&list(DEPTH + 1));
    let ParseAnyError::Parse(ParseError::TooDeep { limit, .. }) = error else {
        panic!("получено {error:?}");
    };
    assert_eq!(limit as usize, DEPTH);

    // Мера спуска: скобка стоит двух входов, ещё четыре тратит само тело
    // определения, поэтому тридцать первая скобка - уже за пределом. Звеньев
    // здесь ноль, и мерой звеньев этот вход не ловится вовсе.
    let error = refused(&parens(31));
    let ParseAnyError::Parse(ParseError::TooDeep { limit, .. }) = error else {
        panic!("получено {error:?}");
    };
    assert_eq!(limit as usize, DEPTH);

    let error = refused_by_elaboration(&unary(UNARY + 1));
    let ElabError::UnaryLiteral { limit, .. } = error else {
        panic!("получено {error:?}");
    };
    assert_eq!(limit as usize, UNARY);

    let error = refused_by_elaboration(&string(STRING));
    let ElabError::StringLength { limit, length, .. } = error else {
        panic!("получено {error:?}");
    };
    assert_eq!((limit as usize, length), (STRING, STRING + 1));
}

/// Глубина терма ровно в предел проходит **до конца**, а не до проверки типов.
#[test]
fn a_term_at_the_depth_limit_is_lowered() {
    lowered(&list(DEPTH));
}

/// Глубина спуска ровно в предел разбирается.
///
/// До понижения тут доводить нечего: скобки звеньев не дают, и терм под ними
/// такой же, как без них. Свидетельствуется ровно разбор.
#[test]
fn a_descent_at_the_depth_limit_is_parsed() {
    assert!(adamas_parser::parse(&parens(30)).is_ok());
}

/// Унарный литерал ровно в предел проходит до конца.
#[test]
fn a_unary_literal_at_the_limit_is_lowered() {
    lowered(&unary(UNARY));
}

/// Строка ровно в предел проходит до конца.
///
/// `STRING` считает завершающий ноль, поэтому написанных байт на один меньше.
#[test]
fn a_string_at_the_limit_is_lowered() {
    lowered(&string(STRING - 1));
}

/// Сумма: предельная глубина **вокруг** предельной строки.
///
/// Мерить слагаемые порознь недостаточно - глубина написанного и глубина, в
/// которую разворачивается литерал, складываются. Замер суммы: под 64 звеньями
/// проходит строка в 46 байт и роняет процесс 47, поэтому предел строки и взят
/// 40, а не 46.
///
/// Форма - **спайн**, а не скобочная вложенность: скобка стоит спуску двух
/// входов, и `(same (same …))` упёрлось бы в предел спуска на тридцать первом
/// уровне, то есть свидетельствовало бы половину. Спайн даёт звено на аргумент
/// при одном входе. Литерал стоит **первым** аргументом: первый написанный
/// лежит глубже всех (`App (App (App g a1) a2) a3`), и поставленный последним
/// он свидетельствовал бы глубину один.
#[test]
fn the_deepest_legal_term_around_the_longest_legal_string_is_lowered() {
    // Шестьдесят один, а не 64: три звена бюджета съедает сама сигнатура, и
    // глубже спайн под пределом не пишется. Это и есть худшее законное.
    const ARITY: usize = 61;
    let bytes = STRING - 1;
    let mut args: Vec<String> = vec![format!("\"{}\"", "a".repeat(bytes))];
    args.extend((0..ARITY - 1).map(|_| "other".to_owned()));
    // Синоним, а не `Array 40 UInt8` на месте: написанное применение ставит
    // два звена сверх стрелки, и цепочка из 64 стрелок вышла бы за предел не
    // стрелками, а доменом.
    let text = format!(
        "type Bytes = Array {0} UInt8\n\nother : Bytes\nother = \"{1}\"\n\n\
         deep : {2}UInt8\ndeep {3} = 0\n\n\
         main : UInt8\nmain = deep {4}\n",
        STRING,
        "b".repeat(bytes),
        "Bytes -> ".repeat(ARITY),
        vec!["_"; ARITY].join(" "),
        args.join(" ")
    );
    lowered(&text);
}

/// Сумма, которая **не** закрыта, и это названо числом.
///
/// Предельная глубина вокруг предельного унарного литерала роняет процесс: под
/// 64 звеньями проходит 65 и рвётся 66, а предел стоит на 112, потому что
/// корпусу нужен `plus 100 n`. Свидетель поэтому берёт не предел, а число под
/// измеренной границей суммы, и стоит здесь ровно затем, чтобы день, когда
/// сумму закроют, был виден: тогда сюда встанет `UNARY`.
#[test]
fn the_deepest_legal_term_around_a_unary_literal_is_lowered_well_short_of_the_limit() {
    let mut items: Vec<String> = (0..DEPTH - 1).map(|_| "Zero".to_owned()).collect();
    items.push("56".to_owned());
    let text = format!(
        "{NAT}{LIST}main : List Nat\nmain = [{}]\n",
        items.join(", ")
    );
    lowered(&text);
}

/// Натуральные для унарного литерала.
const NAT: &str = "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\n";

/// Список: звено на элемент, два входа спуска на весь литерал.
const LIST: &str = "data List a where\n  Nil : List a\n  Cons : a -> List a -> List a\n\n";

/// Программа со списком в `count` элементов: ровно `count` звеньев терма.
fn list(count: usize) -> String {
    let items = vec!["zero"; count].join(", ");
    format!("{LIST}zero : UInt64\nzero = 0\n\nmain : List UInt64\nmain = [{items}]\n")
}

/// Программа с `count` голыми скобками: `2 * count` входов спуска, ноль звеньев.
fn parens(count: usize) -> String {
    format!(
        "main : UInt64\nmain = {}0{}\n",
        "(".repeat(count),
        ")".repeat(count)
    )
}

/// Программа с унарным литералом `value`.
fn unary(value: usize) -> String {
    format!("{NAT}main : Nat\nmain = {value}\n")
}

/// Программа со строкой в `bytes` написанных байт; в типе на один больше.
fn string(bytes: usize) -> String {
    format!(
        "text : Array {} UInt8\ntext = \"{}\"\n\nmain : UInt8\nmain = arrayIndex text 0\n",
        bytes + 1,
        "a".repeat(bytes)
    )
}

/// Разбирает, элаборирует и понижает **обоими** эмиттерами.
fn lowered(text: &str) {
    let (signature, body) = checked(text);
    let emitted = adamas_codegen::compile(&signature, &body).expect("C-эмиттер отказал");
    assert!(!emitted.is_empty());
    let artefacts = adamas_codegen::compile_llvm(&signature, &body).expect("LLVM-эмиттер отказал");
    assert!(!artefacts.ll.is_empty());
}

/// Проверенная программа и тело её `main`.
fn checked(text: &str) -> (Signature, Term) {
    let module = adamas_parser::parse(text).expect("разбор отказал");
    let (signature, _warnings) = adamas_elab::elaborate(&module).expect("элаборация отказала");
    let body = signature
        .lookup("main")
        .and_then(|it| it.body.clone())
        .expect("у `main` нет тела");
    (signature, body)
}

/// Отказ разбора. Успех - провал теста.
fn refused(text: &str) -> ParseAnyError {
    match adamas_parser::parse(text) {
        Err(error) => error,
        Ok(_) => panic!("ожидался отказ разбора"),
    }
}

/// Отказ элаборации. Успех - провал теста.
fn refused_by_elaboration(text: &str) -> ElabError {
    let module = adamas_parser::parse(text).expect("разбор отказал");
    match adamas_elab::elaborate(&module) {
        Err(error) => error,
        Ok(_) => panic!("ожидался отказ элаборации"),
    }
}

//! Форма понижения выбирается по row написанного типа (§13, обе записи
//! 2026-09-08; решение 1 волны 4).
//!
//! Утверждений здесь четыре, и каждое читает **текст** порождённого C либо
//! отказ, а не число блоков: форма живёт в сигнатуре, и по числам она не видна.
//!
//! - *Непустая row даёт два скрытых аргумента, и они стоят в каноническом
//!   порядке* ([`a_rowed_function_carries_both_hidden_arguments`]). Порядок
//!   несимметричен по типам, поэтому перестановка не сокращается: `const
//!   adamas_evidence *` в позиции `adamas_kont *` не собирается вовсе, и
//!   свидетель ловит её дважды - текстом сигнатуры и сборкой прогона.
//! - *Пустая row не даёт ничего* ([`a_pure_function_carries_none`]) - тот же
//!   исходник со снятой меткой, ближайший проходящий сосед.
//! - *Первая форма не зовёт вторую прямым вызовом*
//!   ([`the_first_form_cannot_call_the_second`]). Взяться такая пара из
//!   исходника не может - погашение row не пропустит, - поэтому свидетель
//!   собирает IR руками: это единственное место, где эмиттеру можно подать
//!   вход, которого понижение не порождает.
//! - *Элиминатор хендлера форму не решает* ([`a_handler_does_not_decide_the_form`]):
//!   вычисление под `handleMulti` получает вторую форму по своей row, как и под
//!   одношотным.

mod harness;

use adamas_codegen::emit_c;
use adamas_codegen::ir::{
    Binding, CtorId, Expr, Fact, Form, FuncId, Function, LocalId, Program, Repr,
};
use adamas_core::mult::Mult;

/// Скрытые аргументы второй формы в каноническом порядке `adamas.h`.
const HIDDEN: &str = "(const adamas_evidence *ev, adamas_kont *kont, adamas_value v0)";

/// Программа, где обе формы стоят рядом и обе доезжают до прогона.
///
/// Хендлера здесь нет намеренно: посмотреть надо на форму, а хендлер увёл бы
/// свидетеля к своей площадке (см. [`a_handler_does_not_decide_the_form`]).
/// Метка объявлена и не гасится нигде, потому что и не производится: row -
/// **верхняя граница** производимого, и `quiet u = Zero` под `{Ask}` законно.
/// Функцию с
/// непустой row при этом нельзя **применить** из чистой окружающей, поэтому
/// наружу она уходит значением - `hold` её только держит.
///
/// Формы в программе выходят такие: `quiet` и `louder` - вторая (метка `Ask` в
/// row), `relayed` - вторая же, но применяет чужое значение, `size`, `hold` и
/// `main` - первая.
const BOTH: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

effect Ask where
  ask : Nat

quiet : Unit -> {Ask} Nat
quiet u = Zero

louder : Unit -> {Ask} Nat
louder u = quiet u

size : Unit -> Nat
size u = Succ Zero

relayed : (Unit -> Nat) -> Unit -> {Ask} Nat
relayed g u = g u

hold : (Unit -> {Ask} Nat) -> (Unit -> {Ask} Nat) -> Nat
hold f g = Succ (Succ Zero)

main : Nat
main = hold louder (relayed size)
";

/// Тот же исходник без единой метки: ближайший проходящий сосед.
///
/// Отличие ровно одно - `{Ask}` снято, - и оно же единственная причина, по
/// которой у соседа скрытых аргументов нет ни одного.
const PURE: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

quiet : Unit -> Nat
quiet u = Zero

louder : Unit -> Nat
louder u = quiet u

size : Unit -> Nat
size u = Succ Zero

relayed : (Unit -> Nat) -> Unit -> Nat
relayed g u = g u

hold : (Unit -> Nat) -> (Unit -> Nat) -> Nat
hold f g = Succ (Succ Zero)

main : Nat
main = hold louder (relayed size)
";

/// Мультишот над той же меткой: форму `asked` решает её row, а не элиминатор.
const HANDLED: &str = "\
data Unit where
  MkUnit : Unit

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

effect Ask where
  ask : Nat

asked : {Ask} Nat
asked = ask

main : Nat
main = handleMulti asked with
  return v -> v
  ask -> resume Zero
";

/// Сигнатура функции по её имени: строка под комментарием-заголовком тела.
///
/// По телу, а не по блоку объявлений: объявление и определение печатаются из
/// одного места, и читать надо то, что стоит над кодом.
fn signature(text: &str, name: &str) -> String {
    body(text, name)
        .lines()
        .next()
        .unwrap_or_default()
        .to_owned()
}

/// Тело функции по имени: от заголовка до закрывающей скобки в первой колонке.
fn body(text: &str, name: &str) -> String {
    let title = format!("/* {name} */");
    let mut lines = text.lines().skip_while(|line| *line != title);
    assert!(
        lines.next().is_some(),
        "тела `{name}` в порождённом C нет:\n{text}"
    );
    let mut out = String::new();
    for line in lines {
        out.push_str(line);
        out.push('\n');
        if line == "}" {
            return out;
        }
    }
    panic!("тело `{name}` не закончилось:\n{out}");
}

/// Непустая row даёт два скрытых аргумента - и в сигнатуре, и на месте вызова.
#[test]
fn a_rowed_function_carries_both_hidden_arguments() {
    let text = harness::text(BOTH).unwrap_or_else(|error| panic!("`BOTH` не понизился: {error}"));

    // Сигнатура: скрытые стоят перед написанным и в порядке `adamas.h`.
    for name in ["quiet", "louder", "relayed"] {
        let signature = signature(&text, name);
        assert!(
            signature.contains("(const adamas_evidence *ev, adamas_kont *kont, adamas_value"),
            "скрытые аргументы `{name}` стоят не так, как в `adamas_lowered_second`: {signature}"
        );
    }
    assert_eq!(
        signature(&text, "quiet"),
        format!(
            "static adamas_value fn_{}{HIDDEN} {{",
            number(&text, "quiet")
        ),
        "сигнатура второй формы разошлась с `adamas_lowered_second`"
    );

    // Прямой вызов второй формы из второй: скрытые идут дальше, а не гаснут.
    let call = format!("fn_{}(ev, kont, ", number(&text, "quiet"));
    assert!(
        body(&text, "louder").contains(&call),
        "`louder` зовёт `quiet` без скрытых аргументов:\n{}",
        body(&text, "louder")
    );

    // Применение значения из второй формы: тот же вектор и та же ручка.
    let relayed = body(&text, "relayed");
    assert!(
        applied(&relayed).contains(", ev, kont, "),
        "`relayed` применяет значение без скрытых аргументов:\n{relayed}"
    );

    // Трамплин у второй формы передаёт свои - у него они есть всегда.
    let trampoline = format!("return fn_{}(ev, kont, ", number(&text, "louder"));
    assert!(
        text.contains(&trampoline),
        "трамплин `louder` не передал скрытые аргументы: {text}"
    );

    // И всё это собирается, считается и не течёт.
    let stderr = harness::agreed("формы", BOTH).unwrap_or_else(|error| panic!("прогон: {error}"));
    let (_, live) = harness::blocks("формы", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Пустая row не даёт ни одного скрытого аргумента.
///
/// Отдельно от предыдущего, потому что утверждение про **отсутствие**: скажи
/// `form` «вторая» всем подряд - и первый свидетель остался бы зелёным.
#[test]
fn a_pure_function_carries_none() {
    let text = harness::text(PURE).unwrap_or_else(|error| panic!("`PURE` не понизился: {error}"));
    assert!(
        !text.contains("fn_") || !text.contains("fn_0(const adamas_evidence"),
        "точка входа получила скрытые аргументы"
    );
    for line in text.lines() {
        let Some(at) = line.find("fn_") else { continue };
        let tail = &line[at..];
        assert!(
            !tail.contains("(const adamas_evidence"),
            "у чистой программы завелась вторая форма: {line}"
        );
    }
    // Применение значения из первой формы: вектора у неё нет вовсе, а ручка
    // **своя** - за границей замыкания стоит динамика, и вызываемый вправе
    // оказаться дроблёным (трек D волны 4). Корень стоит ноль ячеек кучи, и
    // это видно тем же прогоном ниже.
    let relayed = body(&text, "relayed");
    assert!(
        applied(&relayed).contains(", NULL, &"),
        "первая форма передала вектор, которого у неё нет:\n{relayed}"
    );
    assert!(
        relayed.contains("adamas_kont_init(&"),
        "первая форма применяет значение без своего корня:\n{relayed}"
    );
    let stderr = harness::agreed("чистые", PURE).unwrap_or_else(|error| panic!("прогон: {error}"));
    let (_, live) = harness::blocks("чистые", &stderr);
    assert_eq!(live, 0, "прогон оставил блоки живыми");
}

/// Строка с применением значения. Их в теле ровно одна у обоих свидетелей.
fn applied(body: &str) -> &str {
    body.lines()
        .find(|line| line.contains("adamas_apply("))
        .unwrap_or_else(|| panic!("применения значения в теле нет:\n{body}"))
}

/// Номер функции по её имени - тот, которым она названа в C.
fn number(text: &str, name: &str) -> usize {
    let signature = signature(text, name);
    let at = signature.find("fn_").unwrap_or_else(|| {
        panic!("в сигнатуре `{name}` нет имени функции: {signature}");
    });
    signature[at + 3..]
        .split('(')
        .next()
        .and_then(|it| it.parse().ok())
        .unwrap_or_else(|| panic!("номер функции `{name}` не прочитался: {signature}"))
}

/// Первая форма второй прямым вызовом не зовёт: передать ей нечего.
///
/// Вход собран руками, и это единственный способ: понижение такой пары не
/// порождает - применить функцию с непустой row из чистой окружающей значило бы
/// погасить непустое пустым (§3.4), а элаборация этого не пропускает. Свидетель
/// поэтому стоит на входе эмиттера, а не на исходнике.
#[test]
fn the_first_form_cannot_call_the_second() {
    let callee = Function {
        id: FuncId(1),
        name: "эффектная".to_owned(),
        form: Form::Detached,
        captured: Vec::new(),
        parameters: vec![Binding {
            name: "x".to_owned(),
            local: LocalId(0),
            fact: Fact::present(Mult::Many),
        }],
        result: Repr::Boxed,
        body: Expr::Local(LocalId(0)),
    };
    let entry = Function {
        id: FuncId(0),
        name: "main".to_owned(),
        form: Form::Stack,
        captured: Vec::new(),
        parameters: Vec::new(),
        result: Repr::Boxed,
        body: Expr::Call {
            function: FuncId(1),
            arguments: vec![Expr::Construct {
                constructor: CtorId(0),
                reuse: None,
                arguments: Vec::new(),
            }],
        },
    };
    let program = Program {
        constructors: Vec::new(),
        packings: Vec::new(),
        labels: Vec::new(),
        handlers: Vec::new(),
        functions: vec![entry, callee],
        entry: FuncId(0),
    };
    let error = emit_c::emit(&program).expect_err("первой форме передать скрытые нечем");
    let text = error.to_string();
    assert!(
        text.contains("main") && text.contains("эффектная"),
        "отказ не назвал ни зовущего, ни званого: {text}"
    );
}

/// Форму выбирает row, а не элиминатор: под мультишотом она та же.
///
/// Свидетель писался треком A, когда мультишот отвергался по имени, и говорил
/// «отказ не про форму функции». Отказа не стало (трек E), а утверждение
/// осталось тем же и проверяется прямо: `asked` объявлена `{Ask} Nat`, значит
/// вторая форма, и оба скрытых аргумента у неё стоят там же, где у одношотного.
#[test]
fn a_handler_does_not_decide_the_form() {
    let text = harness::compiled(HANDLED)
        .unwrap_or_else(|error| panic!("мультишот не понизился: {error}"));
    let signature = signature(&text, "asked");
    assert!(
        signature.contains("(const adamas_evidence *ev, adamas_kont *kont, adamas_value"),
        "вычисление под мультишотом получило не вторую форму: {signature}"
    );
}

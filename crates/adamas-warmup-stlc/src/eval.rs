//! Интерпретатор на подстановке, call-by-value.
//!
//! Инвариант, на котором всё держится: **всякий терм, попадающий в [`reduce`],
//! замкнут.** Вычисление начинается с замкнутой программы (несвязанные
//! переменные отвергнуты выводом типов), а бета-редукция замкнутость сохраняет.
//! Поэтому подстановка обходится без обычного для де Брёйна `shift`: у
//! подставляемого терма нет свободных переменных, поднимать нечего.

use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use crate::core::Expr;
use crate::error::Error;
use crate::syntax::BinOp;

/// Сколько шагов редукции разрешено до того, как вычисление будет признано
/// незавершающимся. `fix` позволяет написать расходящуюся программу, а тест,
/// висящий вечно, хуже упавшего.
const STEP_LIMIT: u32 = 1_000_000;

/// Результат вычисления.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Value {
    /// Целое число.
    Int(i64),
    /// Логическое значение.
    Bool(bool),
    /// Функция. Тело не показывается: без имён оно нечитаемо, а обратное
    /// преобразование в поверхностный синтаксис - работа для Фазы 2.
    Fun,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(value) => write!(f, "{value}"),
            Self::Bool(value) => write!(f, "{value}"),
            Self::Fun => f.write_str("<fun>"),
        }
    }
}

/// Вычисляет замкнутое core-выражение.
///
/// # Errors
///
/// [`Error::StepLimit`] на расходящейся программе, [`Error::Overflow`] на
/// целочисленном переполнении.
pub(crate) fn eval(expr: &Expr) -> Result<Value, Error> {
    let mut fuel = STEP_LIMIT;
    let result = reduce(&Rc::new(expr.clone()), &mut fuel)?;
    Ok(match *result {
        Expr::Int(value) => Value::Int(value),
        Expr::Bool(value) => Value::Bool(value),
        _ => Value::Fun,
    })
}

/// Редуцирует терм до значения.
///
/// Хвостовые переходы - тело беты, выбранная ветка `if`, разворот `fix` -
/// сделаны присваиванием в `current`, а не рекурсивным вызовом: иначе
/// расходящаяся программа переполняла бы стек раньше, чем кончится топливо, и
/// вместо [`Error::StepLimit`] получался бы abort процесса. На нехвостовых
/// позициях стек растёт по-прежнему.
fn reduce(expr: &Rc<Expr>, fuel: &mut u32) -> Result<Rc<Expr>, Error> {
    let mut current = Rc::clone(expr);

    loop {
        *fuel = fuel
            .checked_sub(1)
            .ok_or(Error::StepLimit { limit: STEP_LIMIT })?;

        let node = Rc::clone(&current);
        match &*node {
            // Значения. Под лямбду не заходим: call-by-value, не нормализация.
            Expr::Int(_) | Expr::Bool(_) | Expr::Lam(_) => return Ok(node),

            // Свободная переменная в замкнутом терме невозможна; см. инвариант.
            Expr::Var(index) => unreachable!("свободная переменная с индексом {index}"),

            Expr::App(callee, argument) => {
                let function = reduce(callee, fuel)?;
                let value = reduce(argument, fuel)?;
                let Expr::Lam(body) = &*function else {
                    unreachable!("применение не-функции: {function:?}");
                };
                current = substitute(body, 0, &value);
            }

            Expr::If(cond, then, otherwise) => {
                current = match &*reduce(cond, fuel)? {
                    Expr::Bool(true) => Rc::clone(then),
                    Expr::Bool(false) => Rc::clone(otherwise),
                    other => unreachable!("условие не логического типа: {other:?}"),
                };
            }

            // `fix v` разворачивается в тело `v` с подставленным `fix v`.
            // Аргумент подставляется невычисленным - вычислить его значило бы
            // зациклиться. Работает потому, что вывод типов гарантирует под
            // `fix` лямбду: результат подстановки снова значение.
            Expr::Fix(inner) => {
                let function = reduce(inner, fuel)?;
                let Expr::Lam(body) = &*function else {
                    unreachable!("fix не от функции: {function:?}");
                };
                let unrolled = Rc::new(Expr::Fix(Rc::clone(&function)));
                current = substitute(body, 0, &unrolled);
            }

            Expr::Bin(op, left, right) => {
                let left = reduce(left, fuel)?;
                let right = reduce(right, fuel)?;
                let (Expr::Int(a), Expr::Int(b)) = (&*left, &*right) else {
                    unreachable!("арифметика не над числами");
                };
                return Ok(Rc::new(apply_op(*op, *a, *b)?));
            }
        }
    }
}

fn apply_op(op: BinOp, a: i64, b: i64) -> Result<Expr, Error> {
    let arithmetic = |value: Option<i64>| value.map(Expr::Int).ok_or(Error::Overflow);
    match op {
        BinOp::Add => arithmetic(a.checked_add(b)),
        BinOp::Sub => arithmetic(a.checked_sub(b)),
        BinOp::Mul => arithmetic(a.checked_mul(b)),
        BinOp::Less => Ok(Expr::Bool(a < b)),
        BinOp::Equal => Ok(Expr::Bool(a == b)),
    }
}

/// Подставляет замкнутый терм вместо переменной с индексом `depth`.
///
/// Переменные выше `depth` уменьшаются на единицу: связывание, через которое
/// они считались, исчезает вместе с редексом.
fn substitute(expr: &Rc<Expr>, depth: usize, value: &Rc<Expr>) -> Rc<Expr> {
    match &**expr {
        Expr::Var(index) => match index.cmp(&depth) {
            Ordering::Equal => Rc::clone(value),
            Ordering::Greater => Rc::new(Expr::Var(index - 1)),
            Ordering::Less => Rc::clone(expr),
        },
        Expr::Lam(body) => Rc::new(Expr::Lam(substitute(body, depth + 1, value))),
        Expr::App(callee, argument) => Rc::new(Expr::App(
            substitute(callee, depth, value),
            substitute(argument, depth, value),
        )),
        Expr::If(cond, then, otherwise) => Rc::new(Expr::If(
            substitute(cond, depth, value),
            substitute(then, depth, value),
            substitute(otherwise, depth, value),
        )),
        Expr::Fix(inner) => Rc::new(Expr::Fix(substitute(inner, depth, value))),
        Expr::Bin(op, left, right) => Rc::new(Expr::Bin(
            *op,
            substitute(left, depth, value),
            substitute(right, depth, value),
        )),
        Expr::Int(_) | Expr::Bool(_) => Rc::clone(expr),
    }
}

#[cfg(test)]
mod tests {
    use adamas_core::source::SourceFile;

    use super::Value;
    use crate::Error;

    fn eval(text: &str) -> Result<Value, Error> {
        crate::run(&SourceFile::new("test.stlc", text)).map(|outcome| outcome.value)
    }

    #[test]
    fn arithmetic_respects_precedence() {
        assert_eq!(eval("2 + 3 * 4"), Ok(Value::Int(14)));
    }

    #[test]
    fn shadowing_survives_substitution() {
        // Если подстановка захватывает переменные, здесь получится 2.
        assert_eq!(
            eval("let x = 1 in (\\y -> \\x -> y) x 2"),
            Ok(Value::Int(1))
        );
    }

    #[test]
    fn recursion_terminates_on_a_decreasing_argument() {
        assert_eq!(
            eval("let rec fact = \\n -> if n < 1 then 1 else n * fact (n - 1) in fact 10"),
            Ok(Value::Int(3_628_800))
        );
    }

    #[test]
    fn divergence_hits_the_step_limit_instead_of_hanging() {
        assert!(matches!(
            eval("fix (\\f -> f)"),
            Err(Error::StepLimit { .. })
        ));
    }

    #[test]
    fn overflow_is_an_error_not_a_wrap() {
        assert_eq!(
            eval("let m = 9223372036854775807 in m + 1"),
            Err(Error::Overflow)
        );
    }

    #[test]
    fn functions_print_opaquely() {
        assert_eq!(
            eval("\\x -> x").map(|v| v.to_string()),
            Ok("<fun>".to_owned())
        );
    }
}

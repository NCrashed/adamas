//! Проверка тотальности: структурная рекурсия (§4.7, §9 Фаза 1).
//!
//! С появлением рекурсии ядро перестало гарантировать завершаемость само по
//! себе - это цена выбора `case` вместо рекурсоров (decision log 2026-08-24).
//! Держат её здесь, и результат нужен ядру в двух местах:
//!
//! - **δ-разворот** ([`crate::conv`]) нетотальное определение не трогает вовсе,
//!   поэтому проверка конвертируемости завершается независимо от того, что
//!   пользователь написал;
//! - **стёртый фрагмент** ([`crate::check`]) нетотальное определение не
//!   принимает: §4.7 запрещает нетотальным функциям участвовать в
//!   доказательствах, а типы - тот же фрагмент.
//!
//! # Что считается уменьшением
//!
//! Параметры определения нумеруются, и каждому связыванию сопоставляется
//! "размер" - пара "номер параметра, глубина разбора". Разбор по значению
//! размера `(i, d)` даёт полям размер `(i, d+1)`: поле конструктора строго
//! меньше разобранного значения. Рекурсивный вызов засчитывается уменьшающимся
//! по позиции `k`, если его `k`-й аргумент - переменная размера `(k, d)` при
//! `d > 0`.
//!
//! Определение тотально, если такая позиция `k` **одна на все** рекурсивные
//! вызовы. Позиция ищется перебором - объявлять её, как `{struct n}` в Coq,
//! незачем.
//!
//! # Разбор под применением
//!
//! Ветвь связывает лямбдами не только поля: элаборация клауз выносит соседние
//! аргументы в мотив и применяет разбор обратно к ним (convoy - иначе тип
//! соседа не уточнить). Лямбды сверх полей связывают ровно эти аргументы, и
//! размеры им раздаются от применения. Без раздачи убывание терялось бы на
//! каждом аргументе, прошедшем через уточнение, - то есть ровно на тех, ради
//! которых пишут индексированные семейства.
//!
//! # Что не покрыто
//!
//! Лексикографический порядок (`ack`), well-founded рекурсия с явной мерой,
//! взаимная рекурсия. Последняя невозможна и по построению сигнатуры
//! (ordered scoping, §4.8), остальное - отдельная работа. Проверка
//! консервативна: отвергает часть завершающихся определений, но не пропускает
//! расходящиеся.

use crate::mult::Mult;
use crate::sig::{Definition, Signature};
use crate::term::{Case, Index, Name, Term, spine};

/// Размер связывания относительно параметров определения.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Size {
    /// Номер параметра, от которого связывание произошло.
    argument: usize,
    /// Сколько разборов отделяет его от самого параметра.
    depth: u32,
}

/// Завершается ли определение на всех входах.
///
/// Постулат тотален: тела нет, разворачивать нечего. Определение без
/// рекурсивных вызовов тотально, если тотально всё, что оно зовёт.
#[must_use]
pub fn is_total(signature: &Signature, name: &Name, definition: &Definition) -> bool {
    let Some(body) = &definition.body else {
        return true;
    };

    // Тотальность распространяется по графу вызовов (§4.7). Отдельного обхода
    // это не требует: определения добавляются по одному и каждое уже несёт свой
    // вердикт, поэтому достаточно посмотреть на непосредственно вызванные.
    if calls_a_partial_definition(signature, name, body) {
        return false;
    }

    let mut walk = Walk {
        signature,
        name,
        calls: Vec::new(),
    };
    let mut sizes = Vec::new();
    let arity = walk.parameters(&mut sizes, body);
    walk.calls.is_empty()
        || (0..arity).any(|position| {
            walk.calls.iter().all(|call| {
                matches!(
                    call.get(position),
                    Some(&Some(Size { argument, depth }))
                        if argument == position && depth > 0
                )
            })
        })
}

/// Зовёт ли тело хоть одно нетотальное определение.
///
/// Собственное имя пропускается: рекурсию разбирает структурная проверка, а на
/// этом шаге определение ещё числится тотальным по умолчанию.
fn calls_a_partial_definition(signature: &Signature, name: &Name, term: &Term) -> bool {
    let recur = |inner| calls_a_partial_definition(signature, name, inner);
    match term {
        Term::Var(_) | Term::Universe(_) | Term::Meta(_) => false,
        Term::Record(fields) => fields.iter().any(|field| recur(&field.ty)),
        Term::Object(fields) => fields.iter().any(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Const(other, _) => {
            other != name && signature.lookup(other).is_some_and(|found| !found.total)
        }
        Term::Lam(_, _, body) => recur(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || recur(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(recur)
        }
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || recur(body),
        Term::Case(case) => {
            recur(&case.scrutinee)
                || recur(&case.motive)
                || case.branches.iter().any(|branch| recur(&branch.body))
        }
    }
}

/// Обход тела с накоплением рекурсивных вызовов.
struct Walk<'a> {
    signature: &'a Signature,
    name: &'a Name,
    /// Для каждого вызова - размеры его аргументов по позициям.
    calls: Vec<Vec<Option<Size>>>,
}

impl Walk<'_> {
    /// Снимает лямбды-параметры, приписывая каждой её номер, и обходит тело.
    ///
    /// Возвращает число снятых параметров - только по ним и ищется уменьшение.
    fn parameters(&mut self, sizes: &mut Vec<Option<Size>>, term: &Term) -> usize {
        match term {
            Term::Lam(_, _, body) => {
                sizes.push(Some(Size {
                    argument: sizes.len(),
                    depth: 0,
                }));
                self.parameters(sizes, body)
            }
            other => {
                let arity = sizes.len();
                self.term(sizes, other);
                arity
            }
        }
    }

    /// Размер связывания, на которое указывает индекс.
    fn size(sizes: &[Option<Size>], term: &Term) -> Option<Size> {
        let Term::Var(Index(index)) = term else {
            return None;
        };
        let level = sizes.len().checked_sub(*index as usize + 1)?;
        *sizes.get(level)?
    }

    fn term(&mut self, sizes: &mut Vec<Option<Size>>, term: &Term) {
        match term {
            // Дырка размера не несёт и вызовом не является: она замкнута, а
            // зависимость от контекста выражена применениями вокруг неё.
            Term::Var(_) | Term::Universe(_) | Term::Meta(_) => {}

            // ÐÐ°Ð¿Ð¸ÑÑ ÑÐ°Ð·Ð¼ÐµÑÐ° Ð½Ðµ Ð½ÐµÑÑÑ: Ð¿Ð¾Ð»Ñ - ÑÐ¸Ð¿Ñ Ð¸ Ð·Ð½Ð°ÑÐµÐ½Ð¸Ñ, Ð° ÑÐ¼ÐµÐ½ÑÑÐµÐ½Ð¸Ðµ
            // ÑÑÐ¸ÑÐ°ÐµÑÑÑ Ð¿Ð¾ ÑÐ°Ð·Ð±Ð¾ÑÑ. ÐÐ±ÑÐ¾Ð´ Ð½ÑÐ¶ÐµÐ½, ÑÑÐ¾Ð±Ñ Ð²ÑÐ·Ð¾Ð²Ñ Ð²Ð½ÑÑÑÐ¸ Ð½Ð°ÑÐ»Ð¸ÑÑ.
            Term::Record(fields) => {
                for field in fields.iter() {
                    self.term(sizes, &field.ty);
                }
            }
            Term::Object(fields) => {
                for (_, value) in fields.iter() {
                    self.term(sizes, value);
                }
            }
            Term::Project(record, _) => self.term(sizes, record),

            // Голое имя без аргументов - тоже вызов, просто без единой
            // позиции, по которой можно было бы уменьшаться.
            Term::Const(other, _) => {
                if other == self.name {
                    self.calls.push(Vec::new());
                }
            }

            Term::Lam(_, _, body) => self.under(sizes, None, body),

            Term::App(..) => {
                let (head, arguments) = spine(term);
                let applied: Vec<Option<Size>> = arguments
                    .iter()
                    .map(|argument| Self::size(sizes, argument))
                    .collect();
                match head {
                    Term::Const(other, _) if other == self.name => self.calls.push(applied),
                    // Convoy: аргументы применения - те самые соседи, которые
                    // ветвь связывает лямбдами сверх полей.
                    Term::Case(case) => self.case(sizes, case, &applied),
                    other => self.term(sizes, other),
                }
                for argument in arguments {
                    self.term(sizes, argument);
                }
            }

            Term::Pi(_, _, domain, row, codomain) => {
                self.term(sizes, domain);
                self.under(sizes, None, codomain);
                // Аргументы меток стоят под тем же контекстом, что домен:
                // связывание `Pi` вводится только для кодомена.
                for argument in row.labels().iter().flat_map(|label| &label.arguments) {
                    self.term(sizes, argument);
                }
            }

            Term::Let(_, _, ty, value, body) => {
                self.term(sizes, ty);
                self.term(sizes, value);
                // Связывание `let` размера не несёт: значение известно, но
                // отследить его убывание эта проверка не берётся.
                self.under(sizes, None, body);
            }

            Term::Case(case) => self.case(sizes, case, &[]),
        }
    }

    /// Обходит разбор, раздавая ветвям размеры аргументов, к которым он
    /// применён.
    fn case(&mut self, sizes: &mut Vec<Option<Size>>, case: &Case, applied: &[Option<Size>]) {
        self.term(sizes, &case.scrutinee);
        self.term(sizes, &case.motive);
        // Поля строго меньше разобранного значения - здесь и только здесь
        // размер растёт в глубину.
        let smaller = Self::size(sizes, &case.scrutinee).map(|size| Size {
            argument: size.argument,
            depth: size.depth + 1,
        });
        for branch in &case.branches {
            let fields = self.fields(&branch.constructor, case.params);
            self.branch(sizes, fields, smaller, applied, &branch.body);
        }
    }

    /// Сколько полей связывает ветвь конструктора.
    fn fields(&self, constructor: &Name, params: u32) -> usize {
        let Some(declaration) = self.signature.lookup(constructor) else {
            return 0;
        };
        let mut binders = 0usize;
        let mut current = &declaration.ty;
        while let Term::Pi(_, _, _, _, codomain) = current {
            binders += 1;
            current = codomain;
        }
        binders.saturating_sub(params as usize)
    }

    /// Обходит тело ветви, раздавая её полям размер `smaller`.
    ///
    /// Ветвь - функция от полей, но быть записанной лямбдами она не обязана
    /// (η). Что не снялось лямбдами, обходится как обычный терм: размеров такие
    /// поля не получают, и рекурсия по ним не засчитывается.
    fn branch(
        &mut self,
        sizes: &mut Vec<Option<Size>>,
        fields: usize,
        smaller: Option<Size>,
        applied: &[Option<Size>],
        term: &Term,
    ) {
        match (fields, term) {
            (0, other) => self.convoyed(sizes, applied, other),
            (_, Term::Lam(_, _, body)) => {
                sizes.push(smaller);
                self.branch(sizes, fields - 1, smaller, applied, body);
                sizes.pop();
            }
            // Поля кончились не лямбдами: до аргументов применения такая ветвь
            // не добирается, и раздавать их размеры некому.
            (_, other) => self.term(sizes, other),
        }
    }

    /// Обходит то, что осталось от ветви после полей, раздавая лямбдам размеры
    /// аргументов применения - каждой свой, слева направо.
    fn convoyed(&mut self, sizes: &mut Vec<Option<Size>>, applied: &[Option<Size>], term: &Term) {
        match (applied.split_first(), term) {
            (Some((first, rest)), Term::Lam(_, _, body)) => {
                sizes.push(*first);
                self.convoyed(sizes, rest, body);
                sizes.pop();
            }
            (_, other) => self.term(sizes, other),
        }
    }

    /// Обходит терм под одним связыванием.
    fn under(&mut self, sizes: &mut Vec<Option<Size>>, size: Option<Size>, term: &Term) {
        sizes.push(size);
        self.term(sizes, term);
        sizes.pop();
    }
}

/// Допустимо ли определение в стёртом фрагменте (§4.7).
///
/// Нетотальная функция не может участвовать в доказательствах, а типы живут в
/// том же фрагменте, поэтому проверка одна на оба случая.
#[must_use]
pub fn admits(definition: &Definition, sigma: Mult) -> bool {
    definition.total || sigma != Mult::Zero
}

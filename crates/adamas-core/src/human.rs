//! Печать типов для человека (§7.6).
//!
//! Ядро печатает термы так, как их хранит: индексы де Брёйна, кратность у
//! каждого связывания, уровни вселенных, хвост row, номера дырок, полные
//! имена. Это нужно снимкам ядра и отладке - и мешает автору программы, у
//! которого в сигнатуре написано `{e : Type} -> ({Except e} a) -> Result e a`.
//!
//! Человеческая печать - два шага. [`humane`] переписывает терм: переменные
//! становятся именами связываний (совпавшее имя получает номер: `a1`),
//! неупомянутое связывание - `_`, дырка - `_`, уровни и хвосты row снимаются,
//! полное имя сокращается, если коротко оно в программе однозначно. Флаг
//! [`humanly`] велит печати опускать кратность по умолчанию - `ω` у явного
//! связывания, `0` у неявного - и уровень у `Type`.
//!
//! Чего человеческая печать не прячет: отказ, у которого обе стороны в ней
//! совпали, печатает их полными формами - иначе вернулось бы «ожидался X,
//! получен X», и различие оказалось бы как раз в спрятанном (решение
//! 2026-10-07).

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::mult::Mult;
use crate::row::{Label, Row};
use crate::term::{Args, Field, Fields, Index, Name, Term};
use crate::visibility::Visibility;

thread_local! {
    /// Печатать ли по-человечески: включает [`humanly`].
    static HUMAN: Cell<bool> = const { Cell::new(false) };
    /// Короткие имена, которые в программе объявлены больше одного раза.
    /// `None` - программа ещё не прочитана, и сокращать имена не по чему.
    static AMBIGUOUS: RefCell<Option<HashSet<String>>> = RefCell::default();
    /// Сколько ведущих неявных параметров у определения: столько аргументов
    /// его применения автор не писал, и печать их не показывает.
    static IMPLICITS: RefCell<HashMap<String, usize>> = RefCell::default();
}

/// Исполняет `body` с человеческой печатью.
pub fn humanly<R>(body: impl FnOnce() -> R) -> R {
    let was = HUMAN.with(|it| it.replace(true));
    let answer = body();
    HUMAN.with(|it| it.set(was));
    answer
}

/// Печатать ли сейчас по-человечески.
pub(crate) fn human() -> bool {
    HUMAN.with(Cell::get)
}

/// Записывает имена программы: по ним решается, однозначно ли короткое имя.
///
/// Запись одна на поток и заменяется программой целиком, как и перечень
/// заслонённых имён прелюдии ([`crate::term::shadow_prelude`]).
pub fn note_names<'a>(names: impl IntoIterator<Item = &'a str>) {
    let mut seen: HashMap<&str, u32> = HashMap::new();
    // Невыразимые имена - элиминаторы `#handle.M`, `#mask.M` - автор не
    // пишет и в типе не увидит, и счёт они бы испортили.
    for name in names.into_iter().filter(|it| !it.starts_with('#')) {
        *seen.entry(crate::term::short(name)).or_default() += 1;
    }
    let ambiguous: HashSet<String> = seen
        .into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(name, _)| name.to_owned())
        .collect();
    AMBIGUOUS.with(|it| *it.borrow_mut() = Some(ambiguous));
}

/// Записывает число ведущих неявных параметров каждого определения: их
/// аргументы печать прячет - `x /= 0`, а не `/= Int64 Eq#Int64 x 0`.
pub fn note_implicits<'a>(arities: impl IntoIterator<Item = (&'a str, usize)>) {
    let arities = arities
        .into_iter()
        .filter(|(_, count)| *count > 0)
        .map(|(name, count)| (name.to_owned(), count))
        .collect();
    IMPLICITS.with(|it| *it.borrow_mut() = arities);
}

/// Забывает имена прошлой программы: пока новая не прочитана, имена
/// печатаются полными.
pub fn forget_names() {
    AMBIGUOUS.with(|it| *it.borrow_mut() = None);
    IMPLICITS.with(|it| it.borrow_mut().clear());
}

/// Имя так, как его написал бы автор: без модуля, если короткое однозначно.
#[must_use]
pub fn named(name: &str) -> Name {
    let short = crate::term::short(name);
    // Имя, занятое языком (`arrayIndex`, `Type`), сокращению не подлежит:
    // одноимённый член модуля печатался бы примитивом.
    let taken = crate::prim::Prim::named(short).is_some() || short == "Type" || short == "Effect";
    let unique =
        !taken && AMBIGUOUS.with(|it| it.borrow().as_ref().is_some_and(|set| !set.contains(short)));
    if short.len() < name.len() && unique {
        Name::from(short)
    } else {
        Name::from(crate::term::written_name(name))
    }
}

/// Терм для человеческой печати.
#[must_use]
pub fn humane(term: &Term) -> Term {
    Humane::default().term(term)
}

/// Row для человеческой печати: без хвоста.
#[must_use]
pub fn humane_row(row: &Row<Term>) -> Row<Term> {
    Humane::default().row(row)
}

/// Имена связываний, под которыми идёт переписывание: внутреннее - последнее.
#[derive(Default)]
struct Humane {
    bound: Vec<Name>,
}

impl Humane {
    /// Имя нового связывания: написанное, если оно свободно, иначе с номером.
    fn fresh(&self, written: &str) -> Name {
        let base = if written == "_" { "x" } else { written };
        if !self.bound.iter().any(|it| **it == *base) {
            return Name::from(base);
        }
        (1..u32::MAX)
            .map(|n| format!("{base}{n}"))
            .find(|it| !self.bound.iter().any(|bound| **bound == **it))
            .map_or_else(|| Name::from(base), |it| Name::from(it.as_str()))
    }

    /// Ограничение-факт `{claim} =>`: связывание безымянное и неупомянутое,
    /// кратность - та, при которой печать пишет ограничение.
    fn fact(&mut self, claim: &Term, row: &Row<Term>, codomain: &Term) -> Term {
        let domain = Rc::new(self.term(claim));
        let shown = Name::from("_");
        self.under(Rc::clone(&shown), |this| {
            let row = this.row(row);
            let codomain = Rc::new(this.term(codomain));
            Term::Pi(
                crate::term::Binder::implicit(Mult::Many),
                shown,
                domain,
                row,
                codomain,
            )
        })
    }

    /// Применение без аргументов на месте ведущих неявных параметров головы:
    /// их подставил вывод, а не автор.
    fn application(&mut self, term: &Term) -> Term {
        let mut arguments = Vec::new();
        let mut head = term;
        while let Term::App(callee, argument) = head {
            arguments.push(&**argument);
            head = callee;
        }
        arguments.reverse();
        let hidden = match head {
            Term::Const(name, _, _) => IMPLICITS
                .with(|it| it.borrow().get(&**name).copied())
                .filter(|count| *count <= arguments.len())
                .unwrap_or(0),
            _ => 0,
        };
        let head = self.term(head);
        arguments[hidden..].iter().fold(head, |callee, argument| {
            Term::App(Rc::new(callee), Rc::new(self.term(argument)))
        })
    }

    fn under<R>(&mut self, name: Name, body: impl FnOnce(&mut Self) -> R) -> R {
        self.bound.push(name);
        let answer = body(self);
        self.bound.pop();
        answer
    }

    fn term(&mut self, term: &Term) -> Term {
        let recur = |this: &mut Self, it: &Rc<Term>| Rc::new(this.term(it));
        match term {
            Term::Var(Index(index)) => {
                let index = *index as usize;
                // Свободная переменная остаётся индексом: связывания терма
                // стоят на месте, и назвать её по контексту может тот, кто
                // контекст знает (`adamas-elab`, отказ с телескопом).
                match self.bound.len().checked_sub(index + 1) {
                    Some(at) => Term::Const(Rc::clone(&self.bound[at]), Rc::from([]), Args::none()),
                    None => term.clone(),
                }
            }
            Term::Meta(_) => Term::Const(Name::from("_"), Rc::from([]), Args::none()),
            Term::Const(name, _, args) => Term::Const(
                named(name),
                Rc::from([]),
                Args::new(
                    args.row_args()
                        .iter()
                        .map(|row| self.row(row))
                        .collect::<Vec<_>>(),
                    args.mult_args().to_vec(),
                ),
            ),
            // Дырка, применённая к контексту места, где её завели, - тоже дырка:
            // спайн пересказывает контекст, а не программу.
            Term::App(..) if hole(term) => Term::Const(Name::from("_"), Rc::from([]), Args::none()),
            Term::App(..) => self.application(term),
            // Факт `{d /= 0} =>` печатается так, как написан (§3.7): утверждение
            // без `Equal Bool _ True` вокруг.
            Term::Pi(binder, _, domain, row, codomain)
                if binder.visibility == Visibility::Implicit
                    && !codomain.mentions_recent(0, 1)
                    && claim(domain).is_some() =>
            {
                self.fact(claim(domain).unwrap_or(domain), row, codomain)
            }
            Term::Pi(binder, name, domain, row, codomain) => {
                let domain = recur(self, domain);
                let used = codomain.mentions_recent(0, 1)
                    || row
                        .labels()
                        .iter()
                        .flat_map(|label| &label.arguments)
                        .any(|argument| argument.mentions_recent(0, 1));
                // Неупомянутое явное связывание печатается стрелкой `A -> B`,
                // неупомянутое неявное кратности `ω` - ограничением `{Ord a} =>`,
                // и имя им не нужно; прочее неявное имя держит - `{a : Type}`.
                let constraint =
                    binder.visibility == Visibility::Implicit && binder.mult == Mult::Many;
                let shown = if used || (binder.visibility == Visibility::Implicit && !constraint) {
                    self.fresh(name)
                } else {
                    Name::from("_")
                };
                self.under(Rc::clone(&shown), |this| {
                    let row = this.row(row);
                    let codomain = recur(this, codomain);
                    Term::Pi(*binder, shown, domain, row, codomain)
                })
            }
            Term::Lam(mult, name, body) => {
                let shown = self.fresh(name);
                self.under(Rc::clone(&shown), |this| {
                    Term::Lam(*mult, shown, recur(this, body))
                })
            }
            Term::Let(mult, name, ty, value, body) => {
                let ty = recur(self, ty);
                let value = recur(self, value);
                let shown = self.fresh(name);
                self.under(Rc::clone(&shown), |this| {
                    Term::Let(*mult, shown, ty, value, recur(this, body))
                })
            }
            Term::Record(fields) => Term::Record(self.fields(fields)),
            Term::Row(fields) => Term::Row(self.fields(fields)),
            Term::Object(fields) => Term::Object(
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(self, value)))
                    .collect::<Vec<_>>()
                    .into(),
            ),
            Term::With(base, fields) => Term::With(
                recur(self, base),
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(self, value)))
                    .collect::<Vec<_>>()
                    .into(),
            ),
            Term::Project(record, name) => Term::Project(recur(self, record), Rc::clone(name)),
            // Разборы связывают поля ветвей, и пересказывать их связывания
            // здесь незачем: в типах, которые читает человек, разбор - редкость,
            // и он печатается как есть.
            Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Prim(_)
            | Term::Split(_)
            | Term::Case(_) => term.clone(),
        }
    }

    /// Запись - телескоп: тип поля стоит под предыдущими полями.
    fn fields(&mut self, fields: &Fields) -> Fields {
        let mut written = Vec::with_capacity(fields.fields.len());
        for field in fields.fields.iter() {
            written.push(Field {
                ty: Rc::new(self.term(&field.ty)),
                ..field.clone()
            });
            self.bound.push(Rc::clone(&field.name));
        }
        let tail = fields.tail.as_ref().map(|tail| Rc::new(self.term(tail)));
        self.bound.truncate(self.bound.len() - fields.fields.len());
        Fields {
            fields: written.into(),
            tail,
        }
    }

    /// Row без хвоста: автор хвоста не пишет, его дописывает подъём (§3.4).
    fn row(&mut self, row: &Row<Term>) -> Row<Term> {
        let labels: Vec<Label<Term>> = row
            .labels()
            .iter()
            .map(|label| Label {
                name: named(&label.name),
                arguments: label.arguments.iter().map(|it| self.term(it)).collect(),
            })
            .collect();
        Row::closing(labels, None)
    }
}

/// Кратность связывания, которую человеческая печать не пишет: `ω` у явного,
/// `0` у неявного.
pub(crate) fn implied(mult: Mult, visibility: Visibility) -> bool {
    matches!(
        (mult, visibility),
        (Mult::Many, Visibility::Explicit) | (Mult::Zero, Visibility::Implicit)
    )
}

/// Тип конструктора человеческой печатью: поле кратности `1` - умолчание
/// поля конструктора (§4.1), и пишется оно просто `A -> …`; поле, кратность
/// которого написана иначе, - со своей кратностью, `(ω _ : A) -> …`.
///
/// Отдельная функция, потому что печать терма не знает, чей это тип: у
/// функции умолчание - `ω`, и тот же `(1 _ : Nat) -> Nat` значит там
/// линейный параметр. Знает спросивший - подсказка редактора и `--type`.
#[must_use]
pub fn constructor(ty: &Term) -> String {
    let ty = humane(ty);
    humanly(|| {
        let mut out = String::new();
        let mut rest = &ty;
        while let Term::Pi(binder, name, domain, row, codomain) = rest {
            let row = if row.is_empty() {
                String::new()
            } else {
                format!(" {}", row.to_string().trim_end())
            };
            let field = match (binder.visibility, binder.mult, &**name) {
                (Visibility::Explicit, Mult::One, "_") => domain.as_domain(),
                (Visibility::Explicit, Mult::One, name) => format!("({name} : {domain})"),
                (Visibility::Explicit, mult, name) => format!("({mult} {name} : {domain})"),
                (Visibility::Implicit, mult, name) if implied(mult, Visibility::Implicit) => {
                    format!("{{{name} : {domain}}}")
                }
                (Visibility::Implicit, mult, name) => format!("{{{mult} {name} : {domain}}}"),
            };
            out.push_str(&field);
            out.push_str(" ->");
            out.push_str(&row);
            out.push(' ');
            rest = codomain;
        }
        out.push_str(&rest.to_string());
        out
    })
}

/// Голова применения - дырка.
/// Утверждение факта `Equal Bool claim True`. Имена сверяются коротко: печать
/// сигнатуры не видит, как и у единицы вычисления.
fn claim(ty: &Term) -> Option<&Term> {
    let named = |term: &Term, name: &str| matches!(term, Term::Const(it, _, _) if crate::term::short(it) == name);
    let Term::App(applied, verdict) = ty else {
        return None;
    };
    let Term::App(applied, claim) = &**applied else {
        return None;
    };
    let Term::App(equal, carrier) = &**applied else {
        return None;
    };
    (named(equal, crate::prim::EQUAL)
        && named(carrier, crate::prim::BOOL)
        && named(verdict, crate::prim::TRUE))
    .then_some(&**claim)
}

fn hole(term: &Term) -> bool {
    let mut head = term;
    while let Term::App(callee, _) = head {
        head = callee;
    }
    matches!(head, Term::Meta(_))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::level::Level;
    use crate::term::Binder;
    use crate::visibility::Visibility;

    fn pi(binder: Binder, name: &str, domain: Term, codomain: Term) -> Term {
        Term::Pi(
            binder,
            Name::from(name),
            Rc::new(domain),
            Row::empty(),
            Rc::new(codomain),
        )
    }

    fn shown(term: &Term) -> String {
        let term = humane(term);
        humanly(|| term.to_string())
    }

    /// `{0 a : Type u0} -> (ω _ : a) -> a` - так, как пишет автор.
    #[test]
    fn a_polymorphic_identity_reads_as_written() {
        let implicit = Binder {
            mult: Mult::Zero,
            visibility: Visibility::Implicit,
        };
        let identity = pi(
            implicit,
            "a",
            Term::Universe(Level::Zero),
            pi(
                Binder::explicit(Mult::Many),
                "_",
                Term::var(0),
                Term::var(1),
            ),
        );
        assert_eq!(shown(&identity), "{a : Type} -> a -> a");
        assert_eq!(
            identity.to_string(),
            "{0 a : Type 0} -> (ω _ : #0) -> #1",
            "полная печать не тронута"
        );
    }

    /// Факт `{d /= 0} =>` печатается утверждением, оператор - между
    /// операндами, а аргументы неявных параметров оператора не печатаются:
    /// их подставил вывод (§3.7, §7.6).
    #[test]
    fn a_fact_reads_as_its_written_claim() {
        let named = |name: &str| Term::Const(Name::from(name), Rc::from([]), Args::none());
        let apply = |head: Term, arguments: Vec<Term>| {
            arguments.into_iter().fold(head, |callee, argument| {
                Term::App(Rc::new(callee), Rc::new(argument))
            })
        };
        note_implicits([("/=", 2)]);
        let claim = apply(
            named("/="),
            vec![
                named("Int64"),
                named("Eq#Int64"),
                Term::var(0),
                Term::Prim(crate::prim::Prim::Lit(
                    crate::prim::PrimTy::Int64,
                    0,
                )),
            ],
        );
        let fact = apply(named("Equal"), vec![named("Bool"), claim, named("True")]);
        let ty = pi(
            Binder::explicit(Mult::Many),
            "d",
            named("Int64"),
            pi(Binder::implicit(Mult::Zero), "_", fact, named("Int64")),
        );
        assert_eq!(shown(&ty), "(d : Int64) -> {d /= 0} => Int64");
        forget_names();
    }

    /// У поля конструктора умолчание - `1`: такое поле пишется стрелкой, а
    /// написанное иначе - со своей кратностью.
    #[test]
    fn a_constructor_field_hides_its_default_multiplicity() {
        let named = |name: &str| Term::Const(Name::from(name), Rc::from([]), Args::none());
        let field = pi(
            Binder::explicit(Mult::One),
            "_",
            named("Nat"),
            pi(
                Binder::explicit(Mult::Many),
                "_",
                named("Nat"),
                named("Pair"),
            ),
        );
        assert_eq!(constructor(&field), "Nat -> (ω _ : Nat) -> Pair");
        assert_eq!(
            shown(&field),
            "(1 _ : Nat) -> Nat -> Pair",
            "у функции умолчание другое"
        );
    }

    /// Упомянутое связывание держит имя, совпавшее - получает номер, а
    /// кратность не по умолчанию пишется.
    #[test]
    fn a_dependent_binder_keeps_its_name_and_a_clash_gets_a_number() {
        let nat = || Term::Const(Name::from("Nat"), Rc::from([]), Args::none());
        let vect = |n: Term| {
            Term::App(
                Rc::new(Term::Const(Name::from("Vect"), Rc::from([]), Args::none())),
                Rc::new(n),
            )
        };
        let inner = pi(
            Binder::explicit(Mult::One),
            "n",
            vect(Term::var(0)),
            vect(Term::var(0)),
        );
        let outer = pi(Binder::explicit(Mult::Many), "n", nat(), inner);
        assert_eq!(shown(&outer), "(n : Nat) -> (1 n1 : Vect n) -> Vect n1");
    }
}

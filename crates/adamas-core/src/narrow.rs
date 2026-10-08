//! Сужение `if`, которым никто не воспользовался (§3.7).
//!
//! Элаборация пишет `if c then a else b` разбором `inspect c` прелюдии: ветви
//! получают стёртый факт `c` либо `not c`, и ограничение-факт внутри ветви
//! находит доказательство гипотезой контекста. Решает это поиск, и узнать на
//! месте `if`, понадобится ли факт, нечем.
//!
//! Ветвь, чья гипотеза так и осталась неупомянутой, переписывается обратно в
//! разбор самого условия - здесь, после зонканья, когда решения подставлены.
//! Цена у формы с гипотезой двоякая: условие стоит в типе, и специализация
//! обязана его там типизировать (`key == k` над словарём `Eq String`, который
//! не тотален, - отказ); и исполнитель зовёт `inspect` на каждом `if`. Ни то
//! ни другое не нужно `if`, которому факт не понадобился, - а таких почти все.

use std::rc::Rc;

use crate::sig::Signature;
use crate::term::{Args, Branch, Case, Index, Term};

/// Терм с переписанными неиспользованными сужениями.
#[must_use]
pub fn plain(signature: &Signature, term: &Term) -> Term {
    let inspect = format!("{}.{}", crate::prim::PRELUDE, crate::prim::INSPECT);
    if signature.lookup(&inspect).is_none() {
        return term.clone();
    }
    Plain {
        signature,
        inspect: &inspect,
    }
    .term(term)
}

struct Plain<'a> {
    signature: &'a Signature,
    inspect: &'a str,
}

impl Plain<'_> {
    fn term(&self, term: &Term) -> Term {
        let recur = |inner: &Rc<Term>| Rc::new(self.term(inner));
        match term {
            Term::Let(mult, name, ty, value, body) => {
                let rebuilt = (recur(ty), recur(value), recur(body));
                self.unnarrowed(*mult, name, &rebuilt.1, &rebuilt.2)
                    .unwrap_or_else(|| {
                        Term::Let(*mult, Rc::clone(name), rebuilt.0, rebuilt.1, rebuilt.2)
                    })
            }
            Term::Var(_)
            | Term::Meta(_)
            | Term::EffectKind
            | Term::Universe(_)
            | Term::Prim(_)
            | Term::RowKind(_)
            | Term::Const(..)
            | Term::Record(_)
            | Term::Row(_) => term.clone(),
            Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), recur(body)),
            Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
            Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
                *binder,
                Rc::clone(name),
                recur(domain),
                row.clone(),
                recur(codomain),
            ),
            Term::Object(fields) => Term::Object(
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Term::With(base, fields) => Term::With(
                recur(base),
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Term::Project(record, name) => Term::Project(recur(record), Rc::clone(name)),
            Term::Split(split) => Term::Split(Rc::new(split.map(|it| self.term(it)))),
            Term::Case(case) => Term::Case(Rc::new(Case {
                data: Rc::clone(&case.data),
                levels: Rc::clone(&case.levels),
                params: case.params,
                consumed: case.consumed,
                scrutinee: recur(&case.scrutinee),
                motive: recur(&case.motive),
                branches: case
                    .branches
                    .iter()
                    .map(|branch| Branch {
                        constructor: Rc::clone(&branch.constructor),
                        body: recur(&branch.body),
                    })
                    .collect(),
            })),
        }
    }

    /// `let case = inspect c in case case of Then _ -> a; Else _ -> b` без
    /// упоминания гипотез - `let case = c in case case of True -> a; False ->
    /// b`. `None` - форма не та либо гипотеза в ветви названа.
    fn unnarrowed(
        &self,
        mult: crate::mult::Mult,
        name: &crate::term::Name,
        value: &Term,
        body: &Term,
    ) -> Option<Term> {
        let Term::App(callee, condition) = value else {
            return None;
        };
        if !matches!(&**callee, Term::Const(head, ..) if &**head == self.inspect) {
            return None;
        }
        let Term::Case(case) = body else {
            return None;
        };
        if !matches!(&*case.scrutinee, Term::Var(Index(0))) {
            return None;
        }
        // Мотив от исхода не зависит: тип ответа `if` один на обе ветви.
        if let Term::Lam(_, _, motive) = &*case.motive {
            if motive.mentions_recent(0, 1) {
                return None;
            }
        }
        let field = |constructor: &str| {
            let branch = case
                .branches
                .iter()
                .find(|it| crate::term::short(&it.constructor) == constructor)?;
            let Term::Lam(_, _, inner) = &*branch.body else {
                return None;
            };
            (!inner.mentions_recent(0, 1)).then(|| {
                crate::pattern::instantiate(
                    inner,
                    &Term::Const(
                        self.signature.convention(crate::prim::TRUE),
                        Rc::from([]),
                        Args::none(),
                    ),
                )
            })
        };
        let yes = field(crate::prim::THEN)?;
        let no = field(crate::prim::ELSE)?;
        let constant =
            |name: &str| Term::Const(self.signature.convention(name), Rc::from([]), Args::none());
        let plain = Case {
            data: self.signature.convention(crate::prim::BOOL),
            levels: Rc::from([]),
            params: 0,
            consumed: case.consumed,
            scrutinee: Rc::clone(&case.scrutinee),
            motive: Rc::clone(&case.motive),
            branches: vec![
                Branch {
                    constructor: self.signature.convention(crate::prim::TRUE),
                    body: Rc::new(yes),
                },
                Branch {
                    constructor: self.signature.convention(crate::prim::FALSE),
                    body: Rc::new(no),
                },
            ],
        };
        Some(Term::Let(
            mult,
            Rc::clone(name),
            Rc::new(constant(crate::prim::BOOL)),
            Rc::clone(condition),
            Rc::new(Term::Case(Rc::new(plain))),
        ))
    }
}

//! Упоминается ли связывание в теле - правило вставки `drop` (§3.3).
//!
//! # Почему на исходнике, а не на терме
//!
//! Вопрос «жив ли ресурс на выходе из scope» - это вопрос о **расходе**, и
//! точный ответ на него есть только у `check`: вхождение в стёртой позиции
//! ресурс не потребляет. Отдать этот ответ наружу ядро не может, не нося
//! маршрут на успешном пути (§10 вопрос 49а отверг ровно эту цену), поэтому
//! правило сформулировано так, чтобы решаться там, где написано: **ресурс,
//! имя которого не встречается в теле, закрывается автоматически** (§10
//! вопрос 71).
//!
//! Клауза при этом и есть ветвь, поэтому поветвенной вставки не возникает:
//! `f (Wrap h) = …` и `f Other = …` - два разных тела, и каждое отвечает за
//! себя само. На собранном дереве разбора то же самое потребовало бы
//! живучести по ветвям.
//!
//! # Что считается упоминанием
//!
//! **Позиция терма и только расходующая.** Тип - стёртый фрагмент: `let x : P h
//! = …` ресурс не расходует, поэтому упоминанием не считается, и `drop` всё
//! равно вставится. То же с аргументом, стоящим в `0`-параметре: `describe : (0
//! h : File) -> Bool` ресурс не потребляет, и `leaked h = describe h` обязана
//! его закрыть. Кратности параметров написаны в сигнатуре, поэтому спрашивать
//! ядро не приходится - хватает того же взгляда на написанное, каким правило
//! владения смотрит на голову типа.
//!
//! Голова применения считается известной, только если она **не затенена** - ни
//! связыванием на пути, ни связыванием снаружи выражения. Иначе локальная `k`
//! в `k h` взяла бы кратности одноимённой глобальной, и мы вставили бы `drop` к
//! расходующему вызову - то есть отвергли бы корректную программу.
//!
//! Направление ошибки одно и то же везде: лишний `drop` не вставляется
//! никогда. Пропущенный остался в двух местах, обоих за пределами того, что
//! видит это правило:
//!
//! - ресурс добыт разбором конструктора, а конструктор не в сигнатуре - такое
//!   бывает только внутри объявляемой группы (`mutual`, Фаза 3);
//! - ресурс пришёл в параметр, тип которого - переменная: голова написанного
//!   владением не объявлена, и деструктора взять неоткуда (§10 вопрос 76).
//!
//! # Затенение
//!
//! Учитывается: `\h -> …` внутри тела закрывает внешнее `h`, и упоминанием
//! оно не будет. Иначе `drop` не вставился бы там, где ресурс заведомо не
//! тронут.

use adamas_core::mult::Mult;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_parser::ast::{
    Alt, Binding, Chain, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind, Symbol,
};

/// Поиск расходующего упоминания.
///
/// Сигнатура нужна одному вопросу - в какой кратности стоит аргумент; список
/// локальных имён нужен другому - не затенена ли голова применения.
pub(crate) struct Spent<'a> {
    signature: &'a Signature,
    locals: &'a [Symbol],
}

impl<'a> Spent<'a> {
    pub(crate) fn new(signature: &'a Signature, locals: &'a [Symbol]) -> Self {
        Self { signature, locals }
    }

    /// Встречается ли `name` в позиции терма, где он расходуется.
    pub(crate) fn mentions(&self, name: &str, expr: &Expr) -> bool {
        self.in_expr(name, expr, &mut Vec::new())
    }

    /// Встречается ли имя в том, что стоит **после** связывания: в остальных
    /// связываниях того же `let` и в последующих операторах.
    pub(crate) fn in_bindings_body(&self, name: &str, tail: &[Binding], rest: &[Stmt]) -> bool {
        self.in_bindings(name, tail, rest, &mut Vec::new())
    }

    fn in_expr<'e>(&self, name: &str, expr: &'e Expr, bound: &mut Vec<&'e str>) -> bool {
        match &expr.kind {
            ExprKind::Name(found) => &*found.text == name,
            ExprKind::App(..) => self.in_application(name, expr, bound),
            // Аргумент типа стёрт, как и всё в позиции типа.
            ExprKind::TypeApp(callee, _) => self.in_expr(name, callee, bound),
            ExprKind::Lam { params, body } => {
                let names: Vec<&str> = params
                    .iter()
                    .flat_map(|param| match &param.kind {
                        LamParamKind::Pattern(pattern) => bindings_of(pattern),
                        LamParamKind::Binder(binder) => {
                            binder.names.iter().map(|it| &*it.text).collect()
                        }
                    })
                    .collect();
                !names.contains(&name)
                    && self.under(&names, bound, |it, bound| it.in_expr(name, body, bound))
            }
            ExprKind::Block(block) => self.in_stmts(name, &block.stmts, bound),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.in_expr(name, cond, bound)
                    || self.in_expr(name, then_branch, bound)
                    || self.in_expr(name, else_branch, bound)
            }
            ExprKind::Case { scrutinee, alts } => {
                self.in_expr(name, scrutinee, bound)
                    || alts.iter().any(|alt| self.in_alt(name, alt, bound))
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => {
                items.iter().any(|item| self.in_expr(name, item, bound))
            }
            ExprKind::Chain(chain) => self.in_chain(name, chain, bound),
            // `Pi` и стрелка - типы целиком: что в них написано, стёрто.
            ExprKind::Pi { .. } | ExprKind::Arrow(..) | ExprKind::Lit(_) | ExprKind::Hole => false,
        }
    }

    /// Применение: спайн разбирается целиком, потому что кратность аргумента
    /// известна по его номеру.
    fn in_application<'e>(&self, name: &str, expr: &'e Expr, bound: &mut Vec<&'e str>) -> bool {
        let mut arguments = Vec::new();
        let mut head = expr;
        while let ExprKind::App(callee, argument) = &head.kind {
            arguments.push(&**argument);
            head = callee;
        }
        arguments.reverse();
        if self.in_expr(name, head, bound) {
            return true;
        }
        let mults = self.mults(head, bound);
        arguments.iter().enumerate().any(|(position, argument)| {
            // Кратность неизвестна - считаем расходом: пропущенный `drop`
            // хуже лишнего только на утечку, а лишний отвергает корректное.
            mults.get(position) != Some(&Mult::Zero) && self.in_expr(name, argument, bound)
        })
    }

    /// Кратности параметров головы, если она объявленное имя и не затенена.
    fn mults(&self, head: &Expr, bound: &[&str]) -> Vec<Mult> {
        let ExprKind::Name(name) = &head.kind else {
            return Vec::new();
        };
        self.named_mults(&name.text, bound)
    }

    /// То же по имени: пустой список - «неизвестно», то есть расходует.
    fn named_mults(&self, name: &str, bound: &[&str]) -> Vec<Mult> {
        if bound.contains(&name) || self.locals.iter().any(|it| **it == *name) {
            return Vec::new();
        }
        let Some(definition) = self.signature.lookup(name) else {
            return Vec::new();
        };
        let mut mults = Vec::new();
        let mut current = &definition.ty;
        while let Term::Pi(mult, _, _, _, codomain) = current {
            mults.push(*mult);
            current = codomain;
        }
        mults
    }

    fn in_stmts<'e>(&self, name: &str, stmts: &'e [Stmt], bound: &mut Vec<&'e str>) -> bool {
        let Some((first, rest)) = stmts.split_first() else {
            return false;
        };
        match &first.kind {
            StmtKind::Expr(expr) => {
                self.in_expr(name, expr, bound) || self.in_stmts(name, rest, bound)
            }
            // Значение связывания видит **внешнее** имя, а последующие операторы
            // - уже новое: `let h = f h` расходует старое и заводит другое.
            StmtKind::Let(bindings) => self.in_bindings(name, bindings, rest, bound),
        }
    }

    fn in_bindings<'e>(
        &self,
        name: &str,
        bindings: &'e [Binding],
        rest: &'e [Stmt],
        bound: &mut Vec<&'e str>,
    ) -> bool {
        let Some((binding, tail)) = bindings.split_first() else {
            return self.in_stmts(name, rest, bound);
        };
        if self.in_expr(name, &binding.body, bound) {
            return true;
        }
        let own = [&*binding.name.text];
        &*binding.name.text != name
            && self.under(&own, bound, |it, bound| {
                it.in_bindings(name, tail, rest, bound)
            })
    }

    fn in_alt<'e>(&self, name: &str, alt: &'e Alt, bound: &mut Vec<&'e str>) -> bool {
        let names = bindings_of(&alt.pattern);
        !names.contains(&name)
            && self.under(&names, bound, |it, bound| {
                it.in_expr(name, &alt.body, bound)
            })
    }

    fn in_chain<'e>(&self, name: &str, chain: &'e Chain, bound: &mut Vec<&'e str>) -> bool {
        // Оператор - та же голова применения, операнды - два его аргумента.
        chain.tail.iter().any(|(operator, operand)| {
            let mults = self.named_mults(&operator.text, bound);
            &*operator.text == name
                || (mults.first() != Some(&Mult::Zero) && self.in_expr(name, &chain.head, bound))
                || (mults.get(1) != Some(&Mult::Zero) && self.in_expr(name, operand, bound))
        })
    }

    /// Выполняет `body` под связываниями `names`.
    fn under<'e, T>(
        &self,
        names: &[&'e str],
        bound: &mut Vec<&'e str>,
        body: impl FnOnce(&Self, &mut Vec<&'e str>) -> T,
    ) -> T {
        let depth = bound.len();
        bound.extend_from_slice(names);
        let outcome = body(self, bound);
        bound.truncate(depth);
        outcome
    }
}

/// Имена, которые связывает паттерн, - то есть затеняют внешнее.
fn bindings_of(pattern: &Pattern) -> Vec<&str> {
    match &pattern.kind {
        PatternKind::Name(found) => vec![&found.text],
        PatternKind::App { fields, .. } => fields.iter().flat_map(bindings_of).collect(),
        PatternKind::Tuple(items) => items.iter().flat_map(bindings_of).collect(),
        PatternKind::Wildcard | PatternKind::Lit(_) => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use adamas_core::sig::Signature;
    use adamas_parser::ast::{Decl, DeclKind};

    use super::Spent;

    /// Расход в пустой сигнатуре: голов, чьи кратности известны, здесь нет, и
    /// всякий аргумент считается расходующим. Кратности проверяются отдельно,
    /// на живых программах (`tests/programs.rs`).
    fn mentions(name: &str, expr: &adamas_parser::ast::Expr) -> bool {
        let signature = Signature::default();
        Spent::new(&signature, &[]).mentions(name, expr)
    }

    /// Тело определения `f h = <body>` из текста.
    fn body(source: &str) -> adamas_parser::ast::Expr {
        let module = adamas_parser::parse(source).expect("разбирается");
        let Some(Decl {
            kind: DeclKind::Clauses { clauses, .. },
            ..
        }) = module.decls.last()
        else {
            panic!("последнее объявление - клаузы")
        };
        clauses.last().expect("клауза одна").body.clone()
    }

    #[test]
    fn a_name_in_a_term_position_is_a_mention() {
        assert!(mentions("h", &body("f : A\nf h = g h\n")));
        assert!(mentions("h", &body("f : A\nf h = g (k h) x\n")));
        assert!(!mentions("h", &body("f : A\nf h = g x\n")));
    }

    #[test]
    fn a_name_in_a_type_position_is_not() {
        // Тип - стёртый фрагмент: упоминание там ресурс не расходует, и
        // считать его расходом значило бы пропустить `drop`.
        assert!(!mentions("h", &body("f : A\nf h = g (\\(x : P h) -> x)\n")));
        assert!(!mentions("h", &body("f : A\nf h = k (P h -> Q)\n")));
    }

    #[test]
    fn a_shadowing_binder_hides_the_outer_name() {
        assert!(!mentions("h", &body("f : A\nf h = \\h -> h\n")));
        assert!(mentions("h", &body("f : A\nf h = \\x -> h\n")));
        assert!(!mentions(
            "h",
            &body("f : A\nf h =\n  let h : T = z\n  g h\n")
        ));
        assert!(mentions(
            "h",
            &body("f : A\nf h =\n  let x : T = h\n  g x\n")
        ));
    }

    #[test]
    fn a_shadowing_pattern_hides_it_too() {
        assert!(!mentions(
            "h",
            &body("f : A\nf h = case x of\n  Wrap h -> h\n")
        ));
        assert!(mentions(
            "h",
            &body("f : A\nf h = case x of\n  Wrap y -> h\n")
        ));
    }
}

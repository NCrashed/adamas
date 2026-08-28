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
//! Только позиция терма. Тип - стёртый фрагмент: `let x : P h = …` ресурс не
//! расходует, поэтому упоминанием не считается, и `drop` всё равно вставится.
//! Так правило оказывается **точнее**, чем «встретилось имя».
//!
//! Направление ошибки одно и то же везде: лишний `drop` не вставляется
//! никогда - иначе отвергалась бы корректная программа. Пропущенный возможен,
//! и мест ровно три, все за пределами того, что видит это правило:
//!
//! - имя стоит в позиции терма, но попадает в `0`-параметр (`describe : (0 h :
//!   File) -> Bool`): расхода нет, а упоминание есть;
//! - ресурс добыт разбором конструктора - его тип живёт в объявлении
//!   конструктора, и отвечает за него рекурсия `drop` по полям (§3.3), которой
//!   ещё нет;
//! - ресурс пришёл в параметр, тип которого - переменная: голова написанного
//!   владением не объявлена, и деструктора взять неоткуда.
//!
//! # Затенение
//!
//! Учитывается: `\h -> …` внутри тела закрывает внешнее `h`, и упоминанием
//! оно не будет. Иначе `drop` не вставился бы там, где ресурс заведомо не
//! тронут.

use adamas_parser::ast::{
    Alt, Binding, Block, Chain, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind,
};

/// Встречается ли `name` в позиции терма внутри `expr`.
pub(crate) fn mentions(name: &str, expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Name(found) => &*found.text == name,
        ExprKind::App(callee, argument) => mentions(name, callee) || mentions(name, argument),
        // Аргумент типа стёрт, как и всё в позиции типа.
        ExprKind::TypeApp(callee, _) => mentions(name, callee),
        ExprKind::Lam { params, body } => {
            let shadowed = params.iter().any(|param| match &param.kind {
                LamParamKind::Pattern(pattern) => binds(name, pattern),
                LamParamKind::Binder(binder) => binder.names.iter().any(|it| &*it.text == name),
            });
            !shadowed && mentions(name, body)
        }
        ExprKind::Block(block) => in_block(name, block),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => mentions(name, cond) || mentions(name, then_branch) || mentions(name, else_branch),
        ExprKind::Case { scrutinee, alts } => {
            mentions(name, scrutinee) || alts.iter().any(|alt| in_alt(name, alt))
        }
        ExprKind::Tuple(items) | ExprKind::List(items) => {
            items.iter().any(|item| mentions(name, item))
        }
        ExprKind::Chain(chain) => in_chain(name, chain),
        // `Pi` и стрелка - типы целиком: что в них написано, стёрто.
        ExprKind::Pi { .. } | ExprKind::Arrow(..) | ExprKind::Lit(_) | ExprKind::Hole => false,
    }
}

/// То же для последовательности операторов блока.
pub(crate) fn in_stmts(name: &str, stmts: &[Stmt]) -> bool {
    let Some((first, rest)) = stmts.split_first() else {
        return false;
    };
    match &first.kind {
        StmtKind::Expr(expr) => mentions(name, expr) || in_stmts(name, rest),
        // Значение связывания видит **внешнее** имя, а последующие операторы -
        // уже новое: `let h = f h` расходует старое и заводит другое.
        StmtKind::Let(bindings) => in_bindings(name, bindings, rest),
    }
}

fn in_bindings(name: &str, bindings: &[Binding], rest: &[Stmt]) -> bool {
    let Some((binding, tail)) = bindings.split_first() else {
        return in_stmts(name, rest);
    };
    if mentions(name, &binding.body) {
        return true;
    }
    &*binding.name.text != name && in_bindings(name, tail, rest)
}

fn in_block(name: &str, block: &Block) -> bool {
    in_stmts(name, &block.stmts)
}

fn in_alt(name: &str, alt: &Alt) -> bool {
    !binds(name, &alt.pattern) && mentions(name, &alt.body)
}

fn in_chain(name: &str, chain: &Chain) -> bool {
    mentions(name, &chain.head)
        || chain
            .tail
            .iter()
            .any(|(operator, operand)| &*operator.text == name || mentions(name, operand))
}

/// Связывает ли паттерн это имя - то есть затеняет ли внешнее.
fn binds(name: &str, pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Name(found) => &*found.text == name,
        PatternKind::App { fields, .. } => fields.iter().any(|field| binds(name, field)),
        PatternKind::Tuple(items) => items.iter().any(|item| binds(name, item)),
        PatternKind::Wildcard | PatternKind::Lit(_) => false,
    }
}

/// Встречается ли имя в том, что стоит **после** связывания: в остальных
/// связываниях того же `let` и в последующих операторах.
pub(crate) fn in_bindings_body(name: &str, tail: &[Binding], rest: &[Stmt]) -> bool {
    in_bindings(name, tail, rest)
}

#[cfg(test)]
mod tests {
    use adamas_parser::ast::{Decl, DeclKind};

    use super::mentions;

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

//! Унификация - единственное место, где решаются метапеременные.

use std::rc::Rc;

use adamas_core::source::Span;

use crate::error::Error;
use crate::types::{Level, MetaCtx, MetaId, Type};

/// Приводит два типа к равенству, решая метапеременные по дороге.
///
/// `expected` - то, чего требует контекст, `found` - то, что получилось.
/// Порядок влияет только на текст ошибки, не на результат.
pub(crate) fn unify(
    ctx: &mut MetaCtx,
    expected: &Rc<Type>,
    found: &Rc<Type>,
    span: Span,
) -> Result<(), Error> {
    let left = ctx.force(expected);
    let right = ctx.force(found);

    match (&*left, &*right) {
        (Type::Int, Type::Int) | (Type::Bool, Type::Bool) => Ok(()),
        (Type::Var(a), Type::Var(b)) if a == b => Ok(()),
        (Type::Meta(a), Type::Meta(b)) if a == b => Ok(()),

        (Type::Meta(id), _) => solve(ctx, *id, &right, span),
        (_, Type::Meta(id)) => solve(ctx, *id, &left, span),

        (Type::Fun(from_a, to_a), Type::Fun(from_b, to_b)) => {
            unify(ctx, from_a, from_b, span)?;
            unify(ctx, to_a, to_b, span)
        }

        _ => {
            let (expected, found) = ctx.render_pair(&left, &right);
            Err(Error::Mismatch {
                expected,
                found,
                span,
            })
        }
    }
}

/// Решает метапеременную типом, предварительно проверив два условия.
fn solve(ctx: &mut MetaCtx, id: MetaId, ty: &Rc<Type>, span: Span) -> Result<(), Error> {
    let level = ctx.level_of(id);
    scope_check(ctx, id, level, ty).map_err(|()| {
        // Общее пространство имён: иначе метапеременная в тексте ошибки не
        // совпадёт по имени со своим же вхождением в тип.
        let (meta, ty) = ctx.render_pair(&Rc::new(Type::Meta(id)), ty);
        Error::OccursCheck { meta, ty, span }
    })?;
    ctx.solve(id, Rc::clone(ty));
    Ok(())
}

/// Один обход, две задачи.
///
/// **Occurs check:** если `id` встречается внутри `ty`, решение породило бы
/// бесконечный тип (`?a = ?a -> b`). Классический источник - самоприменение
/// `\x -> x x`.
///
/// **Понижение уровней:** метапеременные внутри `ty`, созданные глубже, чем
/// `id`, теперь достижимы с уровня `id`. Не понизить им уровень - значит
/// разрешить обобщить их в ближайшем `let`, хотя они уже просочились наружу.
/// Это и есть источник классических дыр в наивных реализациях HM.
fn scope_check(ctx: &mut MetaCtx, id: MetaId, level: Level, ty: &Rc<Type>) -> Result<(), ()> {
    let forced = ctx.force(ty);
    match &*forced {
        Type::Meta(other) if *other == id => Err(()),
        Type::Meta(other) => {
            ctx.lower_level(*other, level);
            Ok(())
        }
        Type::Fun(from, to) => {
            scope_check(ctx, id, level, from)?;
            scope_check(ctx, id, level, to)
        }
        Type::Int | Type::Bool | Type::Var(_) => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use adamas_core::source::Span;

    use super::unify;
    use crate::types::{MetaCtx, Type};

    fn span() -> Span {
        Span::new(0, 1)
    }

    #[test]
    fn unification_is_symmetric_on_success() {
        for swapped in [false, true] {
            let mut ctx = MetaCtx::default();
            let meta = ctx.fresh(0);
            let concrete = Type::fun(Rc::new(Type::Int), Rc::new(Type::Bool));
            let (a, b) = if swapped {
                (Rc::clone(&concrete), Rc::clone(&meta))
            } else {
                (Rc::clone(&meta), Rc::clone(&concrete))
            };
            assert!(unify(&mut ctx, &a, &b, span()).is_ok());
            assert_eq!(ctx.generalize(0, &meta).body.to_string(), "Int -> Bool");
        }
    }

    #[test]
    fn unification_is_idempotent() {
        let mut ctx = MetaCtx::default();
        let meta = ctx.fresh(0);
        let int = Rc::new(Type::Int);
        assert!(unify(&mut ctx, &meta, &int, span()).is_ok());
        assert!(
            unify(&mut ctx, &meta, &int, span()).is_ok(),
            "повтор не должен ломаться"
        );
    }

    #[test]
    fn occurs_check_rejects_infinite_types() {
        let mut ctx = MetaCtx::default();
        let meta = ctx.fresh(0);
        let cyclic = Type::fun(Rc::clone(&meta), Rc::new(Type::Int));
        let error = unify(&mut ctx, &meta, &cyclic, span()).unwrap_err();
        assert!(error.to_string().contains("бесконечный тип"), "{error}");
    }

    #[test]
    fn solving_lowers_levels_of_escaping_metas() {
        let mut ctx = MetaCtx::default();
        let outer = ctx.fresh(0);
        let inner = ctx.fresh(5);
        assert!(unify(&mut ctx, &outer, &inner, span()).is_ok());

        // inner теперь достижима с уровня 0, значит обобщать её на уровне 0
        // нельзя - иначе получили бы полиморфизм там, где его нет.
        assert_eq!(ctx.generalize(0, &inner).arity, 0);
    }

    #[test]
    fn mismatch_names_both_sides() {
        let mut ctx = MetaCtx::default();
        let error = unify(&mut ctx, &Rc::new(Type::Int), &Rc::new(Type::Bool), span()).unwrap_err();
        let text = error.to_string();
        assert!(text.contains("Int") && text.contains("Bool"), "{text}");
    }
}

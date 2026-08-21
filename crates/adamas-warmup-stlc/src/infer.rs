//! Bidirectional-вывод типов. Два взаимно рекурсивных режима:
//!
//! - [`Ctx::infer`] - синтез: по терму вычислить его тип;
//! - [`Ctx::check`] - проверка: тип известен снаружи, сверить с ним терм.
//!
//! Переход между режимами один: если для формы нет правила проверки,
//! синтезируем тип и унифицируем с ожидаемым. Там же рождаются все ошибки
//! несовпадения.

use std::rc::Rc;

use crate::error::Error;
use crate::syntax::{BinOp, Kind, Term, TypeExpr};
use crate::types::{Level, MetaCtx, Scheme, Type};
use crate::unify::unify;

/// Выводит тип целой программы и обобщает его.
pub(crate) fn infer_program(term: &Term) -> Result<Type, Error> {
    let mut ctx = Ctx {
        metas: MetaCtx::default(),
        env: Vec::new(),
        level: 1,
    };
    let ty = ctx.infer(term)?;
    // Обобщение на уровне 0: всё, что осталось нерешённым, - параметрический
    // полиморфизм программы, и печатается буквами, а не `?0`.
    Ok((*ctx.metas.generalize(0, &ty).body).clone())
}

struct Ctx {
    metas: MetaCtx,
    /// Стек связываний. Поиск с конца - внутреннее связывание затеняет внешнее.
    env: Vec<(String, Scheme)>,
    /// Текущая глубина вложенности `let`; см. [`crate::types`].
    level: Level,
}

impl Ctx {
    fn lookup(&self, name: &str) -> Option<&Scheme> {
        self.env
            .iter()
            .rev()
            .find(|(bound, _)| bound == name)
            .map(|(_, scheme)| scheme)
    }

    /// Выполняет действие со связыванием `name : scheme` в области видимости.
    fn scoped<T>(&mut self, name: &str, scheme: Scheme, action: impl FnOnce(&mut Self) -> T) -> T {
        self.env.push((name.to_owned(), scheme));
        let result = action(self);
        self.env.pop();
        result
    }

    fn infer(&mut self, term: &Term) -> Result<Rc<Type>, Error> {
        match &term.kind {
            Kind::Int(_) => Ok(Rc::new(Type::Int)),
            Kind::Bool(_) => Ok(Rc::new(Type::Bool)),

            Kind::Var(name) => {
                let scheme = self
                    .lookup(name)
                    .cloned()
                    .ok_or_else(|| Error::UnboundVariable {
                        name: name.clone(),
                        span: term.span,
                    })?;
                Ok(self.metas.instantiate(&scheme, self.level))
            }

            Kind::Lambda {
                param,
                annotation,
                body,
            } => {
                let domain = annotation
                    .as_ref()
                    .map_or_else(|| self.metas.fresh(self.level), from_type_expr);
                let codomain = self.scoped(param, Scheme::mono(Rc::clone(&domain)), |ctx| {
                    ctx.infer(body)
                })?;
                Ok(Type::fun(domain, codomain))
            }

            Kind::App(callee, argument) => {
                let callee_ty = self.infer(callee)?;
                // Вместо разбора случаев "функция / метапеременная / прочее" -
                // одна унификация со свежей стрелкой. Метапеременная решится,
                // конкретная стрелка разложится, всё остальное даст ошибку с
                // осмысленным текстом.
                let domain = self.metas.fresh(self.level);
                let codomain = self.metas.fresh(self.level);
                let arrow = Type::fun(Rc::clone(&domain), Rc::clone(&codomain));
                unify(&mut self.metas, &arrow, &callee_ty, callee.span)?;
                self.check(argument, &domain)?;
                Ok(codomain)
            }

            Kind::Let {
                name,
                recursive,
                value,
                body,
            } => {
                let scheme = self.binding(name, *recursive, value)?;
                self.scoped(name, scheme, |ctx| ctx.infer(body))
            }

            Kind::If {
                cond,
                then,
                otherwise,
            } => {
                self.check(cond, &Rc::new(Type::Bool))?;
                let ty = self.infer(then)?;
                self.check(otherwise, &ty)?;
                Ok(ty)
            }

            // `fix : (a -> a) -> a`. Единственный источник незавершающихся
            // вычислений в языке.
            Kind::Fix(inner) => {
                let ty = self.metas.fresh(self.level);
                let endo = Type::fun(Rc::clone(&ty), Rc::clone(&ty));
                self.check(inner, &endo)?;
                Ok(ty)
            }

            Kind::Bin { op, left, right } => {
                let int = Rc::new(Type::Int);
                self.check(left, &int)?;
                self.check(right, &int)?;
                Ok(match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul => int,
                    BinOp::Less | BinOp::Equal => Rc::new(Type::Bool),
                })
            }

            Kind::Annot { term: inner, ty } => {
                let expected = from_type_expr(ty);
                self.check(inner, &expected)?;
                Ok(expected)
            }
        }
    }

    fn check(&mut self, term: &Term, expected: &Rc<Type>) -> Result<(), Error> {
        let expected = self.metas.force(expected);

        match (&term.kind, &*expected) {
            // Ради этого правила всё и затевалось: тип параметра берётся из
            // ожидаемого типа, метапеременная не нужна.
            (
                Kind::Lambda {
                    param,
                    annotation,
                    body,
                },
                Type::Fun(domain, codomain),
            ) => {
                if let Some(written) = annotation {
                    unify(&mut self.metas, domain, &from_type_expr(written), term.span)?;
                }
                self.scoped(param, Scheme::mono(Rc::clone(domain)), |ctx| {
                    ctx.check(body, codomain)
                })
            }

            // Ветки проверяются против ожидаемого типа напрямую. В режиме
            // синтеза тип брался бы из первой ветки, и ошибка во второй
            // указывала бы на неё, хотя виновата могла быть первая.
            (
                Kind::If {
                    cond,
                    then,
                    otherwise,
                },
                _,
            ) => {
                self.check(cond, &Rc::new(Type::Bool))?;
                self.check(then, &expected)?;
                self.check(otherwise, &expected)
            }

            (
                Kind::Let {
                    name,
                    recursive,
                    value,
                    body,
                },
                _,
            ) => {
                let scheme = self.binding(name, *recursive, value)?;
                self.scoped(name, scheme, |ctx| ctx.check(body, &expected))
            }

            _ => {
                let found = self.infer(term)?;
                unify(&mut self.metas, &expected, &found, term.span)
            }
        }
    }

    /// Типизирует правую часть `let` и обобщает результат.
    ///
    /// Обобщение безусловное: value restriction здесь не нужна, потому что в
    /// языке нет ни ссылок, ни любых других изменяемых ячеек, - а без них
    /// неограниченное обобщение остаётся корректным.
    fn binding(&mut self, name: &str, recursive: bool, value: &Term) -> Result<Scheme, Error> {
        self.level += 1;
        let result = if recursive {
            // Рекурсия мономорфна: внутри собственной правой части имя имеет
            // тип-метапеременную, а не схему. Полиморфная рекурсия в HM
            // неразрешима, и ML-семейство её тоже не выводит.
            let placeholder = self.metas.fresh(self.level);
            let checked = self.scoped(name, Scheme::mono(Rc::clone(&placeholder)), |ctx| {
                ctx.check(value, &placeholder)
            });
            checked.map(|()| placeholder)
        } else {
            self.infer(value)
        };
        // Уровень восстанавливается до разбора ошибки: иначе неудачная ветка
        // оставила бы счётчик смещённым, и следующее обобщение сработало бы
        // неверно.
        self.level -= 1;
        let ty = result?;
        Ok(self.metas.generalize(self.level, &ty))
    }
}

fn from_type_expr(ty: &TypeExpr) -> Rc<Type> {
    match ty {
        TypeExpr::Int => Rc::new(Type::Int),
        TypeExpr::Bool => Rc::new(Type::Bool),
        TypeExpr::Fun(from, to) => Type::fun(from_type_expr(from), from_type_expr(to)),
    }
}

#[cfg(test)]
mod tests {
    use adamas_core::source::SourceFile;

    fn type_of(text: &str) -> String {
        let file = SourceFile::new("test.stlc", text);
        crate::check(&file)
            .expect("программа должна типизироваться")
            .to_string()
    }

    fn error(text: &str) -> String {
        let file = SourceFile::new("test.stlc", text);
        crate::check(&file)
            .expect_err("программа не должна типизироваться")
            .to_string()
    }

    #[test]
    fn identity_is_polymorphic() {
        assert_eq!(type_of("\\x -> x"), "a -> a");
    }

    #[test]
    fn let_bound_identity_is_used_at_two_types() {
        // Без обобщения в let эта программа не типизируется: `id` пришлось бы
        // использовать в одном и том же типе дважды.
        assert_eq!(
            type_of("let id = \\x -> x in if id true then id 1 else 2"),
            "Int"
        );
    }

    #[test]
    fn lambda_bound_identity_is_not_generalized() {
        // Зеркало предыдущего теста: параметр лямбды мономорфен, и то же
        // самое использование обязано провалиться.
        assert!(error("\\id -> if id true then id 1 else 2").contains("несовпадение"));
    }

    #[test]
    fn annotation_drives_checking() {
        assert_eq!(type_of("(\\x -> x + 1 : Int -> Int)"), "Int -> Int");
    }

    #[test]
    fn annotated_parameter_is_respected() {
        assert_eq!(type_of("\\(x : Bool) -> if x then 1 else 0"), "Bool -> Int");
    }

    #[test]
    fn self_application_hits_occurs_check() {
        assert!(error("\\x -> x x").contains("бесконечный тип"));
    }

    #[test]
    fn branches_must_agree() {
        assert!(error("if true then 1 else false").contains("несовпадение"));
    }

    #[test]
    fn recursion_is_monomorphic_but_generalized_afterwards() {
        assert_eq!(type_of("let rec f = \\x -> f x in f"), "a -> b");
    }

    #[test]
    fn unbound_variable_is_reported_by_name() {
        assert!(error("\\x -> y").contains('y'));
    }

    #[test]
    fn escaping_meta_is_not_generalized() {
        // `f` монотипна, поэтому `let g = f` не может стать полиморфной.
        assert_eq!(type_of("\\f -> let g = f in g 1"), "(Int -> a) -> a");
    }
}

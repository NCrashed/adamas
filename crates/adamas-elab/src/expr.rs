//! Выражения и паттерны поверхностного языка в термы ядра.
//!
//! # Элаборация не типонаправленная
//!
//! Она собирает терм по синтаксису и отдаёт его `check` (§9 Фаза 1: элаборация
//! не входит в TCB). Отсюда прямое следствие, видное по [`Missing`]: всё, что
//! требует знать ожидаемый тип, - `if`, `case` выражением, `let` без
//! аннотации, дырка `_` - пока не элаборируется. Это не список недоделок, а
//! граница выбранной архитектуры, и каждая форма названа вместе с тем, чего ей
//! недостаёт.
//!
//! # Регистр решает, что связывает
//!
//! Имя с заглавной буквы разбирает, строчное связывает (§4.1, решение
//! 2026-08-25). Правило локально: чтобы прочитать клаузу, не нужно знать, что
//! объявлено выше. Буква без регистра считается строчной, как в GHC.

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern as CorePattern};
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::term::{Name as CoreName, Term};
use adamas_parser::ast::{
    self, Binding, Block, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind,
    Symbol, Visibility,
};

use crate::error::{ElabError, Missing};

/// Разбирает ли имя (заглавное) или связывает (строчное).
///
/// Письменности без регистра попадают в «строчные»: конструкторов ими не
/// назвать, и это названная цена решения от 2026-08-25.
#[must_use]
pub fn is_reference(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

/// Состояние элаборации: сигнатура, хранилище дырок и локальные связывания.
pub(crate) struct Elaborator<'a> {
    /// Уже объявленное. Элаборация её не меняет - объявляет вызывающий.
    pub signature: &'a Signature,
    /// Хранилище дырок уровня: одно на прогон (§10 вопрос 51).
    pub metas: &'a mut Metas,
    /// Локальные связывания снаружи внутрь; индекс де Брёйна - расстояние от
    /// конца.
    scope: Vec<Symbol>,
    /// Члены объявляемой группы вместе с арностью параметров уровня.
    ///
    /// В сигнатуре их ещё нет - она увидит группу целиком (§10 вопрос 50), - а
    /// ссылаться на них надо: конструктор называет своё семейство, тело
    /// называет само определение. Спросить арность у сигнатуры поэтому нечего,
    /// и её считает вызывающий обобщением по типу члена; это и есть §10
    /// вопрос 63.
    group: Vec<(Symbol, Rc<[Level]>)>,
    /// Аргументы уровня, уже выданные имени в этом объявлении.
    ///
    /// Одно имя - один набор дырок, а не свежий на каждое вхождение. Иначе
    /// `f : D -> D` над полиморфным по уровню `D` читается как `∀u v. D{u} ->
    /// D{v}`: обобщение идёт до проверки тела, связать два параметра потом
    /// нечем, и тождество над таким семейством не пишется. Тот же довод уже
    /// стоял за общими дырками у члена группы (`self_levels` в
    /// [`crate::decl`]), здесь он распространён на объявленное.
    ///
    /// Цена названа: два вхождения одного имени на разных уровнях в одной
    /// сигнатуре теперь несовместимы. Написать их всё равно нечем - уровни в
    /// поверхностном языке не именуются, - и появится это вместе с
    /// имплиситами (§4.1).
    instantiated: HashMap<Symbol, Term>,
}

impl<'a> Elaborator<'a> {
    /// Элаборатор с пустым локальным контекстом.
    pub(crate) fn new(signature: &'a Signature, metas: &'a mut Metas) -> Self {
        Self::with_group(signature, metas, Vec::new())
    }

    /// То же, но с членами объявляемой группы.
    pub(crate) fn with_group(
        signature: &'a Signature,
        metas: &'a mut Metas,
        group: Vec<(Symbol, Rc<[Level]>)>,
    ) -> Self {
        Self {
            signature,
            metas,
            scope: Vec::new(),
            group,
            instantiated: HashMap::new(),
        }
    }

    /// Выполняет `body` под связыванием `name`.
    fn under<T>(&mut self, name: &Symbol, body: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push(Rc::clone(name));
        let outcome = body(self);
        self.scope.pop();
        outcome
    }

    /// Индекс де Брёйна локального связывания.
    fn local(&self, name: &str) -> Option<u32> {
        self.scope
            .iter()
            .rposition(|bound| &**bound == name)
            .and_then(|position| u32::try_from(self.scope.len() - 1 - position).ok())
    }

    /// Кратность связывания: написанная либо умолчание позиции (§4.1).
    fn multiplicity(written: Option<ast::MultAnn>, default: Mult) -> Mult {
        written.map_or(default, |ann| match ann.mult {
            ast::Mult::Zero => Mult::Zero,
            ast::Mult::One => Mult::One,
            ast::Mult::Many => Mult::Many,
        })
    }

    /// Выражение в терм.
    ///
    /// `default` - кратность связываний, у которых она не написана: `ω` у
    /// параметра функции, `1` у поля конструктора (§4.1). Умолчание
    /// **позиционное**: оно расходуется на связывание, к которому пришло, и
    /// доходит только до кодомена - там стоит следующий параметр той же
    /// сигнатуры. В домен и в любой другой подтерм элаборация уходит с `ω`:
    /// `(Nat -> Nat) -> C` берёт поле типа «функция», а не поле с кратностью
    /// поля.
    pub(crate) fn expr(&mut self, expr: &Expr, default: Mult) -> Result<Term, ElabError> {
        let missing = |what| {
            Err(ElabError::Missing {
                what,
                span: expr.span,
            })
        };
        match &expr.kind {
            ExprKind::Name(name) => self.name(name),
            ExprKind::App(callee, argument) => Ok(Term::App(
                Rc::new(self.expr(callee, Mult::Many)?),
                Rc::new(self.expr(argument, Mult::Many)?),
            )),
            ExprKind::Arrow(domain, codomain) => {
                let domain = self.expr(domain, Mult::Many)?;
                let anonymous: Symbol = Rc::from("_");
                let codomain = self.under(&anonymous, |inner| inner.expr(codomain, default))?;
                Ok(Term::Pi(
                    default,
                    CoreName::from("_"),
                    Rc::new(domain),
                    Rc::new(codomain),
                ))
            }
            ExprKind::Pi { binders, codomain } => self.pi(binders, codomain, default),
            ExprKind::Lam { params, body } => self.lam(params, body),
            ExprKind::Block(block) => self.block(block),
            ExprKind::Chain(chain) => self.chain(chain),

            ExprKind::Hole => missing(Missing::TermHole),
            ExprKind::Lit(_) => missing(Missing::Literal),
            ExprKind::TypeApp(..) => missing(Missing::TypeApplication),
            ExprKind::If { .. } => missing(Missing::Conditional),
            ExprKind::Case { .. } => missing(Missing::CaseExpression),
            ExprKind::Tuple(_) => missing(Missing::Tuple),
            ExprKind::List(_) => missing(Missing::List),
        }
    }

    /// Имя: связывание, `Type` или ссылка на объявленное.
    fn name(&mut self, name: &ast::Name) -> Result<Term, ElabError> {
        if let Some(index) = self.local(&name.text) {
            return Ok(Term::var(index));
        }
        // `Type` заслоняется локальным связыванием, но не определением: имя
        // занято языком, и переопределить его нечем.
        if &*name.text == "Type" {
            return Ok(Term::Universe(self.metas.fresh_level()));
        }
        // Член объявляемой группы: аргументы уровня - дырки, числом в арность,
        // посчитанную вызывающим.
        if let Some((_, levels)) = self.group.iter().find(|(member, _)| **member == *name.text) {
            return Ok(Term::Const(CoreName::from(&*name.text), Rc::clone(levels)));
        }
        // Аргументы уровня подставляются дырками - это implicit UP со стороны
        // места использования (§3.2), - и одному имени они выдаются один раз
        // на объявление (см. `instantiated`).
        if let Some(term) = self.instantiated.get(&name.text) {
            return Ok(term.clone());
        }
        let term = self
            .signature
            .instantiate(&name.text, self.metas)
            .ok_or_else(|| ElabError::UnknownName {
                name: Rc::clone(&name.text),
                span: name.span,
            })?;
        self.instantiated
            .insert(Rc::clone(&name.text), term.clone());
        Ok(term)
    }

    /// `(q x y : A) (r z : B) -> C`.
    ///
    /// Группы разворачиваются в плоский список связываний: `(x y : A)` - это
    /// два `Pi`, и второй видит первое связывание, поэтому тип элаборируется
    /// заново под каждым именем. Дырки уровня при этом у каждого свои: общий
    /// `Type` в записи не значит общий универсум, а более общее прочтение
    /// здесь безопасно.
    fn pi(
        &mut self,
        binders: &[ast::Binder],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let mut flat: Vec<(Mult, Symbol, &Expr)> = Vec::new();
        for binder in binders {
            if binder.visibility == Visibility::Implicit {
                return Err(ElabError::Missing {
                    what: Missing::ImplicitBinder,
                    span: binder.span,
                });
            }
            // Связывание без типа бывает только параметром семейства, и туда
            // этот путь не ведёт.
            let Some(ty) = &binder.ty else {
                return Err(ElabError::Missing {
                    what: Missing::Implicits,
                    span: binder.span,
                });
            };
            let mult = Self::multiplicity(binder.mult, default);
            for name in &binder.names {
                flat.push((mult, Rc::clone(&name.text), ty));
            }
        }
        self.pi_flat(&flat, codomain, default)
    }

    fn pi_flat(
        &mut self,
        binders: &[(Mult, Symbol, &Expr)],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let Some(((mult, name, ty), rest)) = binders.split_first() else {
            return self.expr(codomain, default);
        };
        let domain = self.expr(ty, Mult::Many)?;
        let body = self.under(name, |inner| inner.pi_flat(rest, codomain, default))?;
        Ok(Term::Pi(
            *mult,
            CoreName::from(&**name),
            Rc::new(domain),
            Rc::new(body),
        ))
    }

    /// `\x y -> body`.
    fn lam(&mut self, params: &[ast::LamParam], body: &Expr) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            return self.expr(body, Mult::Many);
        };
        let name = match &param.kind {
            LamParamKind::Binder(_) => {
                return Err(ElabError::Missing {
                    what: Missing::LambdaAnnotation,
                    span: param.span,
                });
            }
            LamParamKind::Pattern(pattern) => match &pattern.kind {
                PatternKind::Name(name) if !is_reference(&name.text) => Rc::clone(&name.text),
                PatternKind::Wildcard => Rc::from("_"),
                PatternKind::Tuple(items) if items.is_empty() => {
                    return Err(ElabError::Missing {
                        what: Missing::Tuple,
                        span: pattern.span,
                    });
                }
                _ => {
                    // Разбор в параметре лямбды - это `case` без мотива.
                    return Err(ElabError::Missing {
                        what: Missing::CaseExpression,
                        span: pattern.span,
                    });
                }
            },
        };
        let inner = self.under(&name, |inner| inner.lam(rest, body))?;
        Ok(Term::Lam(
            Mult::Many,
            CoreName::from(&*name),
            Rc::new(inner),
        ))
    }

    /// Блок операторов: цепочка `let` и значение последним.
    fn block(&mut self, block: &Block) -> Result<Term, ElabError> {
        self.statements(&block.stmts)
    }

    fn statements(&mut self, stmts: &[Stmt]) -> Result<Term, ElabError> {
        let Some((first, rest)) = stmts.split_first() else {
            // Пустых блоков layout не делает.
            unreachable!("блок без операторов")
        };
        match &first.kind {
            StmtKind::Expr(expr) if rest.is_empty() => self.expr(expr, Mult::Many),
            StmtKind::Expr(_) => Err(ElabError::Missing {
                what: Missing::Sequencing,
                span: first.span,
            }),
            StmtKind::Let(bindings) => {
                if rest.is_empty() {
                    return Err(ElabError::Missing {
                        what: Missing::Sequencing,
                        span: first.span,
                    });
                }
                self.bindings(bindings, rest)
            }
        }
    }

    /// `let` со своими связываниями: каждое даёт узел `Let`, вложенный в
    /// следующее.
    fn bindings(&mut self, bindings: &[Binding], rest: &[Stmt]) -> Result<Term, ElabError> {
        let Some((binding, tail)) = bindings.split_first() else {
            return self.statements(rest);
        };
        if !binding.params.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: binding.span,
            });
        }
        let Some(ty) = &binding.ty else {
            return Err(ElabError::Missing {
                what: Missing::UntypedLet,
                span: binding.span,
            });
        };
        let ty = self.expr(ty, Mult::Many)?;
        let value = self.expr(&binding.body, Mult::Many)?;
        let mult = Self::multiplicity(binding.mult, Mult::Many);
        let body = self.under(&binding.name.text, |inner| inner.bindings(tail, rest))?;
        Ok(Term::Let(
            mult,
            CoreName::from(&*binding.name.text),
            Rc::new(ty),
            Rc::new(value),
            Rc::new(body),
        ))
    }

    /// Цепочка операторов. Скобки расставляются по фикситетам, а их ещё нет,
    /// поэтому цепочка длиннее одного оператора - отказ.
    fn chain(&mut self, chain: &ast::Chain) -> Result<Term, ElabError> {
        let [(operator, operand)] = &chain.tail[..] else {
            return Err(ElabError::Missing {
                what: Missing::Fixities,
                span: chain.head.span,
            });
        };
        let callee = self.name(operator)?;
        let left = self.expr(&chain.head, Mult::Many)?;
        let right = self.expr(operand, Mult::Many)?;
        Ok(callee.apply([left, right]))
    }

    // --- паттерны ---------------------------------------------------------

    /// Паттерн клаузы или ветки.
    pub(crate) fn pattern(&self, pattern: &Pattern) -> Result<CorePattern, ElabError> {
        match &pattern.kind {
            PatternKind::Wildcard => Ok(CorePattern::Var(CoreName::from("_"))),
            PatternKind::Name(name) => {
                if is_reference(&name.text) {
                    self.constructor(name, Vec::new())
                } else {
                    Ok(CorePattern::Var(CoreName::from(&*name.text)))
                }
            }
            PatternKind::App { head, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<Vec<_>, _>>()?;
                self.constructor(head, fields)
            }
            PatternKind::Lit(_) => Err(ElabError::Missing {
                what: Missing::Literal,
                span: pattern.span,
            }),
            PatternKind::Tuple(_) => Err(ElabError::Missing {
                what: Missing::Tuple,
                span: pattern.span,
            }),
        }
    }

    /// Имя конструктора: обязано быть объявленным конструктором.
    fn constructor(
        &self,
        name: &ast::Name,
        fields: Vec<CorePattern>,
    ) -> Result<CorePattern, ElabError> {
        let known = self.signature.lookup(&name.text).is_some_and(|definition| {
            matches!(definition.kind, DefinitionKind::Constructor { .. })
        });
        if known {
            Ok(CorePattern::Constructor(
                CoreName::from(&*name.text),
                fields,
            ))
        } else {
            Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            })
        }
    }

    /// Клауза: паттерны, затем тело в контексте их переменных.
    ///
    /// Порядок переменных - слева направо в глубину: этого ждёт
    /// [`adamas_core::pattern::compile`], и другого тело видеть не может.
    pub(crate) fn clause(&mut self, clause: &ast::Clause) -> Result<Clause, ElabError> {
        if !clause.wheres.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: clause.span,
            });
        }
        let patterns = clause
            .patterns
            .iter()
            .map(|pattern| self.pattern(pattern))
            .collect::<Result<Vec<_>, _>>()?;

        let mut bound = Vec::new();
        for pattern in &patterns {
            collect(pattern, &mut bound);
        }
        let depth = self.scope.len();
        self.scope.extend(bound);
        let body = self.expr(&clause.body, Mult::Many);
        self.scope.truncate(depth);

        Ok(Clause {
            patterns,
            body: body?,
        })
    }
}

/// Переменные паттерна слева направо в глубину.
fn collect(pattern: &CorePattern, bound: &mut Vec<Symbol>) {
    match pattern {
        CorePattern::Var(name) => bound.push(Rc::from(&**name)),
        CorePattern::Constructor(_, fields) => {
            for field in fields {
                collect(field, bound);
            }
        }
    }
}

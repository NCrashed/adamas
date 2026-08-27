//! Выражения и паттерны поверхностного языка в термы ядра.
//!
//! Границы фрагмента и причина каждой - в [`crate`] и в [`Missing`]; правило
//! регистра - у [`is_reference`]. Здесь - сами правила элаборации, по одному
//! на форму, и то, что из них следует: тому же порядку следует обратный проход
//! маршрута ([`crate::route`]).

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern as CorePattern};
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Name as CoreName, Term};
use adamas_parser::ast::{
    self, Binding, Block, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind,
    Symbol, Visibility,
};

use crate::error::{ElabError, Missing};
use crate::own::Owned;

/// Разбирает ли имя (заглавное) или связывает (строчное).
///
/// §4.1: заглавное имя ссылается на объявленное - в паттерне разбирает, в типе
/// обязано быть известным; строчное связывает. Правило локально, поэтому чтобы
/// прочитать клаузу, не нужно знать, что объявлено выше, и опечатка в имени
/// конструктора называется там, где написана, вместо переменной, ловящей всё.
///
/// Письменности без регистра попадают в «строчные»: конструкторов ими не
/// назвать, и это названная цена решения от 2026-08-25.
#[must_use]
pub fn is_reference(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

/// Локальное связывание: имя и видно ли оно поиску (см. `hiding`).
struct Bound {
    name: Symbol,
    visible: bool,
}

impl Bound {
    fn visible(name: &Symbol) -> Self {
        Self {
            name: Rc::clone(name),
            visible: true,
        }
    }
}

/// Состояние элаборации: сигнатура, хранилище дырок и локальные связывания.
pub(crate) struct Elaborator<'a> {
    /// Уже объявленное. Элаборация её не меняет - объявляет вызывающий.
    pub signature: &'a Signature,
    /// Хранилище дырок уровня: одно на прогон (§10 вопрос 51).
    pub metas: &'a mut Metas,
    /// Типы, объявленные `unique` или `resource` (§3.3). Как и хранилище
    /// дырок, приходит снаружи: прогон элаборации - модуль целиком.
    pub owned: &'a Owned,
    /// Локальные связывания снаружи внутрь; индекс де Брёйна - расстояние от
    /// конца.
    scope: Vec<Bound>,
    /// Члены объявляемой группы вместе с арностью параметров уровня.
    ///
    /// В сигнатуре их ещё нет - она увидит группу целиком (§10 вопрос 50), - а
    /// ссылаться на них надо: конструктор называет своё семейство, тело
    /// называет само определение. Спросить арность у сигнатуры поэтому нечего,
    /// и её считает вызывающий обобщением по типу члена; это и есть §10
    /// вопрос 63.
    group: Vec<(Symbol, Rc<[Level]>)>,
    /// Кратности связываний написанного типа - по одной на `Pi` его спайна.
    ///
    /// Лямбда в ядре несёт кратность, и `check` требует, чтобы она совпадала с
    /// кратностью `Pi`. Вывести её элаборация не может - она не
    /// типонаправленная, - но здесь и выводить нечего: тип **написан**, и
    /// спайн его виден синтаксически. Дальше видимого спайна (кодомен -
    /// константа, разворачивающаяся в `Pi`) кратности кончаются, и лямбда
    /// снова берёт `ω`.
    declared: Vec<Mult>,
    /// Кратности, ожидающие ближайшую лямбду. Их выставляет тот, кто знает
    /// написанный тип: клауза - остатком спайна после своих паттернов, `let` -
    /// спайном своей аннотации.
    expected: Vec<Mult>,
    /// Идёт ли элаборация в позиции типа - см. `typing`.
    types: bool,
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
    pub(crate) fn new(signature: &'a Signature, metas: &'a mut Metas, owned: &'a Owned) -> Self {
        Self::with_group(signature, metas, owned, Vec::new())
    }

    /// То же, но с членами объявляемой группы.
    pub(crate) fn with_group(
        signature: &'a Signature,
        metas: &'a mut Metas,
        owned: &'a Owned,
        group: Vec<(Symbol, Rc<[Level]>)>,
    ) -> Self {
        Self {
            signature,
            metas,
            owned,
            scope: Vec::new(),
            group,
            declared: Vec::new(),
            expected: Vec::new(),
            types: false,
            instantiated: HashMap::new(),
        }
    }

    /// Кратности написанного типа - те, что достанутся лямбдам тела.
    pub(crate) fn declaring(mut self, ty: &Term) -> Self {
        self.declared = pi_mults(ty);
        self
    }

    /// Выполняет `body` в позиции типа.
    ///
    /// Несвязанное строчное имя означает здесь не опечатку, а свободную
    /// переменную, которую §4.1 поднимает в implicit-параметр, - и отвечать
    /// на неё «имя не найдено» значит отправить искать опечатку там, где её
    /// нет.
    pub(crate) fn typing<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.types, true);
        let outcome = body(self);
        self.types = outer;
        outcome
    }

    /// Выполняет `body` под связыванием `name`.
    fn under<T>(&mut self, name: &Symbol, body: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push(Bound::visible(name));
        let outcome = body(self);
        self.scope.pop();
        outcome
    }

    /// Выполняет `body`, спрятав `count` последних связываний.
    ///
    /// Спрятанное связывание место в контексте занимает, а имени не имеет:
    /// индексы де Брёйна остаются верными, а поиск по имени сквозь него
    /// проходит наружу. Нужно это ровно группе `(x y : A)`, где `A` написано
    /// раньше обоих имён и видеть их не может.
    fn hiding<T>(&mut self, count: usize, body: impl FnOnce(&mut Self) -> T) -> T {
        let from = self.scope.len() - count;
        for bound in &mut self.scope[from..] {
            bound.visible = false;
        }
        let outcome = body(self);
        for bound in &mut self.scope[from..] {
            bound.visible = true;
        }
        outcome
    }

    /// Индекс де Брёйна локального связывания.
    fn local(&self, name: &str) -> Option<u32> {
        self.scope
            .iter()
            .rposition(|bound| bound.visible && &*bound.name == name)
            .and_then(|position| u32::try_from(self.scope.len() - 1 - position).ok())
    }

    /// Имя, которое связывает, обязано быть строчным (§4.1).
    ///
    /// Заглавное ссылается на объявленное, и связывать им значило бы заслонить
    /// то, на что оно ссылается: `let Zero : Nat = …` делал конструктор
    /// недостижимым до конца блока.
    fn binds(name: &ast::Name) -> Result<(), ElabError> {
        if is_reference(&name.text) {
            return Err(ElabError::UppercaseBinding {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        }
        Ok(())
    }

    /// Кратность связывания: написанная либо умолчание позиции (§4.1).
    fn multiplicity(written: Option<ast::MultAnn>, default: Mult) -> Mult {
        written.map_or(default, |ann| match ann.mult {
            ast::Mult::Zero => Mult::Zero,
            ast::Mult::One => Mult::One,
            ast::Mult::Many => Mult::Many,
        })
    }

    /// То же, с поправкой на владение (§3.3).
    ///
    /// Связывание unique- или resource-типа получает `1`, если не объявлено
    /// `0`: стёртые упоминания в доказательствах законны, а вот явное `ω` -
    /// ошибка **на самом связывании**. Так закрывается дыра ω→1: значений
    /// такого типа при кратности `ω` не существует, потому что не существует
    /// связывания, которое их удержало бы.
    fn binder_mult(
        &self,
        written: Option<ast::MultAnn>,
        ty: &Expr,
        default: Mult,
        span: Span,
    ) -> Result<Mult, ElabError> {
        let Some(owned) = self.owned.of(ty) else {
            return Ok(Self::multiplicity(written, default));
        };
        match written.map(|ann| ann.mult) {
            None | Some(ast::Mult::One) => Ok(Mult::One),
            Some(ast::Mult::Zero) => Ok(Mult::Zero),
            Some(ast::Mult::Many) => Err(ElabError::UnrestrictedOwned {
                owned,
                span: written.map_or(span, |ann| ann.span),
            }),
        }
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
        // Кратности ждут ближайшую лямбду и только её: подтерм, до которого
        // спустились иначе, написанным типом не накрыт.
        let expected = std::mem::take(&mut self.expected);
        match &expr.kind {
            ExprKind::Name(name) => self.name(name),
            // Спайн собирается циклом. Рекурсия по `callee` уходила на глубину
            // числа аргументов, а его ограничивает только длина файла: предел
            // вложенности парсера на плоское `f a b c …` не тратится, и тысячи
            // аргументов роняли процесс вместо отказа (§10 вопрос 62).
            ExprKind::App(..) => {
                let mut arguments = Vec::new();
                let mut head = expr;
                while let ExprKind::App(callee, argument) = &head.kind {
                    arguments.push(&**argument);
                    head = callee;
                }
                let mut term = self.expr(head, Mult::Many)?;
                for argument in arguments.into_iter().rev() {
                    term = Term::App(Rc::new(term), Rc::new(self.expr(argument, Mult::Many)?));
                }
                Ok(term)
            }
            ExprKind::Arrow(domain, codomain) => {
                // Стрелка связывает так же, как `(x : A) ->`, только без
                // имени, поэтому правило владения (§3.3) действует и здесь:
                // `drop : File -> Unit` даёт `(1 _ : File) -> Unit`, и писать
                // кратность руками не нужно.
                let mult = self.binder_mult(None, domain, default, expr.span)?;
                let domain = self.expr(domain, Mult::Many)?;
                let anonymous: Symbol = Rc::from("_");
                let codomain = self.under(&anonymous, |inner| inner.expr(codomain, default))?;
                Ok(Term::Pi(
                    mult,
                    CoreName::from("_"),
                    Rc::new(domain),
                    Rc::new(codomain),
                ))
            }
            ExprKind::Pi { binders, codomain } => self.pi(binders, codomain, default),
            ExprKind::Lam { params, body } => self.lam(params, body, &expected),
            ExprKind::Block(block) => self.block(block),
            ExprKind::Chain(chain) => self.chain(chain, expr.span),

            ExprKind::Hole => missing(Missing::TermHole),
            ExprKind::Lit(_) => missing(Missing::Literal),
            ExprKind::TypeApp(..) => missing(Missing::TypeApplication),
            ExprKind::If { .. } => missing(Missing::Conditional),
            ExprKind::Case { .. } => missing(Missing::CaseExpression),
            ExprKind::Tuple(items) if items.is_empty() => missing(Missing::Unit),
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
            .ok_or_else(|| {
                if self.types && !is_reference(&name.text) {
                    return ElabError::Missing {
                        what: Missing::Implicits,
                        span: name.span,
                    };
                }
                ElabError::UnknownName {
                    name: Rc::clone(&name.text),
                    span: name.span,
                }
            })?;
        self.instantiated
            .insert(Rc::clone(&name.text), term.clone());
        Ok(term)
    }

    /// `(q x y : A) (r z : B) -> C`.
    ///
    /// Группы разворачиваются в плоский список связываний: `(x y : A)` - это
    /// два `Pi`, и второй видит первое связывание, поэтому тип элаборируется
    /// заново под каждым именем. Заново - но не в другой области видимости:
    /// `A` написано раньше обоих имён, и собственные имена группы для него
    /// спрятаны (`hiding`), иначе `(0 t : Type) -> (0 t x : t) -> …` дало бы
    /// `x` тип соседа по группе вместо написанного снаружи. Отсюда третье
    /// поле плоского списка - сколько имён группы стоит перед этим.
    ///
    /// Дырки уровня у каждого имени свои: общий `Type` в записи не значит
    /// общий универсум, а более общее прочтение здесь безопасно.
    fn pi(
        &mut self,
        binders: &[ast::Binder],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let mut flat: Vec<(Mult, Symbol, &Expr, usize)> = Vec::new();
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
            let mult = self.binder_mult(binder.mult, ty, default, binder.span)?;
            for (position, name) in binder.names.iter().enumerate() {
                Self::binds(name)?;
                flat.push((mult, Rc::clone(&name.text), ty, position));
            }
        }
        self.pi_flat(&flat, codomain, default)
    }

    fn pi_flat(
        &mut self,
        binders: &[(Mult, Symbol, &Expr, usize)],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let Some(((mult, name, ty, siblings), rest)) = binders.split_first() else {
            return self.expr(codomain, default);
        };
        let domain = self.hiding(*siblings, |inner| inner.expr(ty, Mult::Many))?;
        let body = self.under(name, |inner| inner.pi_flat(rest, codomain, default))?;
        Ok(Term::Pi(
            *mult,
            CoreName::from(&**name),
            Rc::new(domain),
            Rc::new(body),
        ))
    }

    /// `\x y -> body`.
    ///
    /// `expected` - кратности написанного типа, по одной на параметр. Кончились
    /// (тип не написан, кодомен не виден насквозь) - берётся `ω`, и лямбда под
    /// не-`ω` связыванием остаётся невыразимой.
    fn lam(
        &mut self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Mult],
    ) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            // Остаток спайна достаётся телу: `\x -> \y -> e` - две лямбды под
            // теми же `Pi`, что и `\x y -> e`.
            self.expected = expected.to_vec();
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
                        what: Missing::Unit,
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
        let (mult, deeper) = expected
            .split_first()
            .map_or((Mult::Many, expected), |(mult, rest)| (*mult, rest));
        let inner = self.under(&name, |inner| inner.lam(rest, body, deeper))?;
        Ok(Term::Lam(mult, CoreName::from(&*name), Rc::new(inner)))
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
            // Блок кончается связыванием: значения у него нет, и дело не в
            // недостающем механизме - написана неполная форма.
            StmtKind::Let(_) if rest.is_empty() => {
                Err(ElabError::BlockWithoutValue { span: first.span })
            }
            StmtKind::Let(bindings) => self.bindings(bindings, rest),
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
        Self::binds(&binding.name)?;
        let mult = self.binder_mult(binding.mult, ty, Mult::Many, binding.span)?;
        let ty = self.typing(|inner| inner.expr(ty, Mult::Many))?;
        // Аннотация `let` - тот же написанный тип, и лямбда значения берёт
        // кратности у него.
        self.expected = pi_mults(&ty);
        let value = self.expr(&binding.body, Mult::Many)?;
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
    fn chain(&mut self, chain: &ast::Chain, span: Span) -> Result<Term, ElabError> {
        let [(operator, operand)] = &chain.tail[..] else {
            // Спан - цепочка целиком: отказ про то, как расставить в ней
            // скобки, а не про первый операнд, к операторам отношения не
            // имеющий.
            return Err(ElabError::Missing {
                what: Missing::Fixities,
                span,
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
            PatternKind::Tuple(items) => Err(ElabError::Missing {
                what: if items.is_empty() {
                    Missing::Unit
                } else {
                    Missing::Tuple
                },
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
        let mut seen: Vec<&ast::Name> = Vec::new();
        for pattern in &clause.patterns {
            repeated(pattern, &mut seen)?;
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
        self.scope.extend(bound.iter().map(Bound::visible));
        // Паттерны сняли первые связывания написанного типа; остаток спайна -
        // тем лямбдам, которыми клауза продолжается.
        self.expected = self
            .declared
            .split_at(patterns.len().min(self.declared.len()))
            .1
            .to_vec();
        let body = self.expr(&clause.body, Mult::Many);
        self.scope.truncate(depth);

        Ok(Clause {
            patterns,
            body: body?,
        })
    }
}

/// Кратности связываний по спайну `Pi` - столько, сколько видно синтаксически.
fn pi_mults(ty: &Term) -> Vec<Mult> {
    let mut mults = Vec::new();
    let mut current = ty;
    while let Term::Pi(mult, _, _, codomain) = current {
        mults.push(*mult);
        current = codomain;
    }
    mults
}

/// Повторное имя переменной в клаузе.
///
/// Клауза `f x x = x` терму отвечает корректному - побеждает правое вхождение,
/// потому что индекс ищется от ближайшего связывания, - и ядро её принимает.
/// Значит поймать опечатку может только элаборация: написанное равенство
/// аргументов языком не выражается, и разбор по нему сравнением не становится.
fn repeated<'a>(pattern: &'a Pattern, seen: &mut Vec<&'a ast::Name>) -> Result<(), ElabError> {
    match &pattern.kind {
        PatternKind::Name(name) if !is_reference(&name.text) => {
            if let Some(first) = seen.iter().find(|earlier| earlier.text == name.text) {
                return Err(ElabError::RepeatedBinding {
                    name: Rc::clone(&name.text),
                    span: name.span,
                    first: first.span,
                });
            }
            seen.push(name);
        }
        PatternKind::App { fields, .. } => {
            for field in fields {
                repeated(field, seen)?;
            }
        }
        _ => {}
    }
    Ok(())
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

//! Понижение термов ядра в [`ir`](crate::ir).
//!
//! Берётся **чистый фрагмент**: семейства и конструкторы, функции и применение,
//! разбор, рекурсия, `let`. Эффектов, хендлеров и резумпций здесь нет - им
//! отвечает вторая форма понижения (§13, 2026-09-08), а она приходит отдельно.
//! Всё, что во фрагмент не входит, отвергается названной причиной: молча
//! посчитать не то хуже, чем не посчитать.
//!
//! # Что здесь повторено за машиной, а не придумано заново
//!
//! **Стирание аргумента.** Машина стирает аргумент, когда вызываемое -
//! глобальное имя, а связывание его **типа** на этой позиции нулевое
//! (`adamas-interp/src/machine.rs`, `erases`). Кратность самой лямбды признаком
//! не служит: решение дырки терма есть цепочка лямбд при `0`, и значения в них
//! настоящие. Здесь ровно то же правило и ровно по тому же источнику - тип из
//! сигнатуры.
//!
//! **Поля ветви.** Ветвь получает связывания конструктора после параметров
//! семейства - столько же и в том же порядке, включая стёртые.
//!
//! # Чего понижение не делает
//!
//! Не бета-редуцирует, не инлайнит, не кеширует значение определения без
//! параметров: оптимизаций на этом срезе нет вовсе, и предсказуемость выхода
//! дороже его длины.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use adamas_core::mult::Mult;
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::term::{Case, Index, Name, Term};

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Expr, Fact, Form, FuncId, Function, LocalId, Program,
};

/// Почему понижение отказало.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    /// Имя, которого нет в сигнатуре.
    #[error("имя `{name}` не объявлено")]
    Unknown {
        /// Оно самое.
        name: String,
    },

    /// Постулат: тип есть, тела нет, понижать нечего.
    #[error("`{name}` - постулат: тела нет, и понижать нечего")]
    Postulate {
        /// Имя постулата.
        name: String,
    },

    /// Метка, операция либо элиминатор хендлера.
    #[error("`{name}` - эффект: вторая форма понижения этим срезом не берётся")]
    Effectful {
        /// Имя метки или операции.
        name: String,
    },

    /// Семейство в позиции значения.
    #[error("`{name}` - семейство типов: значения у него в рантайме нет")]
    TypeValue {
        /// Имя семейства.
        name: String,
    },

    /// Форма терма, которой чистый фрагмент не знает.
    #[error("{form} этим срезом не берётся")]
    Unsupported {
        /// Что именно встретилось.
        form: &'static str,
    },

    /// Ответ программы - функция.
    #[error("ответ программы - функция: печатать её нечем")]
    FunctionAnswer,

    /// Конструкторов больше, чем тегов: верх диапазона занят рантаймом.
    #[error("конструкторов больше {limit}: верх диапазона тегов занят рантаймом")]
    TooManyConstructors {
        /// Сколько их помещается.
        limit: u16,
    },

    /// Переменная за пределами захваченной среды - дефект анализа свободных.
    #[error("переменная #{index} вне захваченной среды")]
    Unbound {
        /// Индекс де Брёйна.
        index: u32,
    },

    /// Живому связыванию не досталось аргумента.
    #[error("`{name}`: живому связыванию #{binder} не досталось аргумента")]
    Missing {
        /// Кому.
        name: String,
        /// Какому связыванию.
        binder: usize,
    },
}

/// Верх диапазона тегов занят служебными объектами рантайма (`adamas.h`).
const TAGS: u16 = 0xFFF0;

/// Понижает терм в программу.
///
/// `entry` - тело `main` с подставленными аргументами уровня и row, то есть
/// ровно то, что вычисляет `adamas eval`.
///
/// # Errors
///
/// [`LowerError`] - форма вне чистого фрагмента либо имя, которого не понизить.
pub fn lower(signature: &Signature, entry: &Term) -> Result<Program, LowerError> {
    Lowerer::new(signature).program(entry)
}

/// Где лежит связывание, видимое телу.
#[derive(Clone, Debug)]
enum Slot {
    /// Связано: номер и факты.
    Bound(LocalId, Fact),
    /// Не захвачено этой функцией: ссылаться на него неоткуда.
    Absent,
}

/// Локальное состояние одной понижаемой функции.
#[derive(Debug, Default)]
struct Scope {
    /// Сколько локальных номеров уже выдано.
    locals: u32,
    /// Связывания в порядке связывания: последнее - индекс 0.
    env: Vec<Slot>,
}

impl Scope {
    /// Свежий номер.
    fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.locals);
        self.locals += 1;
        id
    }

    /// Связывание по индексу де Брёйна.
    fn slot(&self, Index(index): Index) -> Result<&Slot, LowerError> {
        let from_top = usize::try_from(index).unwrap_or(usize::MAX);
        self.env
            .len()
            .checked_sub(from_top + 1)
            .and_then(|position| self.env.get(position))
            .ok_or(LowerError::Unbound { index })
    }
}

/// Понижение: сигнатура на входе, программа на выходе.
struct Lowerer<'a> {
    signature: &'a Signature,
    constructors: Vec<Constructor>,
    tags: HashMap<Name, CtorId>,
    functions: Vec<Function>,
    numbers: HashMap<Name, FuncId>,
    /// Определения, чьи тела ещё не понижены.
    pending: VecDeque<(FuncId, Name)>,
}

impl<'a> Lowerer<'a> {
    fn new(signature: &'a Signature) -> Self {
        Self {
            signature,
            constructors: Vec::new(),
            tags: HashMap::new(),
            functions: Vec::new(),
            numbers: HashMap::new(),
            pending: VecDeque::new(),
        }
    }

    /// Понижает точку входа и всё, до чего она дотягивается.
    fn program(mut self, entry: &Term) -> Result<Program, LowerError> {
        if matches!(entry, Term::Lam(..)) {
            return Err(LowerError::FunctionAnswer);
        }
        let entry_id = FuncId(0);
        self.functions.push(Function {
            id: entry_id,
            name: "main".to_owned(),
            form: form(),
            captured: Vec::new(),
            parameters: Vec::new(),
            body: Expr::Erased,
        });
        let mut scope = Scope::default();
        let body = self.expr(&mut scope, entry)?;
        self.functions[entry_id.0].body = body;

        // Очередь, а не рекурсия: имя получает номер до того, как понижено его
        // тело, поэтому рекурсия и взаимная рекурсия проходят сами собой.
        while let Some((id, name)) = self.pending.pop_front() {
            let (parameters, inner) = self.peeled(&name)?;
            let mut scope = Scope::default();
            for parameter in &parameters {
                scope.locals += 1;
                scope.env.push(Slot::Bound(parameter.local, parameter.fact));
            }
            let body = self.expr(&mut scope, &inner)?;
            self.functions[id.0].body = body;
        }

        Ok(Program {
            constructors: self.constructors,
            functions: self.functions,
            entry: entry_id,
        })
    }

    /// Определение по имени.
    fn definition(&self, name: &Name) -> Result<&'a adamas_core::sig::Definition, LowerError> {
        self.signature
            .lookup(name)
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Параметры определения и тело под ними.
    ///
    /// Параметров столько, сколько ведущих лямбд у тела; кратность каждого
    /// берётся из **типа**, а не из лямбды - тем же правилом, каким машина
    /// решает, стирать ли аргумент.
    fn peeled(&self, name: &Name) -> Result<(Vec<Binding>, Rc<Term>), LowerError> {
        let definition = self.definition(name)?;
        let body = definition.body.as_ref().ok_or_else(|| {
            // Невыразимое имя без тела заводит элаборация эффектов: `#handle.L`,
            // `#handleMulti.L`, `#mask`, `#closing`. Звать их постулатами
            // формально верно и по существу неверно - автор постулата не писал,
            // а написал `handle`.
            if name.starts_with('#') {
                LowerError::Effectful {
                    name: name.to_string(),
                }
            } else {
                LowerError::Postulate {
                    name: name.to_string(),
                }
            }
        })?;
        let mut parameters = Vec::new();
        let mut current = Rc::new(body.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(_, bound, inner) = &*step else {
                break;
            };
            let mult = binder_at(&definition.ty, parameters.len()).unwrap_or(Mult::Many);
            parameters.push(Binding {
                name: bound.to_string(),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult),
            });
            current = Rc::clone(inner);
        }
        Ok((parameters, current))
    }

    /// Номер функции определения; тело откладывается в очередь.
    fn function(&mut self, name: &Name) -> Result<FuncId, LowerError> {
        if let Some(id) = self.numbers.get(name) {
            return Ok(*id);
        }
        let (parameters, _) = self.peeled(name)?;
        let id = FuncId(self.functions.len());
        self.functions.push(Function {
            id,
            name: name.to_string(),
            form: form(),
            captured: Vec::new(),
            parameters,
            body: Expr::Erased,
        });
        self.numbers.insert(Rc::clone(name), id);
        self.pending.push_back((id, Rc::clone(name)));
        Ok(id)
    }

    /// Заводит теги всем конструкторам семейства разом.
    ///
    /// Разом потому, что разбор требует тега у каждой ветви, а не только у
    /// встреченных конструкторов.
    fn family(&mut self, data: &Name) -> Result<(), LowerError> {
        let definition = self.definition(data)?;
        let DefinitionKind::Data {
            constructors,
            params,
            ..
        } = &definition.kind
        else {
            return Err(LowerError::TypeValue {
                name: data.to_string(),
            });
        };
        for name in constructors {
            if self.tags.contains_key(name) {
                continue;
            }
            let tag = u16::try_from(self.constructors.len())
                .ok()
                .filter(|tag| *tag < TAGS)
                .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
            let binders = binders_of(&self.definition(name)?.ty);
            self.constructors.push(Constructor {
                tag: CtorId(tag),
                name: name.to_string(),
                data: data.to_string(),
                binders,
                params: *params,
            });
            self.tags.insert(Rc::clone(name), CtorId(tag));
        }
        Ok(())
    }

    /// Тег конструктора: семейство заводится целиком по дороге.
    fn tag(&mut self, name: &Name) -> Result<CtorId, LowerError> {
        if let Some(tag) = self.tags.get(name) {
            return Ok(*tag);
        }
        let DefinitionKind::Constructor { data } = &self.definition(name)?.kind else {
            return Err(LowerError::Unknown {
                name: name.to_string(),
            });
        };
        self.family(data)?;
        self.tags
            .get(name)
            .copied()
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Понижает выражение.
    fn expr(&mut self, scope: &mut Scope, term: &Term) -> Result<Expr, LowerError> {
        match term {
            Term::Var(index) => match scope.slot(*index)? {
                Slot::Bound(local, fact) if fact.present => Ok(Expr::Local(*local)),
                Slot::Bound(..) => Ok(Expr::Erased),
                Slot::Absent => Err(LowerError::Unbound { index: index.0 }),
            },
            Term::Lam(..) => self.closure(scope, term),
            Term::App(..) | Term::Const(..) => {
                let (head, arguments) = spine(term);
                self.application(scope, head, &arguments)
            }
            Term::Let(mult, name, _, value, body) => {
                let value = self.expr(scope, value)?;
                let binding = Binding {
                    name: name.to_string(),
                    local: scope.fresh(),
                    // Машина считает связанное значение, не спрашивая кратности:
                    // `let 0 x = …` вычисляется наравне с прочими.
                    fact: Fact::present(*mult),
                };
                scope.env.push(Slot::Bound(binding.local, binding.fact));
                let body = self.expr(scope, body);
                scope.env.pop();
                Ok(Expr::Bind {
                    binding,
                    value: Box::new(value),
                    body: Box::new(body?),
                })
            }
            Term::Case(case) => self.analysis(scope, case),
            Term::Record(_) | Term::Object(_) | Term::With(..) | Term::Project(..) => {
                Err(LowerError::Unsupported {
                    form: "записи"
                })
            }
            Term::Pi(..)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Row(_) => Err(LowerError::Unsupported {
                form: "тип в позиции значения",
            }),
            Term::Meta(_) => Err(LowerError::Unsupported {
                form: "неразрешённая дырка",
            }),
        }
    }

    /// Понижает применение с разложенным спайном.
    fn application(
        &mut self,
        scope: &mut Scope,
        head: &Term,
        arguments: &[&Term],
    ) -> Result<Expr, LowerError> {
        let Term::Const(name, ..) = head else {
            // Голова - не имя: применяется значение, и стирания здесь не бывает.
            let mut value = self.expr(scope, head)?;
            for argument in arguments {
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(self.expr(scope, argument)?),
                };
            }
            return Ok(value);
        };
        match &self.definition(name)?.kind {
            DefinitionKind::Constructor { .. } => self.built(scope, name, arguments),
            DefinitionKind::Regular => self.called(scope, name, arguments),
            DefinitionKind::Data { .. } => Err(LowerError::TypeValue {
                name: name.to_string(),
            }),
            DefinitionKind::Effect { .. } | DefinitionKind::Operation { .. } => {
                Err(LowerError::Effectful {
                    name: name.to_string(),
                })
            }
        }
    }

    /// Применение конструктора: насыщенное собирает объект, недобранное -
    /// замыкание.
    fn built(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[&Term],
    ) -> Result<Expr, LowerError> {
        let constructor = self.tag(name)?;
        let binders = self.constructors[usize::from(constructor.0)]
            .binders
            .clone();
        // Насыщено, если всё недоданное стёрто: у него значений нет вовсе.
        let complete = arguments.len() >= binders.len()
            || binders[arguments.len()..].iter().all(|fact| !fact.present);
        if !complete {
            let mut value = Expr::ConstructClosure { constructor };
            for (position, argument) in arguments.iter().enumerate() {
                if !binders[position].present {
                    continue;
                }
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(self.expr(scope, argument)?),
                };
            }
            return Ok(value);
        }
        let mut built = Vec::with_capacity(binders.len());
        for (position, fact) in binders.iter().enumerate() {
            if !fact.present {
                built.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            built.push(self.expr(scope, argument)?);
        }
        let mut value = Expr::Construct {
            constructor,
            arguments: built,
        };
        for argument in arguments.iter().skip(binders.len()) {
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(self.expr(scope, argument)?),
            };
        }
        Ok(value)
    }

    /// Применение определения: насыщенное зовёт напрямую, недобранное -
    /// замыкание.
    fn called(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[&Term],
    ) -> Result<Expr, LowerError> {
        let function = self.function(name)?;
        let parameters: Vec<Fact> = self.functions[function.0]
            .parameters
            .iter()
            .map(|it| it.fact)
            .collect();
        let complete = arguments.len() >= parameters.len()
            || parameters[arguments.len()..]
                .iter()
                .all(|fact| !fact.present);
        if !complete {
            let mut value = Expr::Closure {
                function,
                captured: Vec::new(),
            };
            for (position, argument) in arguments.iter().enumerate() {
                if !parameters[position].present {
                    continue;
                }
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(self.expr(scope, argument)?),
                };
            }
            return Ok(value);
        }
        let mut given = Vec::with_capacity(parameters.len());
        for (position, fact) in parameters.iter().enumerate() {
            if !fact.present {
                given.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            given.push(self.expr(scope, argument)?);
        }
        let mut value = Expr::Call {
            function,
            arguments: given,
        };
        // Пересып: определение отдало функцию, и остаток спайна применяется к
        // ней. Стирания здесь уже нет - имени нет тоже.
        for argument in arguments.iter().skip(parameters.len()) {
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(self.expr(scope, argument)?),
            };
        }
        Ok(value)
    }

    /// Понижает разбор.
    fn analysis(&mut self, scope: &mut Scope, case: &Case) -> Result<Expr, LowerError> {
        self.family(&case.data)?;
        let scrutinee = self.expr(scope, &case.scrutinee)?;
        let mut arms = Vec::with_capacity(case.branches.len());
        for branch in &case.branches {
            let constructor = self.tag(&branch.constructor)?;
            let described = &self.constructors[usize::from(constructor.0)];
            let params = described.params as usize;
            let facts: Vec<Fact> = described.binders.iter().skip(params).copied().collect();
            let mut fields: Vec<Binding> = facts
                .iter()
                .enumerate()
                .map(|(position, fact)| Binding {
                    name: format!("поле{position}"),
                    local: scope.fresh(),
                    fact: *fact,
                })
                .collect();

            // Тело ветви есть функция от полей: сколько ведущих лямбд, столько
            // связываний снимается на месте, остаток применяется.
            let mut current = Rc::new((*branch.body).clone());
            let mut taken = 0;
            while taken < fields.len() {
                let step = Rc::clone(&current);
                let Term::Lam(_, bound, inner) = &*step else {
                    break;
                };
                fields[taken].name = bound.to_string();
                scope
                    .env
                    .push(Slot::Bound(fields[taken].local, fields[taken].fact));
                current = Rc::clone(inner);
                taken += 1;
            }
            let body = self.expr(scope, &current);
            scope.env.truncate(scope.env.len() - taken);
            let mut body = body?;
            for field in fields.iter().skip(taken) {
                body = Expr::Apply {
                    callee: Box::new(body),
                    argument: Box::new(if field.fact.present {
                        Expr::Local(field.local)
                    } else {
                        Expr::Erased
                    }),
                };
            }
            arms.push(Arm {
                constructor,
                fields,
                body,
            });
        }
        Ok(Expr::Match {
            scrutinee: Box::new(scrutinee),
            consumed: case.consumed,
            arms,
        })
    }

    /// Понижает лямбду в замыкание: своя функция плюс захваченная среда.
    fn closure(&mut self, scope: &mut Scope, term: &Term) -> Result<Expr, LowerError> {
        let mut parameters: Vec<(Mult, String)> = Vec::new();
        let mut current = Rc::new(term.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(mult, name, inner) = &*step else {
                break;
            };
            parameters.push((*mult, name.to_string()));
            current = Rc::clone(inner);
        }

        // Захватывается то, на что тело смотрит наружу.
        let mut free = BTreeSet::new();
        escaping(term, 0, &mut free);
        let depth = scope.env.len();
        let mut captured = Vec::new();
        let mut taken = Vec::new();
        let mut inner = Vec::with_capacity(depth + parameters.len());
        for (position, slot) in scope.env.iter().enumerate() {
            let index = u32::try_from(depth - position - 1).unwrap_or(u32::MAX);
            if !free.contains(&index) {
                inner.push(Slot::Absent);
                continue;
            }
            let Slot::Bound(local, fact) = slot else {
                return Err(LowerError::Unbound { index });
            };
            let id = LocalId(u32::try_from(captured.len()).unwrap_or(u32::MAX));
            captured.push(Binding {
                name: format!("захвачено{}", captured.len()),
                local: id,
                fact: *fact,
            });
            taken.push(if fact.present {
                Expr::Local(*local)
            } else {
                Expr::Erased
            });
            inner.push(Slot::Bound(id, *fact));
        }

        let mut nested = Scope {
            locals: u32::try_from(captured.len()).unwrap_or(u32::MAX),
            env: inner,
        };
        // Лямбда получает значение всегда: стирает машина по типу глобального
        // имени, а здесь имени нет.
        let bindings: Vec<Binding> = parameters
            .iter()
            .map(|(mult, name)| Binding {
                name: name.clone(),
                local: nested.fresh(),
                fact: Fact::present(*mult),
            })
            .collect();
        for binding in &bindings {
            nested.env.push(Slot::Bound(binding.local, binding.fact));
        }

        let function = FuncId(self.functions.len());
        self.functions.push(Function {
            id: function,
            name: format!("лямбда{}", function.0),
            form: form(),
            captured,
            parameters: bindings,
            body: Expr::Erased,
        });
        let body = self.expr(&mut nested, &current)?;
        self.functions[function.0].body = body;
        Ok(Expr::Closure {
            function,
            captured: taken,
        })
    }
}

/// Форма понижения функции.
///
/// Спрашивается она у трёхзначного вердикта §3.4 - того же, который различает
/// `@noalloc`. Вердикта пока нет вовсе: [`adamas_core::alloc`] называет его
/// отсутствие своей границей и потому считает всякий элиминатор хендлера
/// аллоцирующим. Ответ здесь известен и без него, и не по умолчанию: чистый
/// фрагмент эффектов не содержит **по построению** - операция, метка и хендлер
/// отвергаются понижением, - а без них оказаться под общим или мультишотным
/// хендлером нечему. Появятся эффекты - здесь встанет вызов вердикта, а не
/// расширение этой функции догадками.
fn form() -> Form {
    Form::Stack
}

/// Голова спайна и его аргументы слева направо.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut head = term;
    while let Term::App(callee, argument) = head {
        arguments.push(&**argument);
        head = callee;
    }
    arguments.reverse();
    (head, arguments)
}

/// Кратность `n`-го связывания типа. `None` - связываний столько нет.
///
/// Ровно то же, что считает машина: `None` значит «не стёрто», потому что
/// связывания на этом месте синтаксически не видно.
fn binder_at(ty: &Term, at: usize) -> Option<Mult> {
    let mut current = ty;
    for _ in 0..at {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    match current {
        Term::Pi(binder, ..) => Some(binder.mult),
        _ => None,
    }
}

/// Факты о связываниях типа: телескоп до результата.
fn binders_of(ty: &Term) -> Vec<Fact> {
    let mut facts = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, _, _, _, codomain) = current {
        facts.push(Fact::declared(binder.mult));
        current = codomain;
    }
    facts
}

/// Индексы, уходящие за `depth`, приведённые к внешнему счёту.
///
/// Обход идёт по позициям, где значение доживает до исполнения: типы, мотив
/// разбора и телескопы пропускаются - переменную оттуда захватывать незачем,
/// а понижение туда не заходит вовсе.
fn escaping(term: &Term, depth: u32, out: &mut BTreeSet<u32>) {
    match term {
        Term::Var(Index(index)) => {
            if *index >= depth {
                out.insert(index - depth);
            }
        }
        Term::Lam(_, _, body) => escaping(body, depth + 1, out),
        Term::App(callee, argument) => {
            escaping(callee, depth, out);
            escaping(argument, depth, out);
        }
        Term::Let(_, _, _, value, body) => {
            escaping(value, depth, out);
            escaping(body, depth + 1, out);
        }
        Term::Case(case) => {
            escaping(&case.scrutinee, depth, out);
            for branch in &case.branches {
                escaping(&branch.body, depth, out);
            }
        }
        _ => {}
    }
}

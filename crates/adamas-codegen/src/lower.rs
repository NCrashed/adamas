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
//! # Откуда берётся представление (§4.11)
//!
//! Плоское значение заголовка не имеет вовсе (§13, 2026-09-08), поэтому
//! [`Repr`] обязан быть известен **до** эмиссии: от него зависят C-тип
//! связывания, наличие RC-трафика и то, чем считает слот дроп с печатью.
//!
//! Читается он там, где тип **написан**: домен `Pi` даёт представление
//! параметра и поля конструктора, аннотация `let` - своего связывания, а
//! литерал и операция несут тип в себе. Дальше представление **синтезируется**
//! снизу вверх - каждое выражение отдаёт своё вместе с собой, - и в объявленных
//! позициях сверяется. Расхождение отвергается
//! ([`LowerError::Representation`]), а не приводится молча: биты числа,
//! принятые за указатель, суть чтение по адресу этого числа.
//!
//! Написан тип не везде: у связывания лямбды его нет в ядре вовсе. Поэтому
//! связывание лямбды объявляется указательным, а плоское значение,
//! пришедшее в такую позицию, отвергается. Граница названа и совпадает с
//! §4.11: обобщённый код над `{Flat a}` получает дескриптор layout имплиситом,
//! а дескрипторов в рантайме пока нет - это следующая половина трека.
//!
//! # Чего понижение не делает
//!
//! Не бета-редуцирует, не инлайнит, не кеширует значение определения без
//! параметров: оптимизаций на этом срезе нет вовсе, и предсказуемость выхода
//! дороже его длины.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use adamas_core::mult::Mult;
use adamas_core::prim::Prim;
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::term::{Case, Index, Name, Term};

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Expr, Fact, Form, FuncId, Function, LocalId, Program, Repr,
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

    /// Представление значения разошлось с представлением позиции (§4.11).
    ///
    /// Отказ, а не приведение: заголовка у плоского значения нет вовсе, и
    /// положить его туда, где ждут указатель, значит отдать биты числа
    /// счётчику ссылок.
    #[error("{at}: ожидалось {want}, а пришло {got} (§4.11)")]
    Representation {
        /// В какой позиции.
        at: &'static str,
        /// Что там объявлено.
        want: String,
        /// Что туда пришло.
        got: String,
    },

    /// Примитивная операция без обоих аргументов.
    ///
    /// Значением она была бы замыканием, а замыкание принимает аргументы
    /// указательными: плоскому нужен дескриптор layout (§4.11), и это
    /// следующая половина трека.
    #[error("`{name}` без обоих аргументов: примитив значением требует дескриптора layout (§4.11)")]
    Partial {
        /// Имя операции.
        name: String,
    },
}

/// Требует, чтобы все живые связывания были указательными.
fn pointing(facts: &[Fact], at: &'static str) -> Result<(), LowerError> {
    for fact in facts {
        if fact.present && !fact.repr.boxed() {
            return Err(LowerError::Representation {
                at,
                want: describe(Repr::Boxed),
                got: describe(fact.repr),
            });
        }
    }
    Ok(())
}

/// Как представление называется в отказе.
fn describe(repr: Repr) -> String {
    match repr {
        Repr::Boxed => "указательное значение".to_owned(),
        Repr::Flat(ty) => format!("плоское `{ty}`"),
    }
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
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let mut scope = Scope::default();
        let (body, repr) = self.expr(&mut scope, entry)?;
        self.functions[entry_id.0].body = body;
        // У точки входа объявленного типа нет - она уже инстанцирована, - и
        // представление ответа берётся у самого ответа.
        self.functions[entry_id.0].result = repr;

        // Очередь, а не рекурсия: имя получает номер до того, как понижено его
        // тело, поэтому рекурсия и взаимная рекурсия проходят сами собой.
        while let Some((id, name)) = self.pending.pop_front() {
            let (parameters, inner) = self.peeled(&name)?;
            let mut scope = Scope::default();
            for parameter in &parameters {
                scope.locals += 1;
                scope.env.push(Slot::Bound(parameter.local, parameter.fact));
            }
            let (body, repr) = self.expr(&mut scope, &inner)?;
            let declared = self.functions[id.0].result;
            if repr != declared {
                return Err(LowerError::Representation {
                    at: "ответ функции",
                    want: describe(declared),
                    got: describe(repr),
                });
            }
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
            let (mult, repr) = binder_at(self.signature, &definition.ty, parameters.len())
                .unwrap_or((Mult::Many, Repr::Boxed));
            parameters.push(Binding {
                name: bound.to_string(),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult).shaped(repr),
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
        let result = result_repr(self.signature, &self.definition(name)?.ty, parameters.len());
        let id = FuncId(self.functions.len());
        self.functions.push(Function {
            id,
            name: name.to_string(),
            form: form(),
            captured: Vec::new(),
            parameters,
            result,
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
            let binders = binders_of(self.signature, &self.definition(name)?.ty);
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

    /// Понижает выражение и отдаёт его представление (§4.11).
    ///
    /// Представление синтезируется, а не проверяется: у каждого узла оно своё,
    /// и в объявленных позициях сверяется [`Lowerer::shaped`].
    fn expr(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        match term {
            Term::Var(index) => match scope.slot(*index)? {
                Slot::Bound(local, fact) if fact.present => Ok((Expr::Local(*local), fact.repr)),
                Slot::Bound(..) => Ok((Expr::Erased, Repr::Boxed)),
                Slot::Absent => Err(LowerError::Unbound { index: index.0 }),
            },
            Term::Lam(..) => self.closure(scope, term),
            Term::App(..) | Term::Const(..) | Term::Prim(_) => {
                let (head, arguments) = spine(term);
                self.application(scope, head, &arguments)
            }
            Term::Let(mult, name, ty, value, body) => {
                let declared = repr_of(self.signature, ty);
                let value = self.shaped(scope, value, declared, "связанное значение")?;
                let binding = Binding {
                    name: name.to_string(),
                    local: scope.fresh(),
                    // Машина считает связанное значение, не спрашивая кратности:
                    // `let 0 x = …` вычисляется наравне с прочими.
                    fact: Fact::present(*mult).shaped(declared),
                };
                scope.env.push(Slot::Bound(binding.local, binding.fact));
                let body = self.expr(scope, body);
                scope.env.pop();
                let (body, repr) = body?;
                Ok((
                    Expr::Bind {
                        binding,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    repr,
                ))
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

    /// Понижает подвыражение и требует от него объявленного представления.
    fn shaped(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        want: Repr,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        let (value, got) = self.expr(scope, term)?;
        if got == want {
            return Ok(value);
        }
        Err(LowerError::Representation {
            at,
            want: describe(want),
            got: describe(got),
        })
    }

    /// Понижает применение с разложенным спайном.
    fn application(
        &mut self,
        scope: &mut Scope,
        head: &Term,
        arguments: &[&Term],
    ) -> Result<(Expr, Repr), LowerError> {
        if let Term::Prim(prim) = head {
            return self.primitive(scope, *prim, arguments);
        }
        let Term::Const(name, ..) = head else {
            // Голова - не имя: применяется значение, и стирания здесь не бывает.
            let mut value = self.shaped(scope, head, Repr::Boxed, "применяемое значение")?;
            for argument in arguments {
                let argument = self.shaped(scope, argument, Repr::Boxed, "аргумент замыкания")?;
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
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

    /// Понижает примитив: тип, литерал либо операцию (§4.3, §4.11).
    ///
    /// Ячейки кучи здесь не возникает ни на одной ветке - плоское значение
    /// живёт в регистре, - и это то самое, что показывает счётчик блоков.
    fn primitive(
        &mut self,
        scope: &mut Scope,
        prim: Prim,
        arguments: &[&Term],
    ) -> Result<(Expr, Repr), LowerError> {
        match prim {
            Prim::Ty(ty) => Err(LowerError::TypeValue {
                name: ty.name().to_owned(),
            }),
            Prim::Lit(ty, bits) => {
                if arguments.is_empty() {
                    Ok((Expr::Literal { ty, bits }, Repr::Flat(ty)))
                } else {
                    Err(LowerError::Unsupported {
                        form: "литерал в позиции функции",
                    })
                }
            }
            Prim::Op(op, ty) => {
                let [left, right] = arguments else {
                    return Err(LowerError::Partial {
                        name: format!("{op}{ty}"),
                    });
                };
                let want = Repr::Flat(ty);
                let left = self.shaped(scope, left, want, "левый аргумент операции")?;
                let right = self.shaped(scope, right, want, "правый аргумент операции")?;
                Ok((
                    Expr::Primitive {
                        op,
                        ty,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    want,
                ))
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
    ) -> Result<(Expr, Repr), LowerError> {
        let constructor = self.tag(name)?;
        let binders = self.constructors[usize::from(constructor.0)]
            .binders
            .clone();
        // Насыщено, если всё недоданное стёрто: у него значений нет вовсе.
        let complete = arguments.len() >= binders.len()
            || binders[arguments.len()..].iter().all(|fact| !fact.present);
        if !complete {
            // Недобранное собирается замыканием, а замыкание копит аргументы
            // слотами указателей: плоскому полю там места нет (§4.11).
            pointing(&binders, "поле недобранного конструктора")?;
            let mut value = Expr::ConstructClosure { constructor };
            for (position, argument) in arguments.iter().enumerate() {
                if !binders[position].present {
                    continue;
                }
                let argument = self.shaped(
                    scope,
                    argument,
                    Repr::Boxed,
                    "аргумент недобранного конструктора",
                )?;
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
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
            built.push(self.shaped(scope, argument, fact.repr, "поле конструктора")?);
        }
        // Переиспользование ставит вставка RC ([`crate::perceus`]): понижение
        // разобранного не помнит, а она помнит.
        let mut value = Expr::Construct {
            constructor,
            reuse: None,
            arguments: built,
        };
        for argument in arguments.iter().skip(binders.len()) {
            let argument = self.shaped(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Применение определения: насыщенное зовёт напрямую, недобранное -
    /// замыкание.
    fn called(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[&Term],
    ) -> Result<(Expr, Repr), LowerError> {
        let function = self.function(name)?;
        let parameters: Vec<Fact> = self.functions[function.0]
            .parameters
            .iter()
            .map(|it| it.fact)
            .collect();
        let result = self.functions[function.0].result;
        let complete = arguments.len() >= parameters.len()
            || parameters[arguments.len()..]
                .iter()
                .all(|fact| !fact.present);
        if !complete {
            // Недобранный вызов уходит замыканием, а трамплин отдаёт слоты
            // указателями: плоский параметр или плоский ответ через него не
            // проходят (§4.11).
            pointing(&parameters, "параметр недобранного вызова")?;
            if !result.boxed() {
                return Err(LowerError::Representation {
                    at: "ответ недобранного вызова",
                    want: describe(Repr::Boxed),
                    got: describe(result),
                });
            }
            let mut value = Expr::Closure {
                function,
                captured: Vec::new(),
            };
            for (position, argument) in arguments.iter().enumerate() {
                if !parameters[position].present {
                    continue;
                }
                let argument =
                    self.shaped(scope, argument, Repr::Boxed, "аргумент недобранного вызова")?;
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
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
            given.push(self.shaped(scope, argument, fact.repr, "аргумент вызова")?);
        }
        let mut value = Expr::Call {
            function,
            arguments: given,
        };
        let extra = arguments.len().saturating_sub(parameters.len());
        if extra == 0 {
            return Ok((value, result));
        }
        // Пересып: определение отдало функцию, и остаток спайна применяется к
        // ней. Стирания здесь уже нет - имени нет тоже.
        if !result.boxed() {
            return Err(LowerError::Representation {
                at: "применяемое значение",
                want: describe(Repr::Boxed),
                got: describe(result),
            });
        }
        for argument in arguments.iter().skip(parameters.len()) {
            let argument = self.shaped(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Понижает разбор.
    fn analysis(&mut self, scope: &mut Scope, case: &Case) -> Result<(Expr, Repr), LowerError> {
        self.family(&case.data)?;
        // Разбирается объект: тег лежит в его заголовке, а у плоского значения
        // заголовка нет вовсе (§4.11).
        let scrutinee = self.shaped(scope, &case.scrutinee, Repr::Boxed, "разбираемое")?;
        // Пустой разбор ответа не даёт: тип пуст, и до печати дело не дойдёт.
        let mut answer = Repr::Boxed;
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
            let (mut body, mut repr) = body?;
            for field in fields.iter().skip(taken) {
                if !repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "применяемое значение",
                        want: describe(Repr::Boxed),
                        got: describe(repr),
                    });
                }
                if field.fact.present && !field.fact.repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "неснятое поле ветви",
                        want: describe(Repr::Boxed),
                        got: describe(field.fact.repr),
                    });
                }
                body = Expr::Apply {
                    callee: Box::new(body),
                    argument: Box::new(if field.fact.present {
                        Expr::Local(field.local)
                    } else {
                        Expr::Erased
                    }),
                };
                repr = Repr::Boxed;
            }
            // Ветви отвечают одним значением, значит и представление у них
            // одно: разойдись оно, у разбора не было бы C-типа.
            if arms.is_empty() {
                answer = repr;
            } else if repr != answer {
                return Err(LowerError::Representation {
                    at: "ветвь разбора",
                    want: describe(answer),
                    got: describe(repr),
                });
            }
            arms.push(Arm {
                constructor,
                fields,
                body,
            });
        }
        Ok((
            Expr::Match {
                scrutinee: Box::new(scrutinee),
                consumed: case.consumed,
                arms,
            },
            answer,
        ))
    }

    /// Понижает лямбду в замыкание: своя функция плюс захваченная среда.
    ///
    /// Связывания лямбды объявляются указательными: типа у них в ядре нет, и
    /// прочитать представление неоткуда. Плоское значение поэтому через
    /// границу замыкания не проходит - ни захватом, ни аргументом, - и это
    /// названная граница, а не упущение: §4.11 отдаёт этот случай дескриптору
    /// layout, которого в рантайме ещё нет.
    fn closure(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
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
            if fact.present && !fact.repr.boxed() {
                return Err(LowerError::Representation {
                    at: "захват замыкания",
                    want: describe(Repr::Boxed),
                    got: describe(fact.repr),
                });
            }
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
            // Ответ замыкания приходит через `adamas_apply`, а он говорит
            // указателями: плоский ответ ему не отдать.
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let body = self.shaped(&mut nested, &current, Repr::Boxed, "тело замыкания")?;
        self.functions[function.0].body = body;
        Ok((
            Expr::Closure {
                function,
                captured: taken,
            },
            Repr::Boxed,
        ))
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

/// Тип после `at` снятых связываний. `None` - связываний столько нет.
fn after(ty: &Term, at: usize) -> Option<&Term> {
    let mut current = ty;
    for _ in 0..at {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    Some(current)
}

/// Сколько алиасов подряд разворачивается по дороге к примитиву.
///
/// Цепочка `type Int = Int64` конечна по построению - ordered scoping (§4.8)
/// не даёт имени сослаться на себя, - но предел стоит: обход по чужой
/// сигнатуре не должен зависать, если она окажется собрана иначе.
const ALIASES: usize = 32;

/// Представление значения написанного типа (§4.11).
///
/// Плоским считается ровно примитив: `Flat` над записями и семействами
/// (§4.11, укладка тегом) существует типовой стороной, а укладывать его в
/// понижении нечем, пока нет дескриптора layout, - это следующая половина
/// трека.
///
/// **Алиас разворачивается.** `Int` и `Float` - прелюдные синонимы `Int64` и
/// `Float64` (§4.3, лог 2026-09-09), то есть каноническое имя написанной
/// программы, и представление есть свойство типа, а не его написания: типовая
/// сторона `Flat` (`adamas-elab/src/flat.rs`) читает укладку у **значения**
/// типа и потому синоним видит насквозь. Разворачивается только имя без
/// аргументов и только у определения, чей тип - универсум: параметризованный
/// алиас требует подстановки, которой понижение не делает, и остаётся
/// указательным.
fn repr_of(signature: &Signature, ty: &Term) -> Repr {
    let mut current = ty;
    for _ in 0..ALIASES {
        match current {
            Term::Prim(Prim::Ty(prim)) => return Repr::Flat(*prim),
            Term::Const(name, ..) => {
                let Some(definition) = signature.lookup(name) else {
                    return Repr::Boxed;
                };
                if !matches!(definition.kind, DefinitionKind::Regular)
                    || !matches!(definition.ty, Term::Universe(_))
                {
                    return Repr::Boxed;
                }
                let Some(body) = definition.body.as_ref() else {
                    return Repr::Boxed;
                };
                current = body;
            }
            _ => return Repr::Boxed,
        }
    }
    Repr::Boxed
}

/// Кратность и представление `n`-го связывания типа.
///
/// Ровно то же, что считает машина: `None` значит «не стёрто», потому что
/// связывания на этом месте синтаксически не видно.
fn binder_at(signature: &Signature, ty: &Term, at: usize) -> Option<(Mult, Repr)> {
    match after(ty, at)? {
        Term::Pi(binder, _, domain, _, _) => Some((binder.mult, repr_of(signature, domain))),
        _ => None,
    }
}

/// Представление ответа после `taken` снятых связываний.
///
/// Снято меньше, чем стрелок в типе, - ответ функция, то есть указатель.
fn result_repr(signature: &Signature, ty: &Term, taken: usize) -> Repr {
    after(ty, taken).map_or(Repr::Boxed, |result| repr_of(signature, result))
}

/// Факты о связываниях типа: телескоп до результата.
fn binders_of(signature: &Signature, ty: &Term) -> Vec<Fact> {
    let mut facts = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, _, domain, _, codomain) = current {
        facts.push(Fact::declared(binder.mult).shaped(repr_of(signature, domain)));
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

//! Элаборация клауз в дерево разбора (§9 Фаза 1, §10 вопрос 7).
//!
//! Ядро умеет ровно один разбор на один уровень конструкторов
//! ([`crate::term::Case`]). Пользователь пишет иначе - несколькими клаузами со
//! вложенными паттернами:
//!
//! ```text
//! plus zero     m = m
//! plus (succ k) m = succ (plus k m)
//! ```
//!
//! Здесь это превращается в цепочку узлов. Стратегия - классическая
//! компиляция сопоставления (Augustsson, Maranget): пока первая клауза не
//! состоит из одних переменных, берётся её левейшая колонка с конструктором и
//! по ней делается разбор; каждая ветвь получает те клаузы, что ей подходят.
//! Отсюда же семантика **первого совпадения**.
//!
//! # Что элаборация не гарантирует
//!
//! Ничего. Она выдаёт обычный терм ядра, и корректность его проверяет
//! [`crate::check`] - как и всякого другого. Это не небрежность, а разделение
//! ответственности: элаборатор не входит в TCB, поэтому ошибка в нём даёт
//! отказ, а не принятую некорректную программу.
//!
//! Полнота при этом обеспечивается **построением**: ветви порождаются по списку
//! конструкторов, поэтому непокрытым остаётся не случай, а клауза - и о ней
//! сообщается ([`PatternError::NonExhaustive`]). Недостижимая клауза
//! обнаруживается тем же обходом. Пустое семейство разбирается и без клауз:
//! ветвей ноль, и разбор сам доказывает, что вызвать функцию нечем.
//!
//! # Уточняется только разбираемый аргумент
//!
//! Ветвь знает, что разбираемое значение построено конструктором, и это видят
//! тип результата и тела клауз. Типы **остальных** аргументов не уточняются:
//! ядро связывает мотив с одним значением, а чтобы уточнить соседей, их надо
//! абстрагировать в тот же мотив и применить обратно (convoy-паттерн). Поэтому
//! `g : (b : Bool) -> If b -> Nat` не пишется клаузами, хотя индексов здесь
//! нет: в ветви `true` аргумент остаётся типа `If b`. См. §10 вопрос 44.
//!
//! # Индексированные семейства не поддержаны
//!
//! Разбор `Vect` требует унификации индексов: ветвь `vnil` осмысленна только
//! при длине `zero`, а `head : Vect A (succ n) -> A` вообще не должна
//! порождать ветвь `vnil`. Ни того ни другого здесь нет, и семейство с
//! индексами отвергается явно ([`PatternError::IndexedFamily`]) - лучше
//! честный отказ, чем терм, который потом не пройдёт проверку с непонятным
//! сообщением. Параметры при этом поддержаны полностью.

use std::fmt;
use std::rc::Rc;

use crate::check::instantiate_telescope;
use crate::ctx::Ctx;
use crate::eval::quote;
use crate::level::Level;
use crate::mult::Mult;
use crate::sig::{DefinitionKind, Signature};
use crate::term::{Branch, Case, Index, Name, Term};
use crate::value::{Elim, Head, Lvl, Value};

/// Паттерн клаузы.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    /// Связывает значение под именем. Имя нужно только для печати.
    Var(Name),
    /// Конструктор и подпаттерны его полей - без параметров, как и в ветви
    /// [`Case`]: параметры определены типом, а не выбором конструктора.
    Constructor(Name, Vec<Pattern>),
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Var(name) => write!(f, "{name}"),
            Self::Constructor(name, fields) if fields.is_empty() => write!(f, "{name}"),
            Self::Constructor(name, fields) => {
                write!(f, "{name}")?;
                for field in fields {
                    match field {
                        Self::Constructor(_, sub) if !sub.is_empty() => write!(f, " ({field})")?,
                        _ => write!(f, " {field}")?,
                    }
                }
                Ok(())
            }
        }
    }
}

/// Одна клауза: паттерн на каждый аргумент и тело.
///
/// Тело записано в контексте из переменных **этой** клаузы, взятых слева
/// направо в глубину: первая переменная - самое внешнее связывание. Ничего
/// другого тело видеть не может.
#[derive(Clone, Debug)]
pub struct Clause {
    /// По паттерну на аргумент.
    pub patterns: Vec<Pattern>,
    /// Тело.
    pub body: Term,
}

/// Ошибка элаборации клауз.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum PatternError {
    /// В клаузе не столько паттернов, сколько у функции аргументов.
    #[error("клауза #{clause}: {found} паттернов при {expected} аргументах")]
    ClauseArity {
        /// Номер клаузы.
        clause: usize,
        /// Сколько аргументов у функции.
        expected: usize,
        /// Сколько паттернов написано.
        found: usize,
    },

    /// Тело клаузы ссылается на связывание, которого у неё нет.
    #[error("клауза #{clause}: тело ссылается за пределы своих переменных")]
    UnboundInBody {
        /// Номер клаузы.
        clause: usize,
    },

    /// Тип определения ссылается на связывание, которого у него нет.
    #[error("тип ссылается за пределы своих аргументов")]
    UnboundInType,

    /// Разбирается значение, тип которого не индуктивное семейство.
    #[error("разбирать нечего: значение имеет тип `{ty}`")]
    NotMatchable {
        /// Тип значения.
        ty: String,
    },

    /// Семейство с индексами - см. заголовок модуля.
    #[error("`{data}` - семейство с индексами, элаборация паттернов их не умеет")]
    IndexedFamily {
        /// Имя типа.
        data: Name,
    },

    /// Паттерн называет конструктор чужого типа.
    #[error("конструктор `{constructor}` не принадлежит типу `{data}`")]
    ForeignConstructor {
        /// Имя из паттерна.
        constructor: Name,
        /// Тип разбираемого значения.
        data: Name,
    },

    /// У конструктора в паттерне не столько подпаттернов, сколько полей.
    #[error("конструктор `{constructor}`: {found} подпаттернов при {expected} полях")]
    ConstructorArity {
        /// Имя конструктора.
        constructor: Name,
        /// Сколько у него полей.
        expected: usize,
        /// Сколько написано.
        found: usize,
    },

    /// Клаузы не покрывают всех случаев.
    #[error("не покрыто: `{example}`")]
    NonExhaustive {
        /// Пример непокрытого набора аргументов.
        example: String,
    },

    /// Клауза не может сработать ни на одном входе.
    #[error("клауза #{clause} недостижима: её перекрывают предыдущие")]
    UnreachableClause {
        /// Номер клаузы.
        clause: usize,
    },
}

/// Собирает клаузы в дерево разбора.
///
/// `ty` - тип определяемой функции; из него берутся кратности аргументов и тип
/// результата. Результат - терм этого типа, готовый уйти в
/// [`crate::sig::Signature::define`], который его и проверит.
///
/// Сколько аргументов разбирается, решают клаузы, а не тип: определение вправе
/// вернуть функцию, и `twice g = \x. g (g x)` - такое же определение, как
/// `twice g x = g (g x)`. Клаузы обязаны сойтись между собой. Без клауз
/// снимаются все `Pi`: разбирать тогда можно только пустое семейство, и колонки
/// для этого нужны все.
///
/// # Errors
///
/// Несовпадение арности, чужой конструктор, семейство с индексами, непокрытый
/// случай, недостижимая клауза.
pub fn compile(signature: &Signature, ty: &Term, clauses: &[Clause]) -> Result<Term, PatternError> {
    let wanted = clauses
        .first()
        .map_or(usize::MAX, |clause| clause.patterns.len());

    // Телескоп аргументов: кратности и имена пойдут в лямбды, типы - в колонки.
    let mut ctx = Ctx::new(signature);
    let mut telescope = Vec::new();
    let mut current = ty;
    while let Term::Pi(mult, name, domain, codomain) = current {
        if telescope.len() == wanted {
            break;
        }
        let domain = ctx.eval(domain);
        ctx = ctx.bind(Rc::clone(name), *mult, Rc::clone(&domain));
        telescope.push((*mult, Rc::clone(name), domain));
        current = codomain;
    }
    let arity = telescope.len();
    if !clauses.is_empty() && arity != wanted {
        return Err(PatternError::ClauseArity {
            clause: 0,
            expected: arity,
            found: wanted,
        });
    }
    let target = current.clone();
    if !well_scoped(&target, arity_u32(arity)) {
        return Err(PatternError::UnboundInType);
    }

    let mut rows = Vec::with_capacity(clauses.len());
    for (index, clause) in clauses.iter().enumerate() {
        if clause.patterns.len() != arity {
            return Err(PatternError::ClauseArity {
                clause: index,
                expected: arity,
                found: clause.patterns.len(),
            });
        }
        let mut variables = 0;
        let patterns = clause
            .patterns
            .iter()
            .map(|pattern| number(pattern, &mut variables))
            .collect();
        if !well_scoped(&clause.body, arity_u32(variables)) {
            return Err(PatternError::UnboundInBody { clause: index });
        }
        rows.push(Row {
            clause: index,
            patterns,
            assigned: vec![None; variables],
            body: Rc::new(clause.body.clone()),
        });
    }

    let columns: Vec<Column> = telescope
        .iter()
        .enumerate()
        .map(|(index, (_, _, domain))| Column {
            level: arity_u32(index),
            path: vec![index],
            ty: Rc::clone(domain),
        })
        .collect();
    let example = vec![Pattern::Var("_".into()); arity];

    let mut compiler = Compiler {
        signature,
        used: vec![false; clauses.len()],
    };
    let tree = compiler.solve(&ctx, &columns, &rows, &target, &example)?;
    if let Some(clause) = compiler.used.iter().position(|used| !used) {
        return Err(PatternError::UnreachableClause { clause });
    }

    Ok(telescope
        .into_iter()
        .rev()
        .fold(tree, |body, (mult, name, _)| {
            Term::Lam(mult, name, Rc::new(body))
        }))
}

/// Паттерн с пронумерованными переменными.
#[derive(Clone, Debug)]
enum Pat {
    /// Ничего не связывает - подстановка на месте поля у переменной-паттерна.
    Any,
    /// Переменная клаузы под этим номером.
    Var(usize),
    /// Конструктор с подпаттернами.
    Ctor(Name, Vec<Pat>),
}

/// Нумерует переменные слева направо в глубину.
fn number(pattern: &Pattern, next: &mut usize) -> Pat {
    match pattern {
        Pattern::Var(_) => {
            let index = *next;
            *next += 1;
            Pat::Var(index)
        }
        Pattern::Constructor(name, fields) => Pat::Ctor(
            Rc::clone(name),
            fields.iter().map(|field| number(field, next)).collect(),
        ),
    }
}

/// Колонка задачи - значение, по которому ещё можно разбирать.
struct Column {
    /// Уровень связывания в контексте.
    level: u32,
    /// Путь до неё в исходных аргументах: номер аргумента, потом номера полей.
    /// Нужен только для примера непокрытого случая.
    path: Vec<usize>,
    /// Тип значения.
    ty: Rc<Value>,
}

/// Строка задачи - клауза с паттернами по числу колонок.
struct Row {
    clause: usize,
    patterns: Vec<Pat>,
    /// Значение каждой переменной клаузы по мере связывания.
    assigned: Vec<Option<Rc<Value>>>,
    body: Rc<Term>,
}

struct Compiler<'a> {
    signature: &'a Signature,
    used: Vec<bool>,
}

impl Compiler<'_> {
    fn solve(
        &mut self,
        ctx: &Ctx<'_>,
        columns: &[Column],
        rows: &[Row],
        target: &Term,
        example: &[Pattern],
    ) -> Result<Term, PatternError> {
        // Клауз не осталось - но случай мог оказаться и невозможным: разбор
        // пустого семейства даёт ноль ветвей и служит доказательством, что
        // вызвать функцию на этом пути нечем.
        let Some(first) = rows.first() else {
            return match self.empty_column(columns) {
                Some(split) => self.split(ctx, columns, rows, target, example, split),
                None => Err(PatternError::NonExhaustive {
                    example: render(example),
                }),
            };
        };

        // Первая клауза без конструкторов подходит под что угодно - дальше
        // разбирать нечего.
        let Some(split) = first
            .patterns
            .iter()
            .position(|pattern| matches!(pattern, Pat::Ctor(..)))
        else {
            return Ok(self.leaf(ctx, columns, first));
        };

        self.split(ctx, columns, rows, target, example, split)
    }

    /// Первая колонка, тип которой - семейство без конструкторов.
    fn empty_column(&self, columns: &[Column]) -> Option<usize> {
        columns.iter().position(|column| {
            data_head(self.signature, &column.ty).is_some_and(|(data, ..)| {
                matches!(
                    self.signature.lookup(&data).map(|found| &found.kind),
                    Some(DefinitionKind::Data { constructors, .. }) if constructors.is_empty()
                )
            })
        })
    }

    /// Тело клаузы, переписанное в текущий контекст.
    fn leaf(&mut self, ctx: &Ctx<'_>, columns: &[Column], row: &Row) -> Term {
        self.used[row.clause] = true;
        let mut assigned = row.assigned.clone();
        for (column, pattern) in columns.iter().zip(&row.patterns) {
            if let Pat::Var(variable) = pattern {
                assigned[*variable] = Some(Value::var(Lvl(column.level)));
            }
        }
        let bound = arity_u32(assigned.len());
        let size = ctx.size();
        rewrite(&row.body, 0, bound, &|variable| {
            let value = assigned[variable as usize]
                .as_ref()
                .unwrap_or_else(|| unreachable!("переменная клаузы осталась несвязанной"));
            quote(size, value)
        })
    }

    /// Разбор по колонке `split`.
    fn split(
        &mut self,
        ctx: &Ctx<'_>,
        columns: &[Column],
        rows: &[Row],
        target: &Term,
        example: &[Pattern],
        split: usize,
    ) -> Result<Term, PatternError> {
        let column = &columns[split];
        let Family {
            data,
            levels,
            params,
            constructors,
            parameters,
        } = self.family(ctx, column, rows, split)?;

        let size = ctx.size();
        let mut branches = Vec::with_capacity(constructors.len());
        for constructor in &constructors {
            let fields = self.fields(ctx, constructor, &levels, &params);
            let mut inner = ctx.clone();
            for field in &fields {
                inner = inner.bind(Rc::clone(&field.name), field.mult, Rc::clone(&field.ty));
            }

            let mut inner_columns = Vec::with_capacity(columns.len() + fields.len());
            inner_columns.extend(shallow(&columns[..split]));
            for (index, field) in fields.iter().enumerate() {
                let mut path = column.path.clone();
                path.push(index);
                inner_columns.push(Column {
                    level: field.level,
                    path,
                    ty: Rc::clone(&field.ty),
                });
            }
            inner_columns.extend(shallow(&columns[split + 1..]));

            // В этой ветви разбираемое значение - не переменная, а
            // построенное конструктором, и увидеть это обязаны оба: и тип
            // результата, и тело клаузы, связавшее аргумент переменной.
            // Без подстановки вложенный разбор строил бы мотив по
            // неуточнённому типу (`P n` против `P zero`), а тело ссылалось бы
            // на исходный аргумент - и тратило бы его второй раз после
            // разбора.
            let inner_size = inner.size();
            let built = fields.iter().fold(
                params.iter().fold(
                    Term::Const(Rc::clone(constructor), Rc::clone(&levels)),
                    |applied, param| Term::App(Rc::new(applied), Rc::new(quote(inner_size, param))),
                ),
                |applied, field| {
                    Term::App(
                        Rc::new(applied),
                        Rc::new(Term::Var(Lvl(field.level).to_index(inner_size))),
                    )
                },
            );
            let refined = inner.eval(&built);

            let mut inner_rows = Vec::new();
            for row in rows {
                let Some(row) = specialise(row, split, constructor, fields.len(), &refined)? else {
                    continue;
                };
                inner_rows.push(row);
            }

            let mut inner_example = example.to_vec();
            place(
                &mut inner_example,
                &column.path,
                Pattern::Constructor(
                    Rc::clone(constructor),
                    vec![Pattern::Var("_".into()); fields.len()],
                ),
            );

            let inner_target = rewrite(target, 0, size, &|level| {
                if level == column.level {
                    built.clone()
                } else {
                    Term::Var(Lvl(level).to_index(inner_size))
                }
            });

            let body = self.solve(
                &inner,
                &inner_columns,
                &inner_rows,
                &inner_target,
                &inner_example,
            )?;
            branches.push(Branch {
                constructor: Rc::clone(constructor),
                body: Rc::new(fields.iter().rev().fold(body, |body, field| {
                    Term::Lam(field.mult, Rc::clone(&field.name), Rc::new(body))
                })),
            });
        }

        let motive = Term::Lam(
            Mult::Zero,
            "x".into(),
            Rc::new(rewrite(target, 0, size, &|level| {
                let redirected = if level == column.level { size } else { level };
                Term::Var(Lvl(redirected).to_index(size + 1))
            })),
        );
        Ok(Term::Case(Rc::new(Case {
            data,
            levels,
            params: parameters,
            scrutinee: Rc::new(Term::Var(Lvl(column.level).to_index(size))),
            motive: Rc::new(motive),
            branches,
        })))
    }

    /// Индуктивное семейство колонки вместе с проверками, которые обязаны
    /// пройти до всякого разбора.
    fn family(
        &self,
        ctx: &Ctx<'_>,
        column: &Column,
        rows: &[Row],
        split: usize,
    ) -> Result<Family, PatternError> {
        let Some((data, levels, params)) = data_head(self.signature, &column.ty) else {
            return Err(PatternError::NotMatchable {
                ty: ctx.quote(&column.ty).to_string(),
            });
        };
        let Some(declaration) = self.signature.lookup(&data) else {
            unreachable!("тип `{data}` только что нашёлся")
        };
        let DefinitionKind::Data {
            constructors,
            params: parameters,
            ..
        } = &declaration.kind
        else {
            unreachable!("`{data}` опознан как индуктивный")
        };
        // Индексы потребовали бы унификации - см. заголовок модуля.
        if binders(&declaration.ty) != *parameters as usize {
            return Err(PatternError::IndexedFamily { data });
        }
        // Семейство обязано быть применено полностью, иначе поля конструктора
        // не сойдутся с параметрами. Ядро проверяет то же самое перед разбором
        // (`NotADataValue`), но `compile` работает до него, и без этой строки
        // `x : Nat zero` роняет элаборацию в `instantiate_telescope`.
        if params.len() != *parameters as usize {
            return Err(PatternError::NotMatchable {
                ty: ctx.quote(&column.ty).to_string(),
            });
        }

        // Чужой конструктор в паттерне - отказ до всякого разбора.
        for row in rows {
            if let Pat::Ctor(name, _) = &row.patterns[split] {
                if !constructors.contains(name) {
                    return Err(PatternError::ForeignConstructor {
                        constructor: Rc::clone(name),
                        data,
                    });
                }
            }
        }

        Ok(Family {
            data,
            levels,
            params,
            constructors: constructors.clone(),
            parameters: *parameters,
        })
    }

    /// Поля конструктора при заданных параметрах, с уровнями, которые они
    /// займут в контексте.
    fn fields(
        &self,
        ctx: &Ctx<'_>,
        constructor: &Name,
        levels: &Rc<[Level]>,
        params: &[Rc<Value>],
    ) -> Vec<Field> {
        let Some(declaration) = self.signature.lookup(constructor) else {
            unreachable!("конструктор `{constructor}` объявлен")
        };
        let mut current = instantiate_telescope(declaration.instantiate_type(levels), params);
        let mut fields = Vec::new();
        let mut level = ctx.size();
        while let Value::Pi(mult, name, domain, codomain) = &*current {
            fields.push(Field {
                mult: *mult,
                name: Rc::clone(name),
                level,
                ty: Rc::clone(domain),
            });
            let next = codomain.apply(Value::var(Lvl(level)));
            level += 1;
            current = next;
        }
        fields
    }
}

/// Индуктивное семейство, по которому идёт разбор колонки.
struct Family {
    data: Name,
    levels: Rc<[Level]>,
    /// Параметры семейства - те же во всех ветвях.
    params: Vec<Rc<Value>>,
    /// Конструкторы в порядке объявления: он же порядок ветвей.
    constructors: Vec<Name>,
    parameters: u32,
}

/// Поле конструктора в разбираемой ветви.
struct Field {
    mult: Mult,
    name: Name,
    level: u32,
    ty: Rc<Value>,
}

/// Приспосабливает строку к ветви конструктора.
///
/// `None` - строка этой ветви не подходит. Переменная подходит любой, и её
/// связывание получает **построенную в этой ветви форму**: `f x` в теле значит
/// всё значение целиком, но в ветви `succ` это значение - `succ k`, а не
/// исходный аргумент. Ссылка на исходный аргумент была бы верна только по
/// вычислению: тип от неё не уточняется, а расход считается вторым.
fn specialise(
    row: &Row,
    split: usize,
    constructor: &Name,
    fields: usize,
    refined: &Rc<Value>,
) -> Result<Option<Row>, PatternError> {
    let mut assigned = row.assigned.clone();
    let replacement = match &row.patterns[split] {
        Pat::Ctor(name, _) if name != constructor => return Ok(None),
        Pat::Ctor(name, subs) => {
            if subs.len() != fields {
                return Err(PatternError::ConstructorArity {
                    constructor: Rc::clone(name),
                    expected: fields,
                    found: subs.len(),
                });
            }
            subs.clone()
        }
        Pat::Var(variable) => {
            assigned[*variable] = Some(Rc::clone(refined));
            vec![Pat::Any; fields]
        }
        Pat::Any => vec![Pat::Any; fields],
    };

    let mut patterns = Vec::with_capacity(row.patterns.len() + fields);
    patterns.extend(row.patterns[..split].iter().cloned());
    patterns.extend(replacement);
    patterns.extend(row.patterns[split + 1..].iter().cloned());
    Ok(Some(Row {
        clause: row.clause,
        patterns,
        assigned,
        body: Rc::clone(&row.body),
    }))
}

/// Копия колонок без глубокого копирования типов.
fn shallow(columns: &[Column]) -> impl Iterator<Item = Column> + '_ {
    columns.iter().map(|column| Column {
        level: column.level,
        path: column.path.clone(),
        ty: Rc::clone(&column.ty),
    })
}

/// Индуктивное семейство в голове типа: имя, аргументы уровня и параметры.
type DataHead = (Name, Rc<[Level]>, Vec<Rc<Value>>);

/// Индуктивное семейство в голове типа, вместе с аргументами.
///
/// δ-разворот обязателен: у определения-синонима голова своя.
fn data_head(signature: &Signature, ty: &Rc<Value>) -> Option<DataHead> {
    let mut current = Rc::clone(ty);
    loop {
        let head = match &*current {
            Value::Neutral(Head::Global(name, levels), spine) => {
                Some((Rc::clone(name), Rc::clone(levels), spine.clone()))
            }
            _ => None,
        };
        if let Some((name, levels, spine)) = head {
            if matches!(
                signature.lookup(&name).map(|found| &found.kind),
                Some(DefinitionKind::Data { .. })
            ) {
                let arguments = spine
                    .iter()
                    .map(|elim| match elim {
                        Elim::App(argument) => Some(Rc::clone(argument)),
                        Elim::Case(_) => None,
                    })
                    .collect::<Option<Vec<_>>>()?;
                return Some((name, levels, arguments));
            }
        }
        current = crate::conv::unfold(signature, &current)?;
    }
}

/// Сколько связываний у типа.
fn binders(ty: &Term) -> usize {
    let mut count = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, codomain) = current {
        count += 1;
        current = codomain;
    }
    count
}

/// Ставит паттерн по пути в пример непокрытого случая.
fn place(example: &mut [Pattern], path: &[usize], pattern: Pattern) {
    let Some((first, rest)) = path.split_first() else {
        return;
    };
    let Some(mut current) = example.get_mut(*first) else {
        return;
    };
    for step in rest {
        let Pattern::Constructor(_, fields) = current else {
            return;
        };
        let Some(next) = fields.get_mut(*step) else {
            return;
        };
        current = next;
    }
    *current = pattern;
}

/// Печатает набор аргументов через пробел.
///
/// Скобки нужны, только когда аргументов несколько: иначе `succ _` и `zero`
/// слиплись бы в `succ _ zero`. У одноаргументной функции они лишний шум.
fn render(example: &[Pattern]) -> String {
    let separate = example.len() > 1;
    example
        .iter()
        .map(|pattern| match pattern {
            Pattern::Constructor(_, fields) if separate && !fields.is_empty() => {
                format!("({pattern})")
            }
            _ => pattern.to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Все ли свободные индексы терма попадают в контекст размера `binders`.
fn well_scoped(term: &Term, binders: u32) -> bool {
    fn go(term: &Term, depth: u32, binders: u32) -> bool {
        match term {
            Term::Var(Index(index)) => *index < depth + binders,
            Term::Universe(_) | Term::Const(..) => true,
            Term::Lam(_, _, body) => go(body, depth + 1, binders),
            Term::App(callee, argument) => {
                go(callee, depth, binders) && go(argument, depth, binders)
            }
            Term::Pi(_, _, domain, codomain) => {
                go(domain, depth, binders) && go(codomain, depth + 1, binders)
            }
            Term::Let(_, _, ty, value, body) => {
                go(ty, depth, binders) && go(value, depth, binders) && go(body, depth + 1, binders)
            }
            Term::Case(case) => {
                go(&case.scrutinee, depth, binders)
                    && go(&case.motive, depth, binders)
                    && case
                        .branches
                        .iter()
                        .all(|branch| go(&branch.body, depth, binders))
            }
        }
    }
    go(term, 0, binders)
}

/// Переписывает свободные переменные терма из контекста размера `from` в
/// контекст размера `to`, применяя `map` к уровню.
///
/// Единственная операция над индексами во всём ядре, и живёт она здесь не
/// случайно: `NbE` подстановку заменяет замыканиями, но элаборация собирает
/// терм из кусков, записанных в разных контекстах, и сшить их иначе нечем.
fn rewrite<F: Fn(u32) -> Term>(term: &Term, depth: u32, from: u32, map: &F) -> Term {
    let recur = |inner: &Rc<Term>| Rc::new(rewrite(inner, depth, from, map));
    let under = |inner: &Rc<Term>| Rc::new(rewrite(inner, depth + 1, from, map));
    match term {
        Term::Var(Index(index)) => {
            if *index < depth {
                return term.clone();
            }
            let level = from + depth - 1 - index;
            shift(&map(level), depth)
        }
        Term::Universe(_) | Term::Const(..) => term.clone(),
        Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), under(body)),
        Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
        Term::Pi(mult, name, domain, codomain) => {
            Term::Pi(*mult, Rc::clone(name), recur(domain), under(codomain))
        }
        Term::Let(mult, name, ty, value, body) => {
            Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), under(body))
        }
        Term::Case(case) => Term::Case(Rc::new(Case {
            data: Rc::clone(&case.data),
            levels: Rc::clone(&case.levels),
            params: case.params,
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

/// Поднимает терм под `by` дополнительных связываний.
///
/// Нужна [`rewrite`]: подставляемый терм записан в целевом контексте, а
/// подставляется он на глубине, где связываний уже больше.
fn shift(term: &Term, by: u32) -> Term {
    fn go(term: &Term, depth: u32, by: u32) -> Term {
        let recur = |inner: &Rc<Term>| Rc::new(go(inner, depth, by));
        let under = |inner: &Rc<Term>| Rc::new(go(inner, depth + 1, by));
        match term {
            Term::Var(Index(index)) if *index >= depth => Term::Var(Index(index + by)),
            Term::Var(_) | Term::Universe(_) | Term::Const(..) => term.clone(),
            Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), under(body)),
            Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
            Term::Pi(mult, name, domain, codomain) => {
                Term::Pi(*mult, Rc::clone(name), recur(domain), under(codomain))
            }
            Term::Let(mult, name, ty, value, body) => {
                Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), under(body))
            }
            Term::Case(case) => Term::Case(Rc::new(Case {
                data: Rc::clone(&case.data),
                levels: Rc::clone(&case.levels),
                params: case.params,
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
    if by == 0 {
        term.clone()
    } else {
        go(term, 0, by)
    }
}

/// Счётчик в `u32`. Столько аргументов и переменных не бывает.
fn arity_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or_else(|_| unreachable!("счётчик не помещается в u32"))
}

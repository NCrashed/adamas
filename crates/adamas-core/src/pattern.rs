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
//! # Уточнение соседей
//!
//! Ветвь знает, что разбираемое значение построено конструктором, и это видят
//! тип результата, тела клауз и типы **соседних** аргументов. Последнее ядру
//! напрямую не выразить: мотив связан с одним значением. Поэтому соседи, чьи
//! типы зависят от разбираемого, выносятся в тот же мотив телескопом `Pi`, а
//! разбор применяется обратно к ним - convoy-паттерн. Так пишется
//! `g : (b : Bool) -> If b -> Nat`, где индексов нет ни одного: в ветви `true`
//! второй аргумент получает тип `If true`.
//!
//! Цена - лишняя лямбда в ветви на каждого вынесенного соседа. Её знает
//! проверка тотальности ([`crate::total`]): размеры аргументов применения
//! доходят до этих лямбд, иначе рекурсия по уточнённому аргументу перестала бы
//! засчитываться.
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

use crate::check::{TypeError, instantiate_telescope, is_type};
use crate::ctx::{Binding, Ctx};
use crate::eval::quote;
use crate::level::Level;
use crate::meta::Metas;
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

    /// Тип определения не проходит проверку типов.
    ///
    /// Элаборация работает до [`crate::check`], поэтому проверяет тип сама:
    /// вычислять непроверенный терм нельзя. Сюда попадает и выход за пределы
    /// собственных аргументов - у отдельной проверки замкнутости после этого не
    /// осталось случая, в котором она могла бы сработать.
    #[error("тип определения не является типом: {error}")]
    IllTypedType {
        /// Что именно не сошлось.
        error: Box<TypeError>,
    },

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
/// Тип проверяется здесь же, до всякого вычисления. Элаборация работает **до**
/// [`crate::check`], а вычислять непроверенный терм нельзя: `eval` вправе
/// паниковать на незамкнутом или нетипизированном входе, и `compile` уносила бы
/// эту панику наружу как поведение публичной функции.
///
/// # Errors
///
/// Тип не является типом; несовпадение арности; чужой конструктор; семейство с
/// индексами; непокрытый случай; недостижимая клауза.
pub fn compile(
    signature: &Signature,
    metas: &mut Metas,
    ty: &Term,
    clauses: &[Clause],
) -> Result<Term, PatternError> {
    let ctx = Ctx::new(signature);
    is_type(&ctx, metas, ty).map_err(|error| PatternError::IllTypedType {
        error: Box::new(error),
    })?;

    let wanted = clauses
        .first()
        .map_or(usize::MAX, |clause| clause.patterns.len());

    // Телескоп аргументов: кратности и имена пойдут в лямбды, типы - в колонки.
    //
    // Снимается по значению, а не по терму: `def Fn = Nat -> Nat` - такой же
    // тип функции, как записанная стрелка, и синтаксическое снятие насчитало бы
    // ему нулевую арность, отвергнув клаузы с выдуманным числом аргументов.
    let mut ctx = ctx;
    let mut telescope = Vec::new();
    let mut current = ctx.eval(ty);
    while telescope.len() != wanted {
        let reduced = crate::conv::whnf(signature, &current);
        let Value::Pi(mult, name, domain, codomain) = &*reduced else {
            break;
        };
        let bound = Lvl(ctx.size());
        telescope.push((*mult, Rc::clone(name), Rc::clone(domain)));
        ctx = ctx.bind(Rc::clone(name), *mult, Rc::clone(domain));
        current = codomain.apply(Value::var(bound));
    }
    let arity = telescope.len();
    if !clauses.is_empty() && arity != wanted {
        return Err(PatternError::ClauseArity {
            clause: 0,
            expected: arity,
            found: wanted,
        });
    }
    // Читается обратно в контексте снятых связываний, поэтому указать вне их
    // уже некуда: отдельная проверка замкнутости здесь была бы недостижима, а
    // выход за контекст ловит `is_type` выше.
    let target = quote(ctx.size(), &current);

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

    /// Разбор по колонке `at`.
    fn split(
        &mut self,
        ctx: &Ctx<'_>,
        columns: &[Column],
        rows: &[Row],
        target: &Term,
        example: &[Pattern],
        at: usize,
    ) -> Result<Term, PatternError> {
        let family = self.family(ctx, &columns[at], rows, at)?;
        // Соседи, чьи типы зависят от разбираемого значения: мотив связан с
        // одним значением, поэтому уточнить их можно только вынеся в тот же
        // мотив и применив разбор обратно к ним.
        let plan = Split {
            columns,
            rows,
            target,
            example,
            column: at,
            carried: carried(ctx, columns, at),
        };

        let size = ctx.size();
        let motive = motive(ctx, plan.scrutinee(), &plan.borrowed(), target);
        let mut branches = Vec::with_capacity(family.constructors.len());
        for constructor in &family.constructors {
            branches.push(self.branch(ctx, &plan, &family, constructor)?);
        }

        let discriminated = Term::Case(Rc::new(Case {
            data: family.data,
            levels: family.levels,
            params: family.parameters,
            scrutinee: Rc::new(Term::Var(Lvl(plan.scrutinee().level).to_index(size))),
            motive: Rc::new(motive),
            branches,
        }));
        // Разбор применяется обратно к вынесенным соседям - к тем самым
        // переменным, с которых начинали: их старые связывания расходуются
        // здесь, а тела ветвей пользуются свежими.
        Ok(discriminated.apply(
            plan.borrowed()
                .iter()
                .map(|carried| Term::Var(Lvl(carried.level).to_index(size))),
        ))
    }

    /// Ветвь одного конструктора.
    fn branch(
        &mut self,
        ctx: &Ctx<'_>,
        plan: &Split<'_>,
        family: &Family,
        constructor: &Name,
    ) -> Result<Branch, PatternError> {
        let size = ctx.size();
        let fields = self.fields(ctx, constructor, &family.levels, &family.params);
        let mut inner = ctx.clone();
        for field in &fields {
            inner = inner.bind(Rc::clone(&field.name), field.mult, Rc::clone(&field.ty));
        }

        // В этой ветви разбираемое значение - не переменная, а построенное
        // конструктором, и увидеть это обязаны все: тип результата, типы
        // вынесенных соседей и тела клауз, связавшие аргумент переменной. Без
        // подстановки вложенный разбор строил бы мотив по неуточнённому типу
        // (`P n` против `P zero`), а тело ссылалось бы на исходный аргумент -
        // и тратило бы его второй раз после разбора.
        let base = inner.size();
        let built = fields.iter().fold(
            family.params.iter().fold(
                Term::Const(Rc::clone(constructor), Rc::clone(&family.levels)),
                |applied, param| Term::App(Rc::new(applied), Rc::new(quote(base, param))),
            ),
            |applied, field| {
                Term::App(
                    Rc::new(applied),
                    Rc::new(Term::Var(Lvl(field.level).to_index(base))),
                )
            },
        );
        let refined = inner.eval(&built);
        let refinement = plan.refinement(Bound::Built(Rc::clone(&refined)), base);

        // Свежие связывания соседей - уже с уточнёнными типами.
        let mut copies = Vec::with_capacity(plan.carried.len());
        for carried_column in plan.borrowed() {
            let at = inner.size();
            let binding = binding(ctx, carried_column.level);
            let domain = rewrite(
                &quote(size, &carried_column.ty),
                0,
                size,
                &refinement.at(at),
            );
            let ty = inner.eval(&domain);
            inner = inner.bind(Rc::clone(&binding.name), binding.mult, Rc::clone(&ty));
            copies.push((binding.mult, Rc::clone(&binding.name), ty));
        }

        let at = inner.size();
        let columns = plan.refined_columns(&fields, &copies, base);
        let rows = plan.refined_rows(&inner, &refinement, constructor, fields.len(), &refined)?;
        let example = plan.refined_example(constructor, fields.len());
        let target = rewrite(plan.target, 0, size, &refinement.at(at));

        let body = self.solve(&inner, &columns, &rows, &target, &example)?;
        let body = copies.iter().rev().fold(body, |body, (mult, name, _)| {
            Term::Lam(*mult, Rc::clone(name), Rc::new(body))
        });
        Ok(Branch {
            constructor: Rc::clone(constructor),
            body: Rc::new(fields.iter().rev().fold(body, |body, field| {
                Term::Lam(field.mult, Rc::clone(&field.name), Rc::new(body))
            })),
        })
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

/// Разбор одной колонки: то, что общее для всех её ветвей.
struct Split<'a> {
    columns: &'a [Column],
    rows: &'a [Row],
    target: &'a Term,
    example: &'a [Pattern],
    /// Номер разбираемой колонки.
    column: usize,
    /// Номера вынесенных в мотив колонок, в порядке контекста.
    carried: Vec<usize>,
}

impl Split<'_> {
    /// Разбираемая колонка.
    fn scrutinee(&self) -> &Column {
        &self.columns[self.column]
    }

    /// Вынесенные колонки.
    fn borrowed(&self) -> Vec<&Column> {
        self.carried
            .iter()
            .map(|index| &self.columns[*index])
            .collect()
    }

    /// Перенос в контекст ветви: копии соседей связываются подряд, начиная с
    /// `base`.
    fn refinement(&self, became: Bound, base: u32) -> Refinement {
        Refinement {
            scrutinee: self.scrutinee().level,
            became,
            carried: self
                .carried
                .iter()
                .enumerate()
                .map(|(position, index)| (self.columns[*index].level, base + arity_u32(position)))
                .collect(),
        }
    }

    /// Колонки ветви: разобранная заменяется своими полями, вынесенные -
    /// свежими копиями, прочие остаются как были.
    fn refined_columns(
        &self,
        fields: &[Field],
        copies: &[(Mult, Name, Rc<Value>)],
        base: u32,
    ) -> Vec<Column> {
        let mut refined = Vec::with_capacity(self.columns.len() + fields.len());
        for (index, column) in self.columns.iter().enumerate() {
            if index == self.column {
                for (position, field) in fields.iter().enumerate() {
                    let mut path = column.path.clone();
                    path.push(position);
                    refined.push(Column {
                        level: field.level,
                        path,
                        ty: Rc::clone(&field.ty),
                    });
                }
            } else if let Some(position) = self.carried.iter().position(|carried| *carried == index)
            {
                refined.push(Column {
                    level: base + arity_u32(position),
                    path: column.path.clone(),
                    ty: Rc::clone(&copies[position].2),
                });
            } else {
                refined.push(Column {
                    level: column.level,
                    path: column.path.clone(),
                    ty: Rc::clone(&column.ty),
                });
            }
        }
        refined
    }

    /// Строки ветви: подходящие клаузы с переехавшими связываниями.
    fn refined_rows(
        &self,
        inner: &Ctx<'_>,
        refinement: &Refinement,
        constructor: &Name,
        fields: usize,
        built: &Rc<Value>,
    ) -> Result<Vec<Row>, PatternError> {
        let at = inner.size();
        let mut refined = Vec::new();
        for row in self.rows {
            let Some(mut row) = specialise(row, self.column, constructor, fields, built)? else {
                continue;
            };
            // Связывания, сделанные разборами выше, переезжают вместе с
            // соседями: переменная клаузы, указывавшая на уточнённый аргумент,
            // обязана указать на его новую форму.
            for value in row.assigned.iter_mut().flatten() {
                *value = inner.eval(&rewrite(&quote(at, value), 0, at, &refinement.at(at)));
            }
            refined.push(row);
        }
        Ok(refined)
    }

    /// Пример непокрытого случая с подставленным конструктором.
    fn refined_example(&self, constructor: &Name, fields: usize) -> Vec<Pattern> {
        let mut example = self.example.to_vec();
        place(
            &mut example,
            &self.scrutinee().path,
            Pattern::Constructor(
                Rc::clone(constructor),
                vec![Pattern::Var("_".into()); fields],
            ),
        );
        example
    }
}

/// Чем стало разбираемое значение при переносе терма.
enum Bound {
    /// Переменной нового уровня - так его видит мотив.
    Variable(u32),
    /// Значением: в ветви оно уже построено конструктором.
    Built(Rc<Value>),
}

/// Перенос терма из контекста разбора в контекст мотива или ветви.
///
/// Меняются двое: разбираемое значение и вынесенные соседи, получившие новые
/// связывания. Всё прочее остаётся собой - меняется только пересчёт уровня в
/// индекс.
struct Refinement {
    /// Уровень разбираемой колонки.
    scrutinee: u32,
    /// Чем она стала.
    became: Bound,
    /// Пары "уровень соседа, уровень его нового связывания".
    carried: Vec<(u32, u32)>,
}

impl Refinement {
    /// Отображение уровня в терм, записанный в контексте размера `at`.
    fn at(&self, at: u32) -> impl Fn(u32) -> Term + '_ {
        move |level| {
            if level == self.scrutinee {
                return match &self.became {
                    Bound::Variable(bound) => Term::Var(Lvl(*bound).to_index(at)),
                    Bound::Built(value) => quote(at, value),
                };
            }
            match self.carried.iter().find(|(from, _)| *from == level) {
                Some((_, to)) => Term::Var(Lvl(*to).to_index(at)),
                None => Term::Var(Lvl(level).to_index(at)),
            }
        }
    }
}

/// Колонки, чьи типы зависят от разбираемого значения, в порядке контекста.
///
/// Замыкание транзитивно: если тип соседа зависит от **вынесенного** соседа,
/// он обязан переехать тоже, иначе останется указывать на старое, неуточнённое
/// связывание.
fn carried(ctx: &Ctx<'_>, columns: &[Column], split: usize) -> Vec<usize> {
    let size = ctx.size();
    let mut refined = vec![columns[split].level];
    let mut chosen: Vec<usize> = Vec::new();
    let mut grown = true;
    while grown {
        grown = false;
        for (index, column) in columns.iter().enumerate() {
            if index == split || chosen.contains(&index) {
                continue;
            }
            if depends(size, &column.ty, &refined) {
                chosen.push(index);
                refined.push(column.level);
                grown = true;
            }
        }
    }
    // Порядок колонок - порядок сопоставления, а связывания идут в порядке
    // контекста: разбор колонки вставляет её поля в середину списка.
    chosen.sort_by_key(|index| columns[*index].level);
    chosen
}

/// Упоминает ли тип хоть один из уровней.
///
/// Считается по нормальной форме: `(\_ -> Nat) b` от `b` не зависит, и
/// уточнять там нечего.
fn depends(size: u32, ty: &Rc<Value>, levels: &[u32]) -> bool {
    fn go(term: &Term, depth: u32, size: u32, levels: &[u32]) -> bool {
        let recur = |inner: &Rc<Term>| go(inner, depth, size, levels);
        let under = |inner: &Rc<Term>| go(inner, depth + 1, size, levels);
        match term {
            Term::Var(Index(index)) => {
                *index >= depth && levels.contains(&(size + depth - 1 - index))
            }
            Term::Universe(_) | Term::Const(..) => false,
            Term::Lam(_, _, body) => under(body),
            Term::App(callee, argument) => recur(callee) || recur(argument),
            Term::Pi(_, _, domain, codomain) => recur(domain) || under(codomain),
            Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || under(body),
            Term::Case(case) => {
                recur(&case.scrutinee)
                    || recur(&case.motive)
                    || case.branches.iter().any(|branch| recur(&branch.body))
            }
        }
    }
    go(&quote(size, ty), 0, size, levels)
}

/// Мотив разбора: `\(0 x) -> Pi <вынесенные соседи>. <тип результата>`.
///
/// Соседи стоят телескопом внутри мотива, поэтому в каждой ветви их типы
/// уточняются вместе с разбираемым значением. Разбор возвращает функцию от
/// них, и вызывающий применяет её обратно - см. [`Compiler::split`].
fn motive(ctx: &Ctx<'_>, column: &Column, carried: &[&Column], target: &Term) -> Term {
    let size = ctx.size();
    let refinement = Refinement {
        scrutinee: column.level,
        became: Bound::Variable(size),
        carried: carried
            .iter()
            .enumerate()
            .map(|(position, carried)| (carried.level, size + 1 + arity_u32(position)))
            .collect(),
    };

    let mut inner = ctx.bind("x".into(), Mult::Zero, Rc::clone(&column.ty));
    let mut domains = Vec::with_capacity(carried.len());
    for carried_column in carried {
        let at = inner.size();
        let binding = binding(ctx, carried_column.level);
        let domain = rewrite(
            &quote(size, &carried_column.ty),
            0,
            size,
            &refinement.at(at),
        );
        let ty = inner.eval(&domain);
        inner = inner.bind(Rc::clone(&binding.name), binding.mult, ty);
        domains.push((binding.mult, Rc::clone(&binding.name), domain));
    }

    let result = rewrite(target, 0, size, &refinement.at(inner.size()));
    let body = domains
        .into_iter()
        .rev()
        .fold(result, |codomain, (mult, name, domain)| {
            Term::Pi(mult, name, Rc::new(domain), Rc::new(codomain))
        });
    Term::Lam(Mult::Zero, "x".into(), Rc::new(body))
}

/// Запись контекста по уровню.
fn binding<'a>(ctx: &'a Ctx<'_>, level: u32) -> &'a Binding {
    ctx.lookup(Lvl(level).to_index(ctx.size()))
        .unwrap_or_else(|| unreachable!("уровень {level} вне контекста"))
}

/// Индуктивное семейство в голове типа: имя, аргументы уровня и параметры.
type DataHead = (Name, Rc<[Level]>, Vec<Rc<Value>>);

/// Индуктивное семейство в голове типа, вместе с аргументами.
///
/// δ-разворот обязателен: у определения-синонима голова своя. Разворотом
/// заведует [`crate::conv::whnf`] - вместе с ним приходит предел, которого у
/// собственного цикла здесь не было.
fn data_head(signature: &Signature, ty: &Rc<Value>) -> Option<DataHead> {
    let reduced = crate::conv::whnf(signature, ty);
    let Value::Neutral(Head::Global(name, levels), spine) = &*reduced else {
        return None;
    };
    if !matches!(
        signature.lookup(name).map(|found| &found.kind),
        Some(DefinitionKind::Data { .. })
    ) {
        return None;
    }
    let arguments = spine
        .iter()
        .map(|elim| match elim {
            Elim::App(argument) => Some(Rc::clone(argument)),
            Elim::Case(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((Rc::clone(name), Rc::clone(levels), arguments))
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

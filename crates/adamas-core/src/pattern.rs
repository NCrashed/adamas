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
//! # Индексы
//!
//! Индексы разбираемого значения сопоставляются с индексами каждого
//! конструктора ([`crate::unify`]), и оба возможных ответа реализует один и тот
//! же механизм - **разбор индекса внутри мотива**. Совпавший путь даёт цель,
//! все прочие - `(1 _ : G) -> G`, который населяет тождество. Отсюда сразу и
//! уточнение (`tail (vcons k x xs)` имеет тип `Vect A k`, потому что связывание
//! разбора и есть то, чем оказалась переменная индекса), и дизъюнктность
//! (ветви `vnil` у `head : Vect A (succ n) -> A` не бывает, и населять её
//! незачем).
//!
//! Различается не всякая позиция: только та, по которой конструкторы
//! расходятся или чьи переменные встречаются в цели. Иначе мотив по ней
//! постоянен - разбор ничего не дал бы, а требовать конструкторной формы от
//! каждого конструктора значило бы отвергать программы зря.
//!
//! Уточнённая переменная перестаёт быть переменной: `n` в ветви `vcons` есть
//! `succ k`, поэтому колонка несёт значение, а не уровень, и разбор по
//! известному конструктору идёт без узла вовсе.

use std::fmt;
use std::rc::Rc;

use crate::check::{Frame, TypeError, instantiate_telescope, is_type};
use crate::ctx::{Binding, Ctx};
use crate::eval::quote;
use crate::level::Level;
use crate::meta::Metas;
use crate::mult::Mult;
// Строка задачи разбора тоже зовётся `Row`, поэтому row эффектов приходит
// сюда под своим полным смыслом в имени.
use crate::row::Row as EffectRow;
use crate::sig::{DefinitionKind, Signature};
use crate::term::{Binder, Branch, Case, Field as RecordField, Fields, Index, Name, Rows, Term};
use crate::unify::{self, Match, Shape};
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

    /// Клауза разбирает случай, которого не бывает.
    ///
    /// Не то же, что недостижимая клауза: ту перекрывают предыдущие, а эта не
    /// сработала бы и в одиночестве - индексы не сходятся.
    #[error(
        "клауза #{clause}: `{constructor}` здесь невозможен - индекс требует `{expected}`, а конструктор даёт `{found}`"
    )]
    ImpossiblePattern {
        /// Номер клаузы.
        clause: usize,
        /// Конструктор из паттерна.
        constructor: Name,
        /// Чего требует индекс разбираемого значения.
        expected: Name,
        /// Что даёт конструктор.
        found: Name,
    },

    /// Индекс конструктора не приводится к форме индекса разбираемого
    /// значения - см. [`crate::unify`].
    #[error(
        "конструктор `{constructor}`: индекс `{found}` не приведён к `{expected}`, унифицировать нечем"
    )]
    StuckIndex {
        /// Конструктор, ветвь которого не строится.
        constructor: Name,
        /// Конструктор, которого требует разбираемое значение.
        expected: Name,
        /// Что стоит вместо него.
        found: String,
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
    Ok(compile_traced(signature, metas, ty, clauses)?.term)
}

/// То же, но вместе с тем, куда в дереве попали клаузы.
///
/// Дерево - структура, которую элаборация порождает сама, и ошибка ядра
/// приходит про терм, которого автор не писал (§10 вопрос 49б). Маршрут ядра
/// проходит по дереву, а `clauses` переводит его пройденную часть обратно в
/// номер клаузы - дальше маршрут продолжается уже по её телу.
///
/// # Errors
///
/// То же, что у [`compile`].
pub fn compile_traced(
    signature: &Signature,
    metas: &mut Metas,
    ty: &Term,
    clauses: &[Clause],
) -> Result<Compiled, PatternError> {
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
        let Value::Pi(Binder { mult, .. }, name, domain, _, codomain) = &*reduced else {
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
            value: Value::var(Lvl(arity_u32(index))),
            path: vec![index],
            ty: Rc::clone(domain),
        })
        .collect();
    let example = vec![Pattern::Var("_".into()); arity];

    let mut compiler = Compiler {
        signature,
        metas,
        base: 0,
        used: vec![false; clauses.len()],
    };
    let tree = compiler.solve(&ctx, &columns, &rows, &target, &example)?;
    if let Some(clause) = compiler.used.iter().position(|used| !used) {
        return Err(PatternError::UnreachableClause { clause });
    }

    // Лямбды аргументов - те же кадры `Body`, что и всякая другая лямбда.
    //
    // Имя берётся у клауз, а из типа - только когда его там нет: связывание
    // называет автор, и `f (Succ k) m = …` в диагностике должно говорить `m`,
    // а не имя одноимённого `Pi`, которого в безымянной стрелке и нет вовсе.
    let tree =
        telescope
            .into_iter()
            .enumerate()
            .rev()
            .fold(tree, |tree, (index, (mult, name, _))| {
                let name = written(clauses, index).unwrap_or(name);
                tree.map(|body| Term::Lam(mult, name, Rc::new(body)))
                    .under(Frame::Body)
            });
    Ok(Compiled {
        term: tree.term,
        clauses: tree.sites,
    })
}

/// Разбор по связыванию, уже стоящему в контексте, - `case` выражением (§4.1).
///
/// Отличается от [`compile_traced`] тем, что колонка одна, стоит она в
/// переданном контексте, и лямбд вокруг дерева нет: тела ветвей живут под тем
/// же контекстом, что и сам разбор.
///
/// Поднимать контекст в аргументы, как делала первая форма, значит применять
/// разбор к нему целиком, а применение расходует **всякое** `1`-связывание -
/// включая те, которых ни одна ветвь не называет. Отсюда и четыре расхождения
/// с §3.3 и §4.7, разобранные в §10 вопросе 82.
///
/// # Errors
///
/// То же, что у [`compile_traced`], плюс `ClauseArity`, если в клаузе не ровно
/// один паттерн.
pub fn compile_case(
    ctx: &Ctx<'_>,
    metas: &mut Metas,
    scrutinee: Lvl,
    target: &Term,
    clauses: &[Clause],
) -> Result<Compiled, PatternError> {
    let base = ctx.size();
    let Lvl(level) = scrutinee;
    let ty = Rc::clone(&binding(ctx, level).ty);
    let mut rows = Vec::with_capacity(clauses.len());
    for (index, clause) in clauses.iter().enumerate() {
        if clause.patterns.len() != 1 {
            return Err(PatternError::ClauseArity {
                clause: index,
                expected: 1,
                found: clause.patterns.len(),
            });
        }
        let mut variables = 0;
        let patterns = clause
            .patterns
            .iter()
            .map(|pattern| number(pattern, &mut variables))
            .collect();
        // Связывания контекста телу законны: оно и написано под ними.
        if !well_scoped(&clause.body, base + arity_u32(variables)) {
            return Err(PatternError::UnboundInBody { clause: index });
        }
        rows.push(Row {
            clause: index,
            patterns,
            assigned: vec![None; variables],
            body: Rc::new(clause.body.clone()),
        });
    }
    let columns = vec![Column {
        value: Value::var(scrutinee),
        path: vec![0],
        ty,
    }];
    let example = vec![Pattern::Var("_".into())];
    let mut compiler = Compiler {
        signature: ctx.signature(),
        metas,
        base,
        used: vec![false; clauses.len()],
    };
    let tree = compiler.solve(ctx, &columns, &rows, target, &example)?;
    if let Some(clause) = compiler.used.iter().position(|used| !used) {
        return Err(PatternError::UnreachableClause { clause });
    }
    Ok(Compiled {
        term: tree.term,
        clauses: tree.sites,
    })
}

/// Как автор назвал `index`-й аргумент.
///
/// Первая клауза, где на этом месте стоит переменная: разбор имени не даёт, а
/// `_` не называет. Клаузы, назвавшие один аргумент по-разному, - обычное
/// дело, и берётся первое: имя нужно диагностике, а не проверке.
fn written(clauses: &[Clause], index: usize) -> Option<Name> {
    clauses
        .iter()
        .find_map(|clause| match clause.patterns.get(index) {
            Some(Pattern::Var(name)) if &**name != "_" => Some(Rc::clone(name)),
            _ => None,
        })
}

/// Клауза, разбирающая невозможный случай, - ошибка на месте, а не
/// недостижимость: перекрывать её нечему, она попросту не сработала бы.
fn impossible(
    rows: &[Row],
    at: usize,
    family: &Family,
    candidates: &[Candidate],
) -> Result<(), PatternError> {
    for row in rows {
        let Pat::Ctor(name, _) = &row.patterns[at] else {
            continue;
        };
        let Some(position) = family.constructors.iter().position(|found| found == name) else {
            continue;
        };
        if let Match::Conflict {
            expected, found, ..
        } = &candidates[position].outcome
        {
            return Err(PatternError::ImpossiblePattern {
                clause: row.clause,
                constructor: Rc::clone(name),
                expected: Rc::clone(expected),
                found: Rc::clone(found),
            });
        }
    }
    Ok(())
}

/// Дерево разбора вместе с тем, куда в нём попали клаузы.
#[derive(Clone, Debug)]
pub struct Compiled {
    /// Само дерево.
    pub term: Term,
    /// Места клауз в дереве. Одна клауза бывает здесь **несколько раз**:
    /// переменная-паттерн подходит под каждый конструктор, и тело копируется
    /// в каждую ветвь.
    pub clauses: Vec<ClauseSite>,
}

impl Compiled {
    /// Номер клаузы, в тело которой ведёт маршрут, и остаток маршрута внутри
    /// неё.
    ///
    /// Выбирается **самый длинный** подходящий префикс: пути к разным копиям
    /// одной клаузы различаются только хвостом, и короткий префикс поймал бы
    /// чужую ветвь.
    #[must_use]
    pub fn locate<'a>(&self, route: &'a [Frame]) -> Option<(usize, &'a [Frame])> {
        let reached = self
            .clauses
            .iter()
            .filter(|site| route.starts_with(&site.route))
            .max_by_key(|site| site.route.len())
            .map(|site| (site.clause, &route[site.route.len()..]));
        if reached.is_some() {
            return reached;
        }

        // Маршрут **короче** записанного пути: отказ случился не внутри тела
        // клаузы, а на узле, который его несёт, - так выходит `UsageViolation`,
        // возбуждаемая при выходе из связывания, а не под ним. Клауза при этом
        // может быть уже определена: если пройденный отрезок ведёт к одной, ею
        // и отвечаем, показывая тело целиком.
        //
        // Несколько клауз за одним отрезком - не неудача, а честная
        // неоднозначность: ветвь обслуживает их все, и выбрать одну не из чего.
        let mut only = None;
        for site in self
            .clauses
            .iter()
            .filter(|site| site.route.starts_with(route))
        {
            match only {
                None => only = Some(site.clause),
                Some(clause) if clause == site.clause => {}
                Some(_) => return None,
            }
        }
        only.map(|clause| (clause, &route[route.len()..]))
    }
}

/// Тело клаузы в собранном дереве.
#[derive(Clone, Debug)]
pub struct ClauseSite {
    /// Номер клаузы в порядке написания.
    pub clause: usize,
    /// Маршрут от корня дерева **снаружи внутрь** - в том порядке, в каком
    /// его отдаёт [`TypeError::path`](crate::check::TypeError::path).
    pub route: Vec<Frame>,
}

/// Собираемое дерево вместе с местами клауз в нём.
///
/// Кадр дописывает тот, кто узел строит: обернул лямбдой - дописал `Body`,
/// положил в ветвь - дописал `Branch`. Соответствие поэтому не может
/// разъехаться с деревом - оно строится тем же кодом и в тот же момент.
struct Tree {
    term: Term,
    sites: Vec<ClauseSite>,
}

impl Tree {
    /// Тело клаузы целиком.
    fn leaf(term: Term, clause: usize) -> Self {
        Self {
            term,
            sites: vec![ClauseSite {
                clause,
                route: Vec::new(),
            }],
        }
    }

    /// Оборачивает дерево узлом, в котором оно стоит на месте `frame`.
    fn under(mut self, frame: Frame) -> Self {
        for site in &mut self.sites {
            site.route.insert(0, frame);
        }
        self
    }

    /// Меняет терм, не трогая места клауз: узел добавлен снаружи и кадр
    /// дописывается отдельным [`Tree::under`].
    fn map(mut self, build: impl FnOnce(Term) -> Term) -> Self {
        self.term = build(self.term);
        self
    }
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
    /// Само значение. Обычно переменная, но уточнение индекса делает его
    /// конструктором: `n` в ветви `vcons` - это `succ k`, и разбирать там уже
    /// нечего, выбор известен.
    value: Rc<Value>,
    /// Путь до неё в исходных аргументах: номер аргумента, потом номера полей.
    /// Нужен только для примера непокрытого случая.
    path: Vec<usize>,
    /// Тип значения.
    ty: Rc<Value>,
}

impl Column {
    /// Уровень связывания, если значение - переменная.
    fn level(&self) -> Option<u32> {
        match &*self.value {
            Value::Neutral(Head::Local(Lvl(level)), spine) if spine.is_empty() => Some(*level),
            _ => None,
        }
    }

    /// То же там, где переменность уже установлена.
    fn bound(&self) -> u32 {
        self.level()
            .unwrap_or_else(|| unreachable!("колонка не переменная"))
    }
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
    /// Нужны для уровня универсума цели: мотив, различающий индексы, пишет
    /// `Type ℓ` руками, а `ℓ` спрашивают у проверки типов.
    metas: &'a mut Metas,
    /// Сколько связываний контекста стоит **до** колонок.
    ///
    /// У клауз ноль: тело живёт под одними аргументами. У `case` выражением -
    /// размер контекста, в котором он написан: тело ветви законно называет
    /// всё, что там связано, и переписывать эти переменные значениями колонок
    /// нельзя - они не колонки.
    base: u32,
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
    ) -> Result<Tree, PatternError> {
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

        match columns[split].level() {
            Some(_) => self.split(ctx, columns, rows, target, example, split),
            // Значение уже построено конструктором: узел разбора не нужен,
            // потому что выбирать не из чего.
            None => self.known(ctx, columns, rows, target, example, split),
        }
    }

    /// Первая колонка-переменная, тип которой - семейство без конструкторов.
    fn empty_column(&self, columns: &[Column]) -> Option<usize> {
        columns.iter().position(|column| {
            column.level().is_some()
                && data_head(self.signature, &column.ty).is_some_and(|(data, ..)| {
                    matches!(
                        self.signature.lookup(&data).map(|found| &found.kind),
                        Some(DefinitionKind::Data { constructors, .. }) if constructors.is_empty()
                    )
                })
        })
    }

    /// Тело клаузы, переписанное в текущий контекст.
    fn leaf(&mut self, ctx: &Ctx<'_>, columns: &[Column], row: &Row) -> Tree {
        self.used[row.clause] = true;
        let mut assigned = row.assigned.clone();
        for (column, pattern) in columns.iter().zip(&row.patterns) {
            if let Pat::Var(variable) = pattern {
                assigned[*variable] = Some(Rc::clone(&column.value));
            }
        }
        let bound = arity_u32(assigned.len());
        let size = ctx.size();
        // Свободные переменные тела нумеруются одним рядом: сперва связывания
        // контекста, потом переменные клаузы. Первые остаются собой - меняется
        // только глубина, на которой они стоят, - вторые заменяются значениями
        // колонок.
        let base = self.base;
        let body = rewrite(&row.body, 0, base + bound, &|level| {
            if level < base {
                return Term::Var(Lvl(level).to_index(size));
            }
            let value = assigned[(level - base) as usize]
                .as_ref()
                .unwrap_or_else(|| unreachable!("переменная клаузы осталась несвязанной"));
            quote(size, value)
        });
        Tree::leaf(body, row.clause)
    }

    /// Колонка, значение которой уже построено конструктором.
    ///
    /// Узел разбора не нужен: выбирать не из чего. Так выходит после уточнения
    /// индекса - `n` в ветви `vcons` есть `succ k`, - и клаузы отбираются по
    /// известному конструктору на месте.
    fn known(
        &mut self,
        ctx: &Ctx<'_>,
        columns: &[Column],
        rows: &[Row],
        target: &Term,
        example: &[Pattern],
        at: usize,
    ) -> Result<Tree, PatternError> {
        let column = &columns[at];
        let family = self.family(ctx, column, rows, at)?;
        let unmatchable = || PatternError::NotMatchable {
            ty: ctx.quote(&column.ty).to_string(),
        };
        let Some((constructor, levels, arguments)) =
            constructor_value(self.signature, &column.value)
        else {
            return Err(unmatchable());
        };
        if !family.constructors.contains(&constructor) {
            return Err(PatternError::ForeignConstructor {
                constructor,
                data: family.data,
            });
        }
        let parameters = family.parameters as usize;
        if arguments.len() < parameters {
            return Err(unmatchable());
        }
        let fields = self.applied_fields(&constructor, &levels, &arguments, parameters);

        let mut inner_columns = Vec::with_capacity(columns.len() + fields.len());
        for (index, other) in columns.iter().enumerate() {
            if index == at {
                for (position, (value, ty)) in fields.iter().enumerate() {
                    let mut path = column.path.clone();
                    path.push(position);
                    inner_columns.push(Column {
                        value: Rc::clone(value),
                        path,
                        ty: Rc::clone(ty),
                    });
                }
            } else {
                inner_columns.push(Column {
                    value: Rc::clone(&other.value),
                    path: other.path.clone(),
                    ty: Rc::clone(&other.ty),
                });
            }
        }

        let mut inner_rows = Vec::new();
        for row in rows {
            if let Some(row) = specialise(row, at, &constructor, fields.len(), &column.value)? {
                inner_rows.push(row);
            }
        }

        let mut inner_example = example.to_vec();
        place(
            &mut inner_example,
            &column.path,
            Pattern::Constructor(
                Rc::clone(&constructor),
                vec![Pattern::Var("_".into()); fields.len()],
            ),
        );

        self.solve(ctx, &inner_columns, &inner_rows, target, &inner_example)
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
    ) -> Result<Tree, PatternError> {
        let family = self.family(ctx, &columns[at], rows, at)?;
        let Some(scrutinee) = columns[at].level() else {
            unreachable!("разбор идёт только по переменной")
        };
        let size = ctx.size();
        // `r` берётся у связывания разбираемого (§3.3). `0` до узла не
        // доходит: `case⁰` ядро отвергает, а линейное потребление стёртого
        // связывания отвергает учёт использований - там же, но с сообщением
        // про само связывание, которое и есть ошибка автора.
        let consumed = match binding(ctx, scrutinee).mult {
            Mult::Many => Mult::Many,
            Mult::One | Mult::Zero => Mult::One,
        };

        // Ветви до сборки: поля конструктора и вердикт унификации его индексов
        // с индексами разбираемого значения.
        let mut candidates = Vec::with_capacity(family.constructors.len());
        for constructor in &family.constructors {
            let (fields, result) = self.fields(ctx, constructor, &family.levels, &family.params);
            let indices = family
                .branch_indices(self.signature, &result)
                .unwrap_or_default();
            let outcome = unify::matches(self.signature, &family.shapes, &indices);
            candidates.push(Candidate {
                fields,
                indices,
                outcome,
            });
        }

        // Уточняется разбираемое значение и переменные, стоящие в его
        // индексах. Соседи, чьи типы от них зависят, выносятся в мотив: ядро
        // связывает мотив с одним значением, и второго места, где их можно
        // уточнить, нет.
        let mut refined = vec![scrutinee];
        for shape in &family.shapes {
            shape.variables(&mut refined);
        }
        let carried = carried(ctx, columns, &refined);
        let borrowed: Vec<&Column> = carried.iter().map(|index| &columns[*index]).collect();
        let unrefined = goal(ctx, &borrowed, target, size, &[]);

        let shapes = discriminated(&family.shapes, &candidates, size, &unrefined);
        for (constructor, candidate) in family.constructors.iter().zip(&mut candidates) {
            candidate.outcome = unify::matches(self.signature, &shapes, &candidate.indices);
            if let Match::Stuck { expected, found } = &candidate.outcome {
                // Индекс записан в контексте ветви - там же, где связаны поля.
                let at = size + arity_u32(candidate.fields.len());
                return Err(PatternError::StuckIndex {
                    constructor: Rc::clone(constructor),
                    expected: Rc::clone(expected),
                    found: quote(at, found).to_string(),
                });
            }
        }

        impossible(rows, at, &family, &candidates)?;

        // Уровень цели нужен только различающему мотиву - он пишет `Type ℓ`
        // руками, - и спрашивается у проверки типов, а не выдумывается свежей
        // дыркой: дырка из чужого хранилища доехала бы до сохранённого
        // определения (§10 вопрос 51). Решённые подставляются здесь же.
        let sort = if shapes.iter().any(Shape::is_rigid) {
            let level = is_type(ctx, self.metas, &unrefined).map_err(|error| {
                PatternError::IllTypedType {
                    error: Box::new(error),
                }
            })?;
            Some(self.metas.zonk(&level))
        } else {
            None
        };

        let plan = Split {
            columns,
            rows,
            target,
            example,
            column: at,
            scrutinee,
            consumed,
            carried,
            shapes,
        };
        let motive = self.motive(ctx, &plan, &family, sort.as_ref());
        let mut branches = Vec::with_capacity(family.constructors.len());
        let mut sites = Vec::new();
        for (index, (constructor, candidate)) in
            family.constructors.iter().zip(&candidates).enumerate()
        {
            let (branch, inner) = self.branch(ctx, &plan, &family, constructor, candidate)?;
            branches.push(branch);
            let slot = Frame::Branch(arity_u32(index));
            sites.extend(inner.into_iter().map(|mut site| {
                site.route.insert(0, slot);
                site
            }));
        }

        let discriminated = Term::Case(Rc::new(Case {
            data: Rc::clone(&family.data),
            levels: Rc::clone(&family.levels),
            params: family.parameters,
            consumed,
            scrutinee: Rc::new(Term::Var(Lvl(scrutinee).to_index(size))),
            motive: Rc::new(motive),
            branches,
        }));
        // Разбор применяется обратно к вынесенным соседям - к тем самым
        // переменным, с которых начинали: их старые связывания расходуются
        // здесь, а тела ветвей пользуются свежими.
        //
        // Узел разбора уезжает при этом внутрь применений, и маршрут к нему
        // идёт через `Callee` - по кадру на вынесенного соседа.
        let tree = Tree {
            term: discriminated,
            sites,
        };
        Ok(plan.borrowed().iter().fold(tree, |tree, carried| {
            let argument = Term::Var(Lvl(carried.bound()).to_index(size));
            tree.map(|callee| callee.apply([argument]))
                .under(Frame::Callee)
        }))
    }

    /// Ветвь одного конструктора.
    fn branch(
        &mut self,
        ctx: &Ctx<'_>,
        plan: &Split<'_>,
        family: &Family,
        constructor: &Name,
        candidate: &Candidate,
    ) -> Result<(Branch, Vec<ClauseSite>), PatternError> {
        let size = ctx.size();
        let fields = &candidate.fields;
        // Поле приходит в ветвь при `q · r` (§3.3), и так же его обязаны
        // видеть все трое: связывание в контексте, лямбда в терме и тип
        // ветви, который построит `check`. Разойдись они - `LambdaMultiplicity`
        // на терме, который сборка же и собрала.
        let taken = |field: &Field| field.mult * plan.consumed;
        let mut inner = ctx.clone();
        for field in fields {
            inner = inner.bind(Rc::clone(&field.name), taken(field), Rc::clone(&field.ty));
        }
        let wrap = |body: Term| {
            fields.iter().rev().fold(body, |body, field| {
                Term::Lam(taken(field), Rc::clone(&field.name), Rc::new(body))
            })
        };

        // Индексы разошлись - такой ветви не бывает. Мотив отдал ей заведомо
        // обитаемый `(1 _ : G) -> G`, и населяет его тождество.
        let Match::Solved(solved) = &candidate.outcome else {
            return Ok((
                Branch {
                    constructor: Rc::clone(constructor),
                    body: Rc::new(wrap(Term::Lam(
                        Mult::One,
                        "z".into(),
                        Rc::new(Term::var(0)),
                    ))),
                },
                Vec::new(),
            ));
        };

        // В этой ветви разбираемое значение - не переменная, а построенное
        // конструктором, и увидеть это обязаны все: тип результата, типы
        // вынесенных соседей и тела клауз, связавшие аргумент переменной. Без
        // подстановки вложенный разбор строил бы мотив по неуточнённому типу
        // (`P n` против `P zero`), а тело ссылалось бы на исходный аргумент -
        // и тратило бы его второй раз после разбора.
        let base = inner.size();
        let built = fields.iter().fold(
            family.params.iter().fold(
                Term::Const(
                    Rc::clone(constructor),
                    Rc::clone(&family.levels),
                    Rows::none(),
                ),
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
        let refinement = plan.refinement(&refined, solved, base);

        // Свежие связывания соседей - уже с уточнёнными типами.
        let mut copies = Vec::with_capacity(plan.carried.len());
        for carried_column in plan.borrowed() {
            let at = inner.size();
            let binding = binding(ctx, carried_column.bound());
            let (mult, name) = (binding.mult, Rc::clone(&binding.name));
            let domain = rewrite(
                &quote(size, &carried_column.ty),
                0,
                size,
                &refinement.at(at),
            );
            let ty = inner.eval(&domain);
            inner = inner.bind(Rc::clone(&name), mult, Rc::clone(&ty));
            copies.push((mult, name, ty));
        }

        let at = inner.size();
        let columns = plan.refined_columns(&inner, &refinement, fields, &copies, base);
        let rows = plan.refined_rows(&inner, &refinement, constructor, fields.len(), &refined)?;
        let example = plan.refined_example(constructor, fields.len());
        let target = rewrite(plan.target, 0, size, &refinement.at(at));

        let body = self.solve(&inner, &columns, &rows, &target, &example)?;
        let body = copies.iter().rev().fold(body, |body, (mult, name, _)| {
            body.map(|body| Term::Lam(*mult, Rc::clone(name), Rc::new(body)))
                .under(Frame::Body)
        });
        // `wrap` кладёт по лямбде на каждое поле - столько же кадров `Body`.
        let body = fields
            .iter()
            .fold(body, |body, _| body.under(Frame::Body))
            .map(wrap);
        Ok((
            Branch {
                constructor: Rc::clone(constructor),
                body: Rc::new(body.term),
            },
            body.sites,
        ))
    }

    /// Мотив разбора: `\(0 i⃗) (0 x) -> <цель, уточнённая по индексам>`.
    fn motive(
        &self,
        ctx: &Ctx<'_>,
        plan: &Split<'_>,
        family: &Family,
        sort: Option<&Level>,
    ) -> Term {
        let size = ctx.size();
        let Some(declaration) = self.signature.lookup(&family.data) else {
            unreachable!("тип `{}` объявлен", family.data)
        };

        // Связывания мотива: индексы семейства, потом само разбираемое
        // значение. Формы индексов идут с ними парой - по ним и различается.
        let mut current = instantiate_telescope(
            declaration.instantiate_type(&family.levels, &[]),
            &family.params,
        );
        let mut inner = ctx.clone();
        let mut names = Vec::new();
        let mut work = Vec::new();
        while let Value::Pi(Binder { .. }, name, domain, _, codomain) = &*current {
            let level = inner.size();
            let next = codomain.apply(Value::var(Lvl(level)));
            inner = inner.bind(Rc::clone(name), Mult::Zero, Rc::clone(domain));
            work.push((
                level,
                plan.shapes
                    .get(names.len())
                    .cloned()
                    .unwrap_or(Shape::Opaque),
            ));
            names.push(Rc::clone(name));
            current = next;
        }

        let mut scrutinee = Term::Const(
            Rc::clone(&family.data),
            Rc::clone(&family.levels),
            Rows::none(),
        );
        for param in &family.params {
            scrutinee = Term::App(Rc::new(scrutinee), Rc::new(quote(inner.size(), param)));
        }
        for (level, _) in &work {
            scrutinee = Term::App(
                Rc::new(scrutinee),
                Rc::new(Term::Var(Lvl(*level).to_index(inner.size()))),
            );
        }
        let bound = inner.size();
        let ty = inner.eval(&scrutinee);
        let inner = inner.bind("x".into(), Mult::Zero, ty);

        let body = self.discriminate(&inner, plan, size, &work, &[(plan.scrutinee, bound)], sort);
        let body = Term::Lam(Mult::Zero, "x".into(), Rc::new(body));
        names.into_iter().rev().fold(body, |body, name| {
            Term::Lam(Mult::Zero, name, Rc::new(body))
        })
    }

    /// Тело мотива: разбор индексов по форме индексов разбираемого значения.
    ///
    /// Совпавший путь даёт цель, все прочие - заведомо обитаемый тип: ветвей по
    /// ним не бывает, и населять их будет тождество. Так одним механизмом
    /// получаются оба ответа унификации: конфликт даёт невозможную ветвь,
    /// совпадение - подстановку, потому что связывание разбора и есть то, чем
    /// оказалась переменная формы.
    fn discriminate(
        &self,
        ctx: &Ctx<'_>,
        plan: &Split<'_>,
        size: u32,
        work: &[(u32, Shape)],
        solved: &[(u32, u32)],
        sort: Option<&Level>,
    ) -> Term {
        let Some(((level, shape), rest)) = work.split_first() else {
            return goal(ctx, &plan.borrowed(), plan.target, size, solved);
        };
        let skip = || self.discriminate(ctx, plan, size, rest, solved, sort);
        match shape {
            Shape::Opaque => skip(),
            Shape::Variable(variable) => {
                let mut solved = solved.to_vec();
                solved.push((*variable, *level));
                self.discriminate(ctx, plan, size, rest, &solved, sort)
            }
            Shape::Constructor(name, shapes) => {
                let (Some(sort), Some((data, levels, arguments))) = (
                    sort,
                    data_head(self.signature, &Rc::clone(&binding(ctx, *level).ty)),
                ) else {
                    return skip();
                };
                let Some(declaration) = self.signature.lookup(&data) else {
                    return skip();
                };
                let DefinitionKind::Data {
                    constructors,
                    params,
                    ..
                } = &declaration.kind
                else {
                    return skip();
                };
                let parameters = *params as usize;
                if arguments.len() != binders(&declaration.ty) {
                    return skip();
                }

                // Мотив внутреннего разбора постоянен: он лишь говорит, что
                // результат - тип, и в каком универсуме.
                let arity = arguments.len() - parameters + 1;
                let inner_motive = (0..arity).fold(Term::Universe(sort.clone()), |body, _| {
                    Term::Lam(Mult::Zero, "_".into(), Rc::new(body))
                });

                let constructors = constructors.clone();
                let mut branches = Vec::with_capacity(constructors.len());
                for candidate in &constructors {
                    let (fields, _) =
                        self.fields(ctx, candidate, &levels, &arguments[..parameters]);
                    let mut inner = ctx.clone();
                    for field in &fields {
                        inner =
                            inner.bind(Rc::clone(&field.name), field.mult, Rc::clone(&field.ty));
                    }
                    let body = if candidate == name {
                        let mut deeper: Vec<(u32, Shape)> = fields
                            .iter()
                            .zip(shapes)
                            .map(|(field, shape)| (field.level, shape.clone()))
                            .collect();
                        deeper.extend_from_slice(rest);
                        self.discriminate(&inner, plan, size, &deeper, solved, Some(sort))
                    } else {
                        trivial(&inner, plan, size, solved)
                    };
                    branches.push(Branch {
                        constructor: Rc::clone(candidate),
                        body: Rc::new(fields.iter().rev().fold(body, |body, field| {
                            Term::Lam(field.mult, Rc::clone(&field.name), Rc::new(body))
                        })),
                    });
                }

                Term::Case(Rc::new(Case {
                    data,
                    levels,
                    params: *params,
                    // Разбор внутри мотива живёт в стёртом фрагменте: мотив
                    // проверяется при `σ = 0`, где весь вектор нулевой, и `r`
                    // ни на что не влияет. `1` - наименьшая законная.
                    consumed: Mult::One,
                    scrutinee: Rc::new(Term::Var(Lvl(*level).to_index(ctx.size()))),
                    motive: Rc::new(inner_motive),
                    branches,
                }))
            }
        }
    }

    /// Поля конструктора, применённого к известным аргументам: значение и тип.
    fn applied_fields(
        &self,
        constructor: &Name,
        levels: &Rc<[Level]>,
        arguments: &[Rc<Value>],
        params: usize,
    ) -> Vec<(Rc<Value>, Rc<Value>)> {
        let Some(declaration) = self.signature.lookup(constructor) else {
            unreachable!("конструктор `{constructor}` объявлен")
        };
        let mut current = instantiate_telescope(
            declaration.instantiate_type(levels, &[]),
            &arguments[..params],
        );
        let mut fields = Vec::new();
        for argument in &arguments[params..] {
            let Value::Pi(_, _, domain, _, codomain) = &*current else {
                break;
            };
            fields.push((Rc::clone(argument), Rc::clone(domain)));
            current = codomain.apply(Rc::clone(argument));
        }
        fields
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
        let Some((data, levels, arguments)) = data_head(self.signature, &column.ty) else {
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
        // Семейство обязано быть применено полностью: параметры, потом индексы.
        // Иначе поля конструктора не сойдутся с параметрами, а мотив - с
        // индексами. Ядро проверяет то же самое перед разбором
        // (`NotADataValue`), но `compile` работает до него, и без этой строки
        // `x : Nat zero` роняет элаборацию в `instantiate_telescope`.
        if arguments.len() != binders(&declaration.ty) {
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

        let (params, indices) = arguments.split_at(*parameters as usize);
        Ok(Family {
            data,
            levels,
            params: params.to_vec(),
            shapes: indices
                .iter()
                .map(|index| unify::classify(self.signature, index))
                .collect(),
            constructors: constructors.clone(),
            parameters: *parameters,
        })
    }

    /// Поля конструктора при заданных параметрах и его результат.
    ///
    /// Результат - `D параметры индексы`, выраженный через поля: оттуда
    /// унификация берёт индексы ветви.
    fn fields(
        &self,
        ctx: &Ctx<'_>,
        constructor: &Name,
        levels: &Rc<[Level]>,
        params: &[Rc<Value>],
    ) -> (Vec<Field>, Rc<Value>) {
        let Some(declaration) = self.signature.lookup(constructor) else {
            unreachable!("конструктор `{constructor}` объявлен")
        };
        let mut current = instantiate_telescope(declaration.instantiate_type(levels, &[]), params);
        let mut fields = Vec::new();
        let mut level = ctx.size();
        while let Value::Pi(Binder { mult, .. }, name, domain, _, codomain) = &*current {
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
        (fields, current)
    }
}

/// Индуктивное семейство, по которому идёт разбор колонки.
struct Family {
    data: Name,
    levels: Rc<[Level]>,
    /// Параметры семейства - те же во всех ветвях.
    params: Vec<Rc<Value>>,
    /// Формы индексов разбираемого значения: по ним унифицируются ветви и по
    /// ним же решается, что различает мотив.
    shapes: Vec<Shape>,
    /// Конструкторы в порядке объявления: он же порядок ветвей.
    constructors: Vec<Name>,
    parameters: u32,
}

impl Family {
    /// Индексы конструктора, выраженные через поля его ветви.
    ///
    /// `None` - результат конструктора не то семейство; проверено при
    /// объявлении, поэтому здесь этого не бывает.
    fn branch_indices(&self, signature: &Signature, result: &Rc<Value>) -> Option<Vec<Rc<Value>>> {
        let (_, _, arguments) = data_head(signature, result)?;
        Some(arguments[self.parameters as usize..].to_vec())
    }
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

/// Ветвь конструктора до сборки.
struct Candidate {
    fields: Vec<Field>,
    /// Индексы, которые даёт конструктор, - выраженные через свои поля.
    indices: Vec<Rc<Value>>,
    /// Что сказала унификация.
    outcome: Match,
}

/// Разбор одной колонки: то, что общее для всех её ветвей.
struct Split<'a> {
    columns: &'a [Column],
    rows: &'a [Row],
    target: &'a Term,
    example: &'a [Pattern],
    /// Номер разбираемой колонки.
    column: usize,
    /// Уровень её связывания.
    scrutinee: u32,
    /// Кратность, с которой разбор потребляет разбираемое, - `r` из §3.3.
    ///
    /// Берётся у связывания: в поверхностном языке `r` не пишется и не
    /// выводится анализом, потому что разбирается всегда переменная. Поля
    /// ветви получают `q · r`, и вложенный разбор берёт `r` тем же правилом -
    /// у связывания поля, которое уже отмасштабировано.
    consumed: Mult,
    /// Номера вынесенных в мотив колонок, в порядке контекста.
    carried: Vec<usize>,
    /// Формы индексов после отбора: непрозрачная - позиция, по которой мотив
    /// не различает.
    shapes: Vec<Shape>,
}

impl Split<'_> {
    /// Вынесенные колонки.
    fn borrowed(&self) -> Vec<&Column> {
        self.carried
            .iter()
            .map(|index| &self.columns[*index])
            .collect()
    }

    /// Перенос в контекст ветви: разбираемое значение и переменные индексов
    /// стали значениями, копии соседей связываются подряд начиная с `base`.
    fn refinement(&self, built: &Rc<Value>, solved: &[(u32, Rc<Value>)], base: u32) -> Refinement {
        let mut values = Vec::with_capacity(solved.len() + 1);
        values.push((self.scrutinee, Rc::clone(built)));
        values.extend(
            solved
                .iter()
                .map(|(level, value)| (*level, Rc::clone(value))),
        );
        Refinement {
            built: values,
            carried: self
                .carried
                .iter()
                .enumerate()
                .map(|(position, index)| (self.columns[*index].bound(), base + arity_u32(position)))
                .collect(),
        }
    }

    /// Колонки ветви: разобранная заменяется своими полями, вынесенные -
    /// свежими копиями, прочие уточняются подстановкой.
    fn refined_columns(
        &self,
        inner: &Ctx<'_>,
        refinement: &Refinement,
        fields: &[Field],
        copies: &[(Mult, Name, Rc<Value>)],
        base: u32,
    ) -> Vec<Column> {
        let at = inner.size();
        let carry =
            |value: &Rc<Value>| inner.eval(&rewrite(&quote(at, value), 0, at, &refinement.at(at)));
        let mut refined = Vec::with_capacity(self.columns.len() + fields.len());
        for (index, column) in self.columns.iter().enumerate() {
            if index == self.column {
                for (position, field) in fields.iter().enumerate() {
                    let mut path = column.path.clone();
                    path.push(position);
                    refined.push(Column {
                        value: Value::var(Lvl(field.level)),
                        path,
                        ty: Rc::clone(&field.ty),
                    });
                }
            } else if let Some(position) = self.carried.iter().position(|carried| *carried == index)
            {
                refined.push(Column {
                    value: Value::var(Lvl(base + arity_u32(position))),
                    path: column.path.clone(),
                    ty: Rc::clone(&copies[position].2),
                });
            } else {
                // Не переехавшая колонка всё равно уточняется: её значением
                // могла быть переменная индекса, а типом - зависящий от неё.
                refined.push(Column {
                    value: carry(&column.value),
                    path: column.path.clone(),
                    ty: carry(&column.ty),
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
            &self.columns[self.column].path,
            Pattern::Constructor(
                Rc::clone(constructor),
                vec![Pattern::Var("_".into()); fields],
            ),
        );
        example
    }
}

/// Перенос терма из контекста разбора в контекст мотива или ветви.
///
/// Меняются двое: то, что стало значением (разбираемый аргумент и переменные
/// его индексов - в ветви), и вынесенные соседи, получившие новые связывания.
/// Всё прочее остаётся собой - меняется только пересчёт уровня в индекс.
struct Refinement {
    /// Пары "уровень, чем он оказался". По уровню срабатывает первая.
    built: Vec<(u32, Rc<Value>)>,
    /// Пары "уровень, уровень нового связывания".
    carried: Vec<(u32, u32)>,
}

impl Refinement {
    /// Отображение уровня в терм, записанный в контексте размера `at`.
    fn at(&self, at: u32) -> impl Fn(u32) -> Term + '_ {
        move |level| {
            if let Some((_, value)) = self.built.iter().find(|(from, _)| *from == level) {
                return quote(at, value);
            }
            match self.carried.iter().find(|(from, _)| *from == level) {
                Some((_, to)) => Term::Var(Lvl(*to).to_index(at)),
                None => Term::Var(Lvl(level).to_index(at)),
            }
        }
    }
}

/// Колонки, чьи типы зависят от уточняемых уровней, в порядке контекста.
///
/// Замыкание транзитивно: если тип соседа зависит от **вынесенного** соседа,
/// он обязан переехать тоже, иначе останется указывать на старое, неуточнённое
/// связывание. Колонка с известным значением не переезжает: её уточняет
/// подстановка, связывать заново нечего.
fn carried(ctx: &Ctx<'_>, columns: &[Column], refined: &[u32]) -> Vec<usize> {
    let size = ctx.size();
    let mut refined = refined.to_vec();
    let mut chosen: Vec<usize> = Vec::new();
    let mut grown = true;
    while grown {
        grown = false;
        for (index, column) in columns.iter().enumerate() {
            let Some(level) = column.level() else {
                continue;
            };
            if refined.contains(&level) || chosen.contains(&index) {
                continue;
            }
            if depends(size, &column.ty, &refined) {
                chosen.push(index);
                refined.push(level);
                grown = true;
            }
        }
    }
    // Порядок колонок - порядок сопоставления, а связывания идут в порядке
    // контекста: разбор колонки вставляет её поля в середину списка.
    chosen.sort_by_key(|index| columns[*index].bound());
    chosen
}

/// Цель разбора: `Pi <вынесенные соседи>. <тип результата>`.
///
/// Пишется в контексте `ctx` - там, где уже известны связывания, которыми
/// различение заменило переменные индексов, - а читается из контекста размера
/// `size`, в котором записаны типы колонок и сама цель.
fn goal(
    ctx: &Ctx<'_>,
    carried: &[&Column],
    target: &Term,
    size: u32,
    redirects: &[(u32, u32)],
) -> Term {
    let mut refinement = Refinement {
        built: Vec::new(),
        carried: redirects.to_vec(),
    };
    let mut inner = ctx.clone();
    let mut domains = Vec::with_capacity(carried.len());
    for column in carried {
        let at = inner.size();
        let binding = binding(&inner, column.bound());
        let (mult, name) = (binding.mult, Rc::clone(&binding.name));
        let domain = rewrite(&quote(size, &column.ty), 0, size, &refinement.at(at));
        let ty = inner.eval(&domain);
        inner = inner.bind(Rc::clone(&name), mult, ty);
        refinement.carried.push((column.bound(), at));
        domains.push((mult, name, domain));
    }

    let result = rewrite(target, 0, size, &refinement.at(inner.size()));
    domains
        .into_iter()
        .rev()
        .fold(result, |codomain, (mult, name, domain)| {
            Term::Pi(
                Binder::explicit(mult),
                name,
                Rc::new(domain),
                EffectRow::empty(),
                Rc::new(codomain),
            )
        })
}

/// Заведомо обитаемый тип того же универсума, что и цель.
///
/// `(1 _ : G) -> G` населяется тождеством при любом `G` и, в отличие от
/// `Unit`, не требует ни имени из prelude, ни того, чтобы это имя было
/// объявлено. Кратность 1, а не ω: ω-связывания unique-типа не существует, и
/// порождать его элаборация не вправе.
fn trivial(ctx: &Ctx<'_>, plan: &Split<'_>, size: u32, solved: &[(u32, u32)]) -> Term {
    let goal = goal(ctx, &plan.borrowed(), plan.target, size, solved);
    let shifted = shift(&goal, 1);
    Term::Pi(
        Binder::explicit(Mult::One),
        "_".into(),
        Rc::new(goal),
        EffectRow::empty(),
        Rc::new(shifted),
    )
}

/// Какие позиции индексов различает мотив.
///
/// Различать нужно там, где конструкторы расходятся - иначе невозможную ветвь
/// нечем населить, - и там, где переменные позиции встречаются в цели, иначе
/// уточнение до неё не дойдёт. Прочие позиции мотив пропускает: разбор по ним
/// ничего не даёт, а требовать конструкторной формы от каждого конструктора
/// значило бы отвергать программы зря.
fn discriminated(shapes: &[Shape], candidates: &[Candidate], size: u32, goal: &Term) -> Vec<Shape> {
    shapes
        .iter()
        .enumerate()
        .map(|(position, shape)| {
            if !shape.is_rigid() {
                return shape.clone();
            }
            let conflicting = candidates.iter().any(|candidate| {
                matches!(
                    &candidate.outcome,
                    Match::Conflict { position: found, .. } if *found == position
                )
            });
            let mut variables = Vec::new();
            shape.variables(&mut variables);
            if conflicting || depends_term(goal, 0, size, &variables) {
                shape.clone()
            } else {
                Shape::Opaque
            }
        })
        .collect()
}

/// Упоминает ли тип хоть один из уровней.
///
/// Считается по нормальной форме: `(\_ -> Nat) b` от `b` не зависит, и
/// уточнять там нечего.
fn depends(size: u32, ty: &Rc<Value>, levels: &[u32]) -> bool {
    depends_term(&quote(size, ty), 0, size, levels)
}

/// То же по терму, записанному в контексте размера `size`.
fn depends_term(term: &Term, depth: u32, size: u32, levels: &[u32]) -> bool {
    let recur = |inner: &Rc<Term>| depends_term(inner, depth, size, levels);
    let under = |inner: &Rc<Term>| depends_term(inner, depth + 1, size, levels);
    match term {
        Term::Var(Index(index)) => *index >= depth && levels.contains(&(size + depth - 1 - index)),
        Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Const(..)
        | Term::Meta(_) => false,
        // Хвост стоит на исходной глубине, а не под полями: открытый ряд
        // зависимостей не имеет (§4.2).
        Term::Record(fields) | Term::Row(fields) => {
            fields.iter().enumerate().any(|(index, field)| {
                depends_term(
                    &field.ty,
                    depth + u32::try_from(index).unwrap_or(0),
                    size,
                    levels,
                )
            }) || fields.tail.as_ref().is_some_and(&recur)
        }
        Term::Object(fields) => fields.iter().any(|(_, value)| recur(value)),
        Term::With(base, fields) => recur(base) || fields.iter().any(|(_, value)| recur(value)),
        Term::Project(record, _) => recur(record),
        Term::Lam(_, _, body) => under(body),
        Term::App(callee, argument) => recur(callee) || recur(argument),
        Term::Pi(_, _, domain, row, codomain) => {
            recur(domain)
                || under(codomain)
                || row
                    .labels()
                    .iter()
                    .flat_map(|label| &label.arguments)
                    .any(|argument| depends_term(argument, depth, size, levels))
        }
        Term::Let(_, _, ty, value, body) => recur(ty) || recur(value) || under(body),
        Term::Case(case) => {
            recur(&case.scrutinee)
                || recur(&case.motive)
                || case.branches.iter().any(|branch| recur(&branch.body))
        }
    }
}

/// Конструктор в голове значения: имя, аргументы уровня и аргументы.
type ConstructorValue = (Name, Rc<[Level]>, Vec<Rc<Value>>);

/// Конструктор и его аргументы, если значение построено конструктором.
fn constructor_value(signature: &Signature, value: &Rc<Value>) -> Option<ConstructorValue> {
    let reduced = crate::conv::whnf(signature, value);
    let Value::Neutral(Head::Global(name, levels, _), spine) = &*reduced else {
        return None;
    };
    if !matches!(
        signature.lookup(name).map(|found| &found.kind),
        Some(DefinitionKind::Constructor { .. })
    ) {
        return None;
    }
    let arguments = spine
        .iter()
        .map(|elim| match elim {
            Elim::App(argument) => Some(Rc::clone(argument)),
            Elim::Case(_) | Elim::Project(_) | Elim::With(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((Rc::clone(name), Rc::clone(levels), arguments))
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
    let Value::Neutral(Head::Global(name, levels, _), spine) = &*reduced else {
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
            Elim::Case(_) | Elim::Project(_) | Elim::With(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((Rc::clone(name), Rc::clone(levels), arguments))
}

/// Сколько связываний у типа.
fn binders(ty: &Term) -> usize {
    let mut count = 0;
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
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
            Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Const(..)
            | Term::Meta(_) => true,
            Term::Record(fields) | Term::Row(fields) => {
                fields.iter().enumerate().all(|(index, field)| {
                    go(
                        &field.ty,
                        depth + u32::try_from(index).unwrap_or(0),
                        binders,
                    )
                }) && fields
                    .tail
                    .as_ref()
                    .is_none_or(|tail| go(tail, depth, binders))
            }
            Term::Object(fields) => fields.iter().all(|(_, value)| go(value, depth, binders)),
            Term::With(base, fields) => {
                go(base, depth, binders)
                    && fields.iter().all(|(_, value)| go(value, depth, binders))
            }
            Term::Project(record, _) => go(record, depth, binders),
            Term::Lam(_, _, body) => go(body, depth + 1, binders),
            Term::App(callee, argument) => {
                go(callee, depth, binders) && go(argument, depth, binders)
            }
            Term::Pi(_, _, domain, row, codomain) => {
                go(domain, depth, binders)
                    && go(codomain, depth + 1, binders)
                    && row
                        .labels()
                        .iter()
                        .flat_map(|label| &label.arguments)
                        .all(|argument| go(argument, depth, binders))
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
/// Поля с переписанными переменными: тип каждого - на своей глубине, хвост -
/// на исходной, потому что зависимостей в открытой записи нет.
fn rewrite_fields<F: Fn(u32) -> Term>(fields: &Fields, depth: u32, from: u32, map: &F) -> Fields {
    Fields {
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, field)| RecordField {
                name: Rc::clone(&field.name),
                mult: field.mult,
                ty: Rc::new(rewrite(
                    &field.ty,
                    depth + u32::try_from(index).unwrap_or(0),
                    from,
                    map,
                )),
            })
            .collect(),
        tail: fields
            .tail
            .as_ref()
            .map(|it| Rc::new(rewrite(it, depth, from, map))),
    }
}

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
        Term::Record(fields) => Term::Record(rewrite_fields(fields, depth, from, map)),
        Term::Row(fields) => Term::Row(rewrite_fields(fields, depth, from, map)),
        Term::Object(fields) => Term::Object(
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), recur(value)))
                .collect(),
        ),
        Term::With(base, fields) => Term::With(
            recur(base),
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), recur(value)))
                .collect(),
        ),
        Term::Project(record, name) => Term::Project(recur(record), Rc::clone(name)),
        Term::Universe(_)
        | Term::RowKind(_)
        | Term::EffectKind
        | Term::Const(..)
        | Term::Meta(_) => term.clone(),
        Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), under(body)),
        Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
        Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            recur(domain),
            row.map(|argument| rewrite(argument, depth, from, map)),
            under(codomain),
        ),
        Term::Let(mult, name, ty, value, body) => {
            Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), under(body))
        }
        Term::Case(case) => Term::Case(Rc::new(Case {
            data: Rc::clone(&case.data),
            levels: Rc::clone(&case.levels),
            params: case.params,
            consumed: case.consumed,
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
/// Поля со сдвинутыми индексами - той же формы, что и `rewrite_fields`.
fn shift_fields(fields: &Fields, depth: u32, by: u32) -> Fields {
    Fields {
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, field)| RecordField {
                name: Rc::clone(&field.name),
                mult: field.mult,
                ty: Rc::new(shift_at(
                    &field.ty,
                    depth + u32::try_from(index).unwrap_or(0),
                    by,
                )),
            })
            .collect(),
        tail: fields
            .tail
            .as_ref()
            .map(|it| Rc::new(shift_at(it, depth, by))),
    }
}

fn shift(term: &Term, by: u32) -> Term {
    shift_at(term, 0, by)
}

/// То же, начиная с глубины `depth`.
fn shift_at(term: &Term, depth: u32, by: u32) -> Term {
    fn go(term: &Term, depth: u32, by: u32) -> Term {
        let recur = |inner: &Rc<Term>| Rc::new(go(inner, depth, by));
        let under = |inner: &Rc<Term>| Rc::new(go(inner, depth + 1, by));
        match term {
            Term::Var(Index(index)) if *index >= depth => Term::Var(Index(index + by)),
            Term::Var(_)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Const(..)
            | Term::Meta(_) => term.clone(),
            Term::Record(fields) => Term::Record(shift_fields(fields, depth, by)),
            Term::Row(fields) => Term::Row(shift_fields(fields, depth, by)),
            Term::Object(fields) => Term::Object(
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Term::With(base, fields) => Term::With(
                recur(base),
                fields
                    .iter()
                    .map(|(name, value)| (Rc::clone(name), recur(value)))
                    .collect(),
            ),
            Term::Project(record, name) => Term::Project(recur(record), Rc::clone(name)),
            Term::Lam(mult, name, body) => Term::Lam(*mult, Rc::clone(name), under(body)),
            Term::App(callee, argument) => Term::App(recur(callee), recur(argument)),
            Term::Pi(binder, name, domain, row, codomain) => Term::Pi(
                *binder,
                Rc::clone(name),
                recur(domain),
                row.map(|argument| go(argument, depth, by)),
                under(codomain),
            ),
            Term::Let(mult, name, ty, value, body) => {
                Term::Let(*mult, Rc::clone(name), recur(ty), recur(value), under(body))
            }
            Term::Case(case) => Term::Case(Rc::new(Case {
                data: Rc::clone(&case.data),
                levels: Rc::clone(&case.levels),
                params: case.params,
                consumed: case.consumed,
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
        go(term, depth, by)
    }
}

/// Счётчик в `u32`. Столько аргументов и переменных не бывает.
fn arity_u32(value: usize) -> u32 {
    u32::try_from(value).unwrap_or_else(|_| unreachable!("счётчик не помещается в u32"))
}

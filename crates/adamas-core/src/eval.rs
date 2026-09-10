//! Normalization by evaluation (§9, Фаза 1).
//!
//! Вместо того чтобы переписывать термы правилами редукции, терм вычисляется в
//! значение средствами хозяйского языка, а потом читается обратно. Подстановка
//! при этом не выполняется ни разу: её заменяет захват окружения в замыкании.
//! Ровно то, что warm-up делал наивно и медленно - см.
//! `docs/warmup-retrospective.md`.
//!
//! Обратное чтение ([`quote`]) заходит под связывания, применяя замыкание к
//! свежей переменной. Поэтому результат - полная нормальная форма, а не только
//! головная.
//!
//! # Что здесь предполагается о входе
//!
//! Терм обязан быть **замкнутым и корректно типизированным**. Ядро -
//! нетипизированная λ-система, завершаемость ей даёт только типизация: на
//! `(\x -> x x) (\x -> x x)` вычисление разворачивается бесконечно и кладёт
//! процесс переполнением стека. Проверка типов - обязанность вызывающего, и
//! отдельного предохранителя (счётчика шагов) здесь нет: в отличие от
//! warm-up'а, где расходимость была штатным пользовательским случаем, сюда
//! расходящийся терм может попасть только при поломке проверяющего.

use std::rc::Rc;

use crate::row::{Row, Tail};
use crate::term::{Args, Branch, Case, Field, Fields, Mults, Name, Term};
use crate::value::{
    Closure, Elim, Env, Head, Lvl, RowClosure, StuckBranch, StuckCase, Telescope, Value,
};

impl Closure {
    /// Применяет замыкание к аргументу.
    #[must_use]
    pub fn apply(&self, argument: Rc<Value>) -> Rc<Value> {
        eval(&self.env.extend(argument), &self.body)
    }

    /// Тело замыкания вместе с окружением, в котором его вычислять.
    ///
    /// Нужно тому, кто вычисляет **не** через [`eval`]: интерпретатор эффектов
    /// (§9 Фаза 5) обязан войти в тело сам, потому что внутри тела бывает
    /// операция, и рекурсия `eval` перехватить её не даст.
    #[must_use]
    pub fn open(&self) -> (&Env, &Rc<Term>) {
        (&self.env, &self.body)
    }
}

/// Вычисляет терм в окружении.
///
/// Терм обязан быть корректно типизированным - иначе вычисление может не
/// завершиться, см. заголовок модуля.
///
/// # Panics
///
/// Паникует на незамкнутом терме - индексе, которому нечего сопоставить в
/// окружении. Это internal invariant: замкнутость обеспечивает проверяющий, и
/// нарушить её может только поломка компилятора.
#[must_use]
pub fn eval(env: &Env, term: &Term) -> Rc<Value> {
    match term {
        Term::Var(index) => env.lookup(*index).unwrap_or_else(|| {
            unreachable!("незамкнутый терм: {index:?} при {} связываниях", env.len())
        }),

        // Решённая дырка разворачивается сразу: её решение замкнуто, поэтому
        // окружение ему не нужно. Нерешённая застревает - головой спайна,
        // ровно как переменная контекста.
        Term::Meta(meta) => Rc::new(Value::Neutral(Head::Meta(*meta), Vec::new())),

        Term::Universe(level) => Rc::new(Value::Universe(level.clone())),

        // Тип и литерал уже значения. Операция - голова: применение к ней
        // копится спайном и сводится в `try_apply`, когда аргументов набралось
        // два и оба оказались литералами.
        Term::Prim(crate::prim::Prim::Op(op, ty)) => {
            Rc::new(Value::Neutral(Head::Prim(*op, *ty), Vec::new()))
        }
        // Массив и операции над ним - головы по той же причине: и тип
        // применяется к длине с элементом, и операция копит аргументы спайном
        // (§4.11).
        Term::Prim(crate::prim::Prim::Array) => Rc::new(Value::Neutral(Head::Array, Vec::new())),
        Term::Prim(crate::prim::Prim::Over(op)) => {
            Rc::new(Value::Neutral(Head::ArrayOp(*op), Vec::new()))
        }
        Term::Prim(prim) => Rc::new(Value::Prim(*prim)),

        Term::Lam(mult, name, body) => Rc::new(Value::Lam(
            *mult,
            Rc::clone(name),
            Closure {
                env: env.clone(),
                body: Rc::clone(body),
            },
        )),

        Term::Pi(binder, name, domain, row, codomain) => Rc::new(Value::Pi(
            *binder,
            Rc::clone(name),
            eval(env, domain),
            // Row стоит под связыванием наравне с кодоменом, поэтому и она
            // замыкание: `{Alloc r}` у `(0 r : Region) -> {Alloc r} Nat`
            // называет аргумент, а он станет известен только при применении.
            RowClosure {
                env: env.clone(),
                row: row.clone(),
            },
            Closure {
                env: env.clone(),
                body: Rc::clone(codomain),
            },
        )),

        Term::App(callee, argument) => apply(&eval(env, callee), eval(env, argument)),

        // Определение не разворачивается здесь: оно остаётся застрявшим, а
        // δ-редукцию делает проверка конвертируемости и только когда это
        // действительно нужно (`crate::conv`). Иначе нормальные формы и
        // сообщения об ошибках раздувались бы телами всех определений.
        // Аргументы-row вычисляются вместе с термом: метки несут обычные
        // термы, и под связыванием они без вычисления остались бы индексами,
        // которым в значении не на что указывать.
        Term::Const(name, levels, args) => Value::constant(
            Rc::clone(name),
            levels,
            args.row_args().iter().map(|row| row_of(env, row)).collect(),
            Mults::new(args.mult_args().iter().copied()),
        ),

        // Тип связывания при вычислении не нужен: он влияет на проверку, а не
        // на значение.
        Term::Let(_, _, _, value, body) => {
            let value = eval(env, value);
            eval(&env.extend(value), body)
        }

        Term::RowKind(level) => Rc::new(Value::RowKind(level.clone())),
        Term::EffectKind => Rc::new(Value::EffectKind),

        // Ни тип записи, ни ряд вычислением не раскрываются: поля живут
        // телескопом, и вычислить тип поля можно только вместе со значениями
        // предыдущих. Окружение поэтому захватывается целиком - как у
        // замыкания.
        Term::Record(fields) => Rc::new(Value::Record(telescope(env, fields))),

        // **Ряд без собственных полей есть его хвост.** Это не оптимизация, а
        // единичный закон расширения: `{| r }` и `r` описывают один набор
        // меток. Без него `r` - переменная, а `{| r }` - конструктор, и
        // сравнение их не сводит ничем; на этом спотыкалась унификация двух
        // открытых записей. Запись так не схлопывается: `{ | r }` - тип
        // значения с полями `r`, а не сам ряд.
        Term::Row(fields) => match (fields.is_empty(), &fields.tail) {
            (true, Some(tail)) => eval(env, tail),
            _ => Rc::new(Value::Row(telescope(env, fields))),
        },

        Term::Object(fields) => Rc::new(Value::Object(
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), eval(env, value)))
                .collect(),
        )),

        Term::With(base, fields) => with(
            &eval(env, base),
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), eval(env, value)))
                .collect(),
        ),

        Term::Project(record, name) => project(&eval(env, record), name),

        // Вычисляется **одна** ветвь - та, что выбрана. Собрать застрявший
        // разбор целиком значит вычислить мотив и все ветви, а у дерева
        // разбора ветвь сама бывает разбором: цена растёт как `2^d` вместо
        // `d`. Застрявший разбор собирается только когда он и правда застрял.
        Term::Case(case) => {
            let scrutinee = eval(env, &case.scrutinee);
            let selected = match &*scrutinee {
                Value::Neutral(Head::Global(name, ..), spine) => case
                    .branches
                    .iter()
                    .find(|branch| branch.constructor == *name)
                    .map(|branch| (Rc::clone(&branch.body), spine.clone())),
                _ => None,
            };
            match selected {
                Some((body, spine)) => apply_fields(eval(env, &body), &spine, case.params)
                    .unwrap_or_else(|| unreachable!("конструктор под разбором: {scrutinee}")),
                None => eliminate_case(&Rc::new(stuck_case(env, case)), &scrutinee),
            }
        }
    }
}

/// Row в значение: аргументы меток вычисляются, а хвост-параметр заменяется
/// аргументом из окружения.
///
/// Подстановка идёт здесь, а не заранее по терму, потому что метка несёт
/// **открытые** термы: замкнутого шага, на котором её можно было бы вложить в
/// тело определения, не существует (§3.2).
#[must_use]
pub fn row_of(env: &Env, row: &Row<Term>) -> Row<Rc<Value>> {
    let mapped = row.map(|argument| eval(env, argument));
    match row.tail() {
        Some(Tail::Var(index)) => env
            .row(index)
            .map_or(mapped.clone(), |tail| mapped.substituted(tail)),
        _ => mapped,
    }
}

/// Читает телескоп обратно - по одному полю, каждое под предыдущими.
fn quote_fields(size: u32, telescope: &Telescope) -> Fields {
    let mut earlier = Vec::with_capacity(telescope.fields().len());
    let mut written = Vec::with_capacity(telescope.fields().len());
    for (index, field) in telescope.fields().iter().enumerate() {
        let ty = telescope.at(index, &earlier);
        let depth = size + u32::try_from(index).unwrap_or(0);
        written.push(Field {
            name: Rc::clone(&field.name),
            mult: field.mult,
            shape: field.shape,
            ty: Rc::new(quote(depth, &ty)),
        });
        earlier.push(Value::var(Lvl(depth)));
    }
    // Хвост от полей не зависит: открытая запись зависимостей не имеет
    // (§4.2, решение 2026-08-29), поэтому читается он на исходной глубине.
    Fields {
        fields: written.into(),
        tail: telescope.tail().map(|tail| Rc::new(quote(size, &tail))),
    }
}

/// Телескоп полей вместе с окружением, в котором их вычислять.
fn telescope(env: &Env, fields: &Fields) -> Telescope {
    Telescope {
        env: env.clone(),
        fields: fields.clone(),
    }
}

/// Берёт поле у записи; на застрявшем значении копит проекцию в спайне.
///
/// # Panics
///
/// Если поля нет: имена сверяет проверка типов, и промах здесь - её пропуск.
#[must_use]
pub fn project(record: &Rc<Value>, name: &Name) -> Rc<Value> {
    match &**record {
        Value::Object(fields) => {
            let Some((_, value)) = fields.iter().find(|(field, _)| field == name) else {
                unreachable!("поля `{name}` нет в записи")
            };
            Rc::clone(value)
        }
        // Проекция сквозь переопределение считается: написанное поле берётся
        // прямо, ненаписанное - у базы, то есть `With` из спайна снимается.
        // Это и есть правило вычисления `{ p | x = v }`, и без него проекция
        // застревала бы на записи, поля которой известны.
        Value::Neutral(head, spine) => {
            if let Some((Elim::With(fields), rest)) = spine.split_last().map(|it| (it.0, it.1)) {
                if let Some((_, value)) = fields.iter().rev().find(|(field, _)| field == name) {
                    return Rc::clone(value);
                }
                let base = Rc::new(Value::Neutral(head.clone(), rest.to_vec()));
                return project(&base, name);
            }
            let mut spine = spine.clone();
            spine.push(Elim::Project(Rc::clone(name)));
            Rc::new(Value::Neutral(head.clone(), spine))
        }
        _ => unreachable!("проекция не из записи: {record}"),
    }
}

/// Переопределяет поля записи: `{ p | x = v }`.
///
/// На собранной записи пересобирает её - написанное поле заменяет одноимённое,
/// а не найденное дописывается слева, затеняя всё, что могло бы прийти из
/// хвоста. На застрявшей базе копит элиминатор в спайне.
///
/// # Panics
///
/// Если база не запись: сверяет это проверка типов.
#[must_use]
pub fn with(base: &Rc<Value>, fields: Vec<(Name, Rc<Value>)>) -> Rc<Value> {
    match &**base {
        Value::Object(written) => {
            // Шаг в шаг с типизацией (`check::infer_with`): написанное поле
            // либо заменяет своё, либо дописывается в конец. Отсюда же и
            // ответ на дубликат в написанном - побеждает последний, потому
            // что тип от него же и остался.
            let mut found: Vec<(Name, Rc<Value>)> = written.to_vec();
            for (name, value) in fields {
                match found.iter().position(|(it, _)| *it == name) {
                    Some(at) => found[at].1 = value,
                    None => found.push((name, value)),
                }
            }
            Rc::new(Value::Object(found.into()))
        }
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::With(fields.into()));
            Rc::new(Value::Neutral(head.clone(), spine))
        }
        _ => unreachable!("переопределение не записи: {base}"),
    }
}

/// Применяет тело ветви к полям конструктора.
///
/// Спайн конструктора - это параметры, потом поля; ветвь получает только
/// вторые. `None` - в спайне оказался разбор, то есть значение не конструктор.
fn apply_fields(body: Rc<Value>, spine: &[Elim], params: u32) -> Option<Rc<Value>> {
    spine
        .iter()
        .skip(params as usize)
        .try_fold(body, |body, elim| match elim {
            Elim::App(argument) => try_apply(&body, Rc::clone(argument)),
            Elim::Case(_) | Elim::Project(_) | Elim::With(_) => None,
        })
}

/// Переводит разбор из терма в значение, вычисляя мотив и ветви.
fn stuck_case(env: &Env, case: &Case) -> StuckCase {
    StuckCase {
        data: Rc::clone(&case.data),
        levels: case
            .levels
            .iter()
            .map(crate::level::Level::normalize)
            .collect(),
        params: case.params,
        consumed: case.consumed,
        motive: eval(env, &case.motive),
        branches: case
            .branches
            .iter()
            .map(|branch| StuckBranch {
                constructor: Rc::clone(&branch.constructor),
                body: eval(env, &branch.body),
            })
            .collect(),
    }
}

/// Выполняет разбор над значением - ι-редукция.
///
/// Сводится, когда голова разбираемого значения оказалась конструктором из
/// ветвей: тогда спайн - это параметры, потом поля, и ветвь применяется к
/// полям. Всё остальное застревает, включая **определение с телом**: [`eval`]
/// его не разворачивает, и `case two of …` останется застрявшим до тех пор,
/// пока разворота не потребует проверка конвертируемости ([`crate::conv`]).
///
/// # Panics
///
/// Паникует, если разбирается не застрявшее значение. Internal invariant:
/// у значения индуктивного типа других форм не бывает, а типизацию обеспечивает
/// вызывающий. Там, где инвариант держать некому - δ-разворот переигрывает
/// спайн, накопленный над значением **другого** типа, - берут
/// [`try_eliminate_case`].
#[must_use]
pub fn eliminate_case(case: &Rc<StuckCase>, scrutinee: &Rc<Value>) -> Rc<Value> {
    try_eliminate_case(case, scrutinee)
        .unwrap_or_else(|| unreachable!("разбор неподходящего значения: {scrutinee}"))
}

/// [`eliminate_case`], возвращающая `None` вместо паники.
///
/// `None` - разбираемое значение не той формы: не нейтраль вовсе либо
/// конструктор, над которым уже накоплен разбор. Из корректно типизированного
/// терма ни то ни другое не получается, но δ-разворот ([`crate::conv`])
/// переигрывает спайн над развёрнутым телом, а тело может оказаться чем угодно,
/// если сравниваются значения разных типов - что проверка конвертируемости
/// обязана переживать отказом, а не падением.
#[must_use]
pub fn try_eliminate_case(case: &Rc<StuckCase>, scrutinee: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(head, spine) = &**scrutinee else {
        return None;
    };

    if let Head::Global(name, ..) = head {
        if let Some(branch) = case
            .branches
            .iter()
            .find(|branch| branch.constructor == *name)
        {
            return apply_fields(Rc::clone(&branch.body), spine, case.params);
        }
    }

    let mut spine = spine.clone();
    spine.push(Elim::Case(Rc::clone(case)));
    Some(Rc::new(Value::Neutral(head.clone(), spine)))
}

/// Применяет значение к аргументу.
///
/// # Panics
///
/// Паникует на применении не-функции. Internal invariant: такие термы
/// отвергает проверяющий. Где инвариант не гарантирован - [`try_apply`].
#[must_use]
pub fn apply(callee: &Rc<Value>, argument: Rc<Value>) -> Rc<Value> {
    try_apply(callee, argument).unwrap_or_else(|| unreachable!("применение не-функции: {callee}"))
}

/// [`apply`], возвращающая `None` вместо паники. См. [`try_eliminate_case`].
#[must_use]
pub fn try_apply(callee: &Rc<Value>, argument: Rc<Value>) -> Option<Rc<Value>> {
    match &**callee {
        Value::Lam(_, _, closure) => Some(closure.apply(argument)),
        // Применение застряло - аргумент дописывается в спайн.
        Value::Neutral(head, spine) => {
            let mut spine = spine.clone();
            spine.push(Elim::App(argument));
            if let Head::Prim(op, ty) = head {
                if let Some(folded) = folded(*op, *ty, &spine) {
                    return Some(folded);
                }
            }
            if let Head::ArrayOp(crate::prim::ArrayOp::Index) = head {
                if let Some(read) = indexed(&spine) {
                    return Some(read);
                }
            }
            Some(Rc::new(Value::Neutral(head.clone(), spine)))
        }
        _ => None,
    }
}

/// δ-шаг примитивной операции: два литерала своего типа сводятся в один.
///
/// Аргумент не литерал - операция остаётся застрявшей, как всякий спайн над
/// переменной. Тип аргумента сверяет проверка, здесь он лишь читается: чужой
/// литерал в спайне означал бы, что проверка его пропустила.
fn folded(op: crate::prim::PrimOp, ty: crate::prim::PrimTy, spine: &[Elim]) -> Option<Rc<Value>> {
    let [Elim::App(left), Elim::App(right)] = spine else {
        return None;
    };
    let (
        Value::Prim(crate::prim::Prim::Lit(_, left)),
        Value::Prim(crate::prim::Prim::Lit(_, right)),
    ) = (&**left, &**right)
    else {
        return None;
    };
    Some(Rc::new(Value::Prim(crate::prim::Prim::literal(
        ty,
        op.fold(ty, *left, *right),
    ))))
}

/// Чтение ячейки массива (§4.11): последняя запись по этому номеру и выигрывает.
///
/// Массив здесь - **спайн**, а не отдельная форма значения: `arrayNew`
/// заводит его, `arraySet` наращивает цепочку. Чтение идёт от вершины вниз и
/// останавливается на первой записи в ту же ячейку; дно цепочки - `arrayNew`,
/// и там лежит начальное значение. Порядок этот и есть семантика записи: она
/// заслоняет прежнее.
///
/// Не сводится, когда номер не литерал, когда цепочка упирается не в
/// `arrayNew` (массив пришёл переменной) либо когда номер вне длины.
///
/// Последнее - **названная граница**: у понижения тот же случай обрывает
/// процесс (`adamas_fail`), и сходятся два вычислителя лишь в том, что оба не
/// дают ответа. Корпус программ с выходом за длину не содержит.
fn indexed(spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::{ArrayOp, Prim};
    let [Elim::App(_), Elim::App(_), Elim::App(array), Elim::App(at)] = spine else {
        return None;
    };
    let Value::Prim(Prim::Lit(_, wanted)) = &**at else {
        return None;
    };
    let mut current = Rc::clone(array);
    loop {
        let Value::Neutral(Head::ArrayOp(op), spine) = &*Rc::clone(&current) else {
            return None;
        };
        match (op, spine.as_slice()) {
            (
                ArrayOp::Set,
                [
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(inner),
                    Elim::App(slot),
                    Elim::App(value),
                ],
            ) => {
                let Value::Prim(Prim::Lit(_, slot)) = &**slot else {
                    return None;
                };
                if slot == wanted {
                    return Some(Rc::clone(value));
                }
                current = Rc::clone(inner);
            }
            (ArrayOp::New, [Elim::App(_), Elim::App(count), Elim::App(initial)]) => {
                let Value::Prim(Prim::Lit(_, count)) = &**count else {
                    return None;
                };
                return (wanted < count).then(|| Rc::clone(initial));
            }
            _ => return None,
        }
    }
}

/// Читает значение обратно в терм.
///
/// `size` - число связываний в контексте: оно же уровень следующей свежей
/// переменной. Обязано совпадать с контекстом, в котором значение построено.
///
/// # Panics
///
/// Если `size` меньше - в значении окажется уровень, которому не соответствует
/// ни одно связывание. См. [`Lvl::to_index`].
#[must_use]
pub fn quote(size: u32, value: &Rc<Value>) -> Term {
    match &**value {
        // Уровень нормализуется, чтобы нормальная форма была канонической и
        // `max u 0` не отличался от `u`.
        Value::Universe(level) => Term::Universe(level.normalize()),
        // Стёртое обратно не читается - значения у него нет (§3.3). Имя
        // невыразимое: увидеть его автор вправе, написать не может.
        Value::Erased => Term::constant(crate::value::ERASED),

        Value::RowKind(level) => Term::RowKind(level.normalize()),
        Value::EffectKind => Term::EffectKind,
        Value::Prim(prim) => Term::Prim(*prim),

        // Телескоп читается по одному полю: тип каждого следующего живёт под
        // предыдущими, и подставлять туда надо свежие переменные.
        Value::Record(telescope) => Term::Record(quote_fields(size, telescope)),
        Value::Row(telescope) => Term::Row(quote_fields(size, telescope)),

        Value::Object(fields) => Term::Object(
            fields
                .iter()
                .map(|(name, value)| (Rc::clone(name), Rc::new(quote(size, value))))
                .collect(),
        ),

        Value::Neutral(head, spine) => {
            let base = match head {
                Head::Local(level) => Term::Var(level.to_index(size)),
                Head::Global(name, levels, rows, mults) => Term::Const(
                    Rc::clone(name),
                    Rc::clone(levels),
                    Args::new(
                        rows.iter()
                            .map(|row| row.map(|argument| quote(size, argument))),
                        mults.as_slice().iter().copied(),
                    ),
                ),
                Head::Meta(meta) => Term::Meta(*meta),
                Head::Prim(op, ty) => Term::Prim(crate::prim::Prim::Op(*op, *ty)),
                Head::Array => Term::Prim(crate::prim::Prim::Array),
                Head::ArrayOp(op) => Term::Prim(crate::prim::Prim::Over(*op)),
            };
            spine.iter().fold(base, |callee, elim| match elim {
                Elim::App(argument) => Term::App(Rc::new(callee), Rc::new(quote(size, argument))),
                Elim::Project(name) => Term::Project(Rc::new(callee), Rc::clone(name)),
                Elim::With(fields) => Term::With(
                    Rc::new(callee),
                    fields
                        .iter()
                        .map(|(name, value)| (Rc::clone(name), Rc::new(quote(size, value))))
                        .collect(),
                ),
                // Накопленный терм и есть то, на чём разбор застрял.
                Elim::Case(case) => Term::Case(Rc::new(Case {
                    data: Rc::clone(&case.data),
                    levels: Rc::clone(&case.levels),
                    params: case.params,
                    consumed: case.consumed,
                    scrutinee: Rc::new(callee),
                    motive: Rc::new(quote(size, &case.motive)),
                    branches: case
                        .branches
                        .iter()
                        .map(|branch| Branch {
                            constructor: Rc::clone(&branch.constructor),
                            body: Rc::new(quote(size, &branch.body)),
                        })
                        .collect(),
                })),
            })
        }

        Value::Lam(mult, name, closure) => Term::Lam(
            *mult,
            Rc::clone(name),
            Rc::new(quote(size + 1, &closure.apply(Value::var(Lvl(size))))),
        ),

        // Row читается обратно под тем же свежим связыванием, что и кодомен:
        // она стоит под ним и вправе его называть.
        Value::Pi(binder, name, domain, row, codomain) => Term::Pi(
            *binder,
            Rc::clone(name),
            Rc::new(quote(size, domain)),
            row.apply(Value::var(Lvl(size)))
                .map(|argument| quote(size + 1, argument)),
            Rc::new(quote(size + 1, &codomain.apply(Value::var(Lvl(size))))),
        ),
    }
}

/// Приводит замкнутый корректно типизированный терм к нормальной форме.
#[must_use]
pub fn normalize(term: &Term) -> Term {
    quote(0, &eval(&Env::default(), term))
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::row::Row;
    use crate::term::Binder;

    use super::{eval, normalize, quote};
    use crate::level::Level;
    use crate::mult::Mult;
    use crate::term::Term;
    use crate::value::{Env, Lvl, Value};

    /// `\(ω x) -> body`
    fn lam(body: Term) -> Term {
        Term::Lam(Mult::Many, "x".into(), Rc::new(body))
    }

    /// `(ω _ : domain) -> codomain`
    fn arrow(domain: Term, codomain: Term) -> Term {
        Term::Pi(
            Binder::explicit(Mult::Many),
            "_".into(),
            Rc::new(domain),
            Row::empty(),
            Rc::new(codomain),
        )
    }

    #[test]
    fn beta_reduction_happens() {
        // (\x -> x) (Type 0)  ==>  Type 0
        let term = lam(Term::var(0)).apply([Term::universe(0)]);
        assert_eq!(normalize(&term).to_string(), "Type 0");
    }

    #[test]
    fn a_row_names_the_binding_of_its_own_arrow() {
        // Row стоит под связыванием стрелки, поэтому `#0` в метке - её же
        // аргумент. Вычисление и обратное чтение обязаны это сохранить: читай
        // `quote` метку на глубине домена, тот же индекс указывал бы наружу
        // стрелки, и `(0 r : Region) -> {Alloc r} A` после нормализации значил
        // бы не то, что написано.
        let ty = Term::Pi(
            Binder::explicit(Mult::Many),
            "r".into(),
            Rc::new(Term::universe(0)),
            Row::new([crate::row::Label {
                name: "Alloc".into(),
                arguments: vec![Term::var(0)],
            }]),
            Rc::new(Term::universe(0)),
        );
        assert_eq!(
            normalize(&ty).to_string(),
            "(ω r : Type 0) -> {Alloc #0} Type 0"
        );
    }

    #[test]
    fn normalization_goes_under_binders() {
        // \y -> (\x -> x) y  ==>  \y -> y
        let term = lam(lam(Term::var(0)).apply([Term::var(0)]));
        assert_eq!(normalize(&term).to_string(), "\\(ω x) -> #0");
    }

    #[test]
    fn closures_capture_the_right_binding() {
        // (\a -> \b -> a) (Type 1)  ==>  \b -> Type 1
        // Если бы захват был неверен, тело вернуло бы b.
        let konst = lam(lam(Term::var(1)));
        let term = konst.apply([Term::universe(1)]);
        assert_eq!(normalize(&term).to_string(), "\\(ω x) -> Type 1");
    }

    #[test]
    fn shadowing_resolves_by_index_not_by_name() {
        // \x -> \x -> #1 - внешнее связывание, несмотря на совпадение имён.
        let term = lam(lam(Term::var(1)));
        assert_eq!(normalize(&term), term);
    }

    #[test]
    fn let_is_eliminated_by_evaluation() {
        // let x : Type 1 = Type 0 in x  ==>  Type 0
        let term = Term::Let(
            Mult::Many,
            "x".into(),
            Rc::new(Term::universe(1)),
            Rc::new(Term::universe(0)),
            Rc::new(Term::var(0)),
        );
        assert_eq!(normalize(&term).to_string(), "Type 0");
    }

    #[test]
    fn neutral_terms_accumulate_a_spine() {
        // В контексте из одной свободной переменной: f (\x -> x) остаётся как
        // есть, но аргумент нормализуется.
        let env = Env::default().extend(Value::var(Lvl(0)));
        let term = Term::var(0).apply([lam(lam(Term::var(0)).apply([Term::var(0)]))]);
        let quoted = quote(1, &eval(&env, &term));
        assert_eq!(quoted.to_string(), "#0 (\\(ω x) -> #0)");
    }

    #[test]
    fn universe_levels_are_normalized_on_readback() {
        // max 0 u  ==>  u
        let level = Level::Zero.max(Level::Var(crate::level::LevelVar(0)));
        let term = Term::Universe(level);
        assert_eq!(normalize(&term).to_string(), "Type u0");
    }

    #[test]
    fn pi_normalizes_domain_and_codomain() {
        // ((\x -> x) (Type 0)) -> ((\x -> x) (Type 0))  ==>  Type 0 -> Type 0
        let redex = || lam(Term::var(0)).apply([Term::universe(0)]);
        let term = arrow(redex(), redex());
        assert_eq!(normalize(&term).to_string(), "(ω _ : Type 0) -> Type 0");
    }

    #[test]
    fn normalization_is_idempotent() {
        let term = lam(lam(Term::var(1)).apply([Term::var(0)]));
        let once = normalize(&term);
        assert_eq!(normalize(&once), once);
    }
}

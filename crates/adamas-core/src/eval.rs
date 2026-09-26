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
    Block, Closure, Elim, Env, Head, Lvl, RowClosure, StuckBranch, StuckCase, Telescope, Value,
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
        Term::Prim(crate::prim::Prim::Cmp(op, ty)) => {
            Rc::new(Value::Neutral(Head::Cmp(*op, *ty), Vec::new()))
        }
        Term::Prim(crate::prim::Prim::Convert(cast)) => {
            Rc::new(Value::Neutral(Head::Convert(*cast), Vec::new()))
        }
        // Массив и операции над ним - головы по той же причине: и тип
        // применяется к длине с элементом, и операция копит аргументы спайном
        // (§4.11).
        Term::Prim(crate::prim::Prim::Array) => Rc::new(Value::Neutral(Head::Array, Vec::new())),
        Term::Prim(crate::prim::Prim::Over(op)) => {
            Rc::new(Value::Neutral(Head::ArrayOp(*op), Vec::new()))
        }
        // Операции региона (§3.6) - головы по тому же доводу: значение блока и
        // есть спайн `regionNew`/`regionAlloc`/`regionWrite`.
        Term::Prim(crate::prim::Prim::In(op)) => {
            Rc::new(Value::Neutral(Head::Region(*op), Vec::new()))
        }
        // Вектор (§4.9) - голова по тому же доводу: значение его есть спайн
        // `simdSplat`/`simdSet`, надстроенный арифметикой.
        Term::Prim(crate::prim::Prim::Simd) => Rc::new(Value::Neutral(Head::Simd, Vec::new())),
        Term::Prim(crate::prim::Prim::Across(op)) => {
            Rc::new(Value::Neutral(Head::SimdOp(*op), Vec::new()))
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

/// Читает плоский блок обратно - в `arrayNew` с надстройкой из `arraySet`.
///
/// Формы своей у блока в терме **нет** и заводить её нечем: `arrayNew` с
/// `arraySet` выражают всякое его содержимое, а второй способ написать массив
/// пришлось бы разбирать понижению, проверке типов и печати - трём местам,
/// которым блок не нужен вовсе.
///
/// Записи печатаются только для ячеек, отличных от нулевой: `arrayNew n c0`
/// уже кладёт `c0` во все, и повторять её значило бы печатать `arraySet`,
/// ничего не меняющий.
pub(crate) fn quote_block(size: u32, block: &crate::value::Block) -> Term {
    use crate::prim::{ArrayOp, Prim, PrimTy};
    let elem = Rc::new(quote(size, block.elem()));
    let length = Rc::new(Term::Prim(Prim::literal(PrimTy::UInt64, block.count())));
    let first = block.read(0).unwrap_or_default();
    let literal = |bits: u64| Rc::new(Term::Prim(Prim::literal(block.ty(), bits)));
    let apply = |callee: Term, argument: Rc<Term>| Term::App(Rc::new(callee), argument);
    let mut built = apply(
        apply(
            apply(Term::Prim(Prim::Over(ArrayOp::New)), Rc::clone(&elem)),
            Rc::clone(&length),
        ),
        literal(first),
    );
    for at in 1..block.count() {
        let Some(bits) = block.read(at) else { break };
        if bits == first {
            continue;
        }
        built = apply(
            apply(
                apply(
                    apply(
                        apply(Term::Prim(Prim::Over(ArrayOp::Set)), Rc::clone(&length)),
                        Rc::clone(&elem),
                    ),
                    Rc::new(built),
                ),
                Rc::new(Term::Prim(Prim::literal(PrimTy::UInt64, at))),
            ),
            literal(bits),
        );
    }
    built
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
        // Ответ сравнения - **голый** конструктор соглашения: [`compared`]
        // строит его без сигнатуры, а у программы, объявившей `Bool` в
        // подключаемом файле, ветви названы путём (§4.8, §10 вопрос 188).
        // Сверяется поэтому последний сегмент, и только для имён соглашения:
        // всякое другое застрявшее имя обязано оставаться застрявшим. Третье
        // такое имя - ответ линейного чтения массива (§10 вопрос 202), тот же
        // голый конструктор из δ-шага.
        if matches!(
            &**name,
            crate::prim::TRUE | crate::prim::FALSE | crate::prim::MKREAD
        ) {
            if let Some(branch) = case
                .branches
                .iter()
                .find(|branch| crate::term::short(&branch.constructor) == &**name)
            {
                return apply_fields(Rc::clone(&branch.body), spine, case.params);
            }
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
            if let Head::Cmp(op, ty) = head {
                if let Some(verdict) = compared(*op, *ty, &spine) {
                    return Some(verdict);
                }
            }
            if let Head::Convert(cast) = head {
                if let Some(answer) = converted(*cast, &spine) {
                    return Some(answer);
                }
            }
            if let Head::ArrayOp(op) = head {
                if let Some(answer) = arrayed(*op, &spine) {
                    return Some(answer);
                }
            }
            if let Head::Region(op) = head {
                if let Some(answer) = region_answer(*op, &spine) {
                    return Some(answer);
                }
            }
            if let Head::SimdOp(op) = head {
                if let Some(answer) = vectored(*op, &spine) {
                    return Some(answer);
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
///
/// **Целое деление на ноль тоже остаётся застрявшим** - [`crate::prim::PrimOp::fold`]
/// не отдаёт ему ответа. Это та же названная граница, что у чтения вне длины
/// массива: понижение обрывает прогон, машина не отвечает вовсе, и сходятся
/// два вычислителя в том, что ответа не даёт ни один.
/// Сводит преобразование, когда его единственный аргумент - литерал (§4.3).
fn converted(cast: crate::prim::PrimCast, spine: &[Elim]) -> Option<Rc<Value>> {
    let [Elim::App(argument)] = spine else {
        return None;
    };
    let Value::Prim(crate::prim::Prim::Lit(ty, bits)) = &**argument else {
        return None;
    };
    (*ty == cast.from).then(|| {
        Rc::new(Value::Prim(crate::prim::Prim::literal(
            cast.to,
            cast.apply(*bits),
        )))
    })
}

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
        op.fold(ty, *left, *right)?,
    ))))
}

/// δ-шаг сравнения: два литерала своего типа сводятся в конструктор `Bool`.
///
/// Имя конструктора - соглашение (§4.3, [`crate::prim::BOOL`]), и сигнатура
/// здесь не нужна: `True` и `False` аргументов не несут, поэтому спайн пуст, а
/// списки уровней, рядов и кратностей - тоже. Объяви программа `Bool` иначе, и
/// отказал бы её собственный разбор, а не эта свёртка.
fn compared(
    op: crate::prim::PrimCmp,
    ty: crate::prim::PrimTy,
    spine: &[Elim],
) -> Option<Rc<Value>> {
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
    let name = if op.holds(ty, *left, *right) {
        crate::prim::TRUE
    } else {
        crate::prim::FALSE
    };
    Some(Value::constant(
        crate::term::Name::from(name),
        &[],
        Rc::from([]),
        crate::term::Mults::none(),
    ))
}

/// δ-шаг операции над массивом (§4.11).
///
/// # Представлений два, и заводится первое из них
///
/// `arrayNew` с литеральной длиной и **примитивной литеральной** ячейкой даёт
/// [`Block`] - байты подряд с идентичностью. Всё прочее - непримитивная ячейка
/// (`Array 3 (Option Int64)`), нелитеральная длина, блок сверх
/// [`Block::LIMIT`] - остаётся спайном, ровно как было до блоков.
///
/// Почему первое вообще заведено: у спайна **нет адреса**, и машина оттого не
/// могла одолжить буфер чужой стороне (§5.3). Цена названа у [`Block`].
///
/// `arraySet` над блоком даёт **новый** блок: запись функциональна, и это то же
/// правило, каким спайн заслонял прежнюю ячейку новой записью. Не сложившийся
/// шаг (нелитеральный номер, нелитеральное значение, номер вне длины) оставляет
/// спайн **над копией** блока - не над ним самим: иначе чужая запись по
/// одолженному адресу исходного протекла бы в производный массив, которого у
/// рантайма не бывает (`adamas_array_writable` копирует разделённое).
fn arrayed(op: crate::prim::ArrayOp, spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::{ArrayOp, Prim};
    match op {
        ArrayOp::New => {
            let [Elim::App(elem), Elim::App(count), Elim::App(initial)] = spine else {
                return None;
            };
            let (Value::Prim(Prim::Lit(_, count)), Value::Prim(Prim::Lit(ty, init))) =
                (&**count, &**initial)
            else {
                return None;
            };
            let block = Block::new(*ty, Rc::clone(elem), *count, *init)?;
            Some(Rc::new(Value::Neutral(Head::Block(block), Vec::new())))
        }
        ArrayOp::Set => {
            let [
                Elim::App(_),
                Elim::App(_),
                Elim::App(array),
                Elim::App(slot),
                Elim::App(value),
            ] = spine
            else {
                return None;
            };
            let Value::Neutral(Head::Block(block), empty) = &**array else {
                return None;
            };
            if !empty.is_empty() {
                return None;
            }
            let (Value::Prim(Prim::Lit(_, slot)), Value::Prim(Prim::Lit(ty, bits))) =
                (&**slot, &**value)
            else {
                return Some(copied(block, spine));
            };
            if *ty != block.ty() {
                return Some(copied(block, spine));
            }
            let written = block.with_cell(*slot, *bits)?;
            Some(Rc::new(Value::Neutral(Head::Block(written), Vec::new())))
        }
        ArrayOp::Index => {
            let [Elim::App(_), Elim::App(_), Elim::App(array), Elim::App(at)] = spine else {
                return None;
            };
            let Value::Prim(Prim::Lit(_, wanted)) = &**at else {
                return None;
            };
            cell_of(array, *wanted)
        }
        // Ответ линейного чтения - конструктор программы (§10 вопрос 202):
        // ячейка и **тот же** массив. Имя голое, как у `compared`: сверка
        // конструкторов идёт по последнему сегменту, и `Prelude.MkRead` его
        // узнаёт.
        ArrayOp::Read => {
            let [
                Elim::App(length),
                Elim::App(element),
                Elim::App(array),
                Elim::App(at),
            ] = spine
            else {
                return None;
            };
            let Value::Prim(Prim::Lit(_, wanted)) = &**at else {
                return None;
            };
            let cell = cell_of(array, *wanted)?;
            let head = Head::Global(
                crate::term::Name::from(crate::prim::MKREAD),
                Rc::from([]),
                Rc::from([]),
                crate::term::Mults::none(),
            );
            Some(Rc::new(Value::Neutral(
                head,
                vec![
                    Elim::App(Rc::clone(length)),
                    Elim::App(Rc::clone(element)),
                    Elim::App(cell),
                    Elim::App(Rc::clone(array)),
                ],
            )))
        }
    }
}

/// Спайн `arraySet` над **копией** блока: шаг не сложился, а делить байты с
/// исходным нельзя. См. [`arrayed`].
fn copied(block: &Rc<crate::value::Block>, spine: &[Elim]) -> Rc<Value> {
    let mut spine = spine.to_vec();
    if let Some(copy) = block.with_cell(0, block.read(0).unwrap_or_default()) {
        spine[2] = Elim::App(Rc::new(Value::Neutral(Head::Block(copy), Vec::new())));
    }
    Rc::new(Value::Neutral(
        Head::ArrayOp(crate::prim::ArrayOp::Set),
        spine,
    ))
}

/// Значение ячейки `wanted` (§4.11): последняя запись по этому номеру и
/// выигрывает.
///
/// Представлений массива два, и читаются оба одним обходом. **Блок** отвечает
/// сразу - байты лежат подряд, и ячейка берётся по смещению. **Спайн** читается
/// от вершины вниз: чтение останавливается на первой записи в ту же ячейку, а
/// дно цепочки - `arrayNew` либо блок, если запись над ним не сложилась.
///
/// Не сводится, когда номер не литерал, когда цепочка упирается в переменную
/// либо когда номер вне длины.
///
/// Последнее - **названная граница**: у понижения тот же случай обрывает
/// процесс (`adamas_fail`), и сходятся два вычислителя лишь в том, что оба не
/// дают ответа. Корпус программ с выходом за длину не содержит.
///
/// Вынесено отдельно потому, что векторная загрузка (§4.9) читает по этому же
/// правилу `n` соседних ячеек.
fn cell_of(array: &Rc<Value>, wanted: u64) -> Option<Rc<Value>> {
    use crate::prim::{ArrayOp, Prim};
    let wanted = &wanted;
    let mut current = Rc::clone(array);
    loop {
        let Value::Neutral(head, spine) = &*Rc::clone(&current) else {
            return None;
        };
        if let Head::Block(block) = head {
            if !spine.is_empty() {
                return None;
            }
            let bits = block.read(*wanted)?;
            return Some(Rc::new(Value::Prim(Prim::literal(block.ty(), bits))));
        }
        let Head::ArrayOp(op) = head else {
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

/// δ-шаг вектора (§4.9): чтение дорожки и подорожечная арифметика.
///
/// # Машина считает `Simd` подорожечно, и это решение трека H
///
/// §4.9 обещает, что операции над `Simd` лоуэрятся в инструкции напрямую.
/// Машина инструкций не имеет, и вариантов у неё два: считать подорожечно либо
/// объявить вектор своей границей. Взят первый - договор трёх вычислителей
/// (`adamas-codegen/tests/agreement.rs`) требует, чтобы одна программа давала
/// одно значение у машины, у C и у LLVM, а граница вывела бы всякую фикстуру с
/// вектором из `eval/` и тем ослабила бы договор ровно там, где заводится новое
/// представление.
///
/// # Значение вектора - спайн, и оттого арифметика сводится **сразу**
///
/// Отдельной формы значения у вектора нет: `simdSplat` заводит цепочку,
/// `simdSet` её наращивает - ровно как это делал массив до плоского блока
/// (§4.11, [`crate::value::Block`]; вектору блок не заведён, потому что адреса
/// у него никто не просит). Отсюда
/// цена, и она **измерена**: пока `simdAdd` не сводился сам, а раскрывался
/// только чтением дорожки, цепочка росла на два узла за операцию, и векторный
/// цикл на 4096 витков ронял машину переполнением стека - `lane_of`
/// проталкивала чтение вглубь рекурсией по числу операций, а не по ширине.
///
/// Поэтому арифметика сводится к **канонической форме** сразу, как только обе
/// стороны читаются дорожками-литералами: ответ есть `simdSplat` с дорожкой
/// нуль, надстроенный `simdSet`'ами по числу дорожек. Глубина цепочки тем самым
/// ограничена **шириной вектора**, а не длиной программы, и виток перестаёт
/// накапливать. Тот же ход, каким [`folded`] сводит два скалярных литерала в
/// один.
///
/// Правила, и они ровно правила element-wise семантики:
///
/// - `simdLane (simdSplat n x) i` → `x`;
/// - `simdLane (simdSet v j x) i` → `x` при `i = j`, иначе `simdLane v i`;
/// - `simdAdd u w` → канон, чья дорожка `i` есть `addT (u[i]) (w[i])`,
///   посчитанное тем же [`crate::prim::PrimOp::fold`], каким считается скаляр.
///   Второго счёта сложения поэтому не существует, и разойтись `Float32` в
///   одинарной точности с самим собой негде.
///
/// Не сводится, когда номер дорожки не литерал, когда цепочка упирается не в
/// `simdSplat` (вектор пришёл переменной), когда ширина не литерал либо когда
/// номер вне ширины. Последнее - **названная граница**, та же, что у массива: у
/// понижения выход за ширину обрывает процесс, и сходятся два вычислителя лишь
/// в том, что ответа не даёт ни один.
fn vectored(op: crate::prim::SimdOp, spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::{Prim, SimdOp};
    match op {
        SimdOp::Lane => {
            let [
                Elim::App(_),
                Elim::App(_),
                Elim::App(_),
                Elim::App(vector),
                Elim::App(at),
            ] = spine
            else {
                return None;
            };
            let Value::Prim(Prim::Lit(_, wanted)) = &**at else {
                return None;
            };
            lane_of(vector, *wanted)
        }
        SimdOp::Add | SimdOp::Sub | SimdOp::Mul => {
            let [
                Elim::App(width),
                Elim::App(lane),
                Elim::App(dict),
                Elim::App(left),
                Elim::App(right),
            ] = spine
            else {
                return None;
            };
            let Value::Prim(Prim::Lit(_, lanes)) = &**width else {
                return None;
            };
            let arith = op.arith()?;
            let mut folded = Vec::with_capacity(usize::try_from(*lanes).ok()?);
            for at in 0..*lanes {
                let (left, right) = (lane_of(left, at)?, lane_of(right, at)?);
                let (Value::Prim(Prim::Lit(ty, left)), Value::Prim(Prim::Lit(_, right))) =
                    (&*left, &*right)
                else {
                    return None;
                };
                folded.push(Rc::new(Value::Prim(Prim::literal(
                    *ty,
                    arith.fold(*ty, *left, *right)?,
                ))));
            }
            Some(canonical(width, lane, dict, &folded))
        }
        SimdOp::Load => loaded(spine),
        SimdOp::Store => stored(spine),
        SimdOp::Splat | SimdOp::Set => None,
    }
}

/// δ-шаг векторной загрузки (§4.9): `simdLoad n xs i` → канон из `n` ячеек.
///
/// Ячейка читается тем же [`cell_of`], каким её читает `arrayIndex`: второй
/// счёт «что лежит в ячейке» разошёлся бы с первым молча. Не сводится по тем
/// же трём причинам, что чтение ячейки - номер не литерал, ширина не литерал,
/// массив не блок и цепочка не упирается в `arrayNew`, - плюс четвёртая: хвост
/// окна вышел за
/// длину. Последнее и есть **названная граница**, та же, что у выхода за длину
/// у `arrayIndex`: понижение там обрывает процесс, а машина не отвечает вовсе.
fn loaded(spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::Prim;
    let [
        Elim::App(_),
        Elim::App(lane),
        Elim::App(dict),
        Elim::App(width),
        Elim::App(array),
        Elim::App(at),
    ] = spine
    else {
        return None;
    };
    let (Value::Prim(Prim::Lit(_, lanes)), Value::Prim(Prim::Lit(_, first))) = (&**width, &**at)
    else {
        return None;
    };
    let mut cells = Vec::with_capacity(usize::try_from(*lanes).ok()?);
    for step in 0..*lanes {
        cells.push(cell_of(array, first.checked_add(step)?)?);
    }
    Some(canonical(width, lane, dict, &cells))
}

/// δ-шаг векторной записи (§4.9): `simdStore n xs i v` → цепочка `arraySet`.
///
/// Каждая запись идёт **тем же** δ-шагом, каким идёт написанный руками
/// `arraySet` ([`arrayed`]): окно из восьми записей неотличимо от восьми
/// записей, написанных руками, и это ровно то, что element-wise семантика §4.9
/// и обещает. Второй счёт «что делает запись» разошёлся бы с первым молча -
/// и разошёлся бы прежде всего на блоке: спайн, построенный здесь **мимо**
/// шага, оставил бы над блоком цепочку, у которой адреса уже нет.
fn stored(spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::Prim;
    let [
        Elim::App(length),
        Elim::App(lane),
        Elim::App(_),
        Elim::App(width),
        Elim::App(array),
        Elim::App(at),
        Elim::App(vector),
    ] = spine
    else {
        return None;
    };
    let (Value::Prim(Prim::Lit(_, lanes)), Value::Prim(Prim::Lit(_, first))) = (&**width, &**at)
    else {
        return None;
    };
    let mut built = Rc::clone(array);
    for step in 0..*lanes {
        let value = lane_of(vector, step)?;
        let index = Rc::new(Value::Prim(Prim::literal(
            crate::prim::PrimTy::UInt64,
            first.checked_add(step)?,
        )));
        let written = vec![
            Elim::App(Rc::clone(length)),
            Elim::App(Rc::clone(lane)),
            Elim::App(built),
            Elim::App(index),
            Elim::App(value),
        ];
        built = arrayed(crate::prim::ArrayOp::Set, &written).unwrap_or_else(|| {
            Rc::new(Value::Neutral(
                Head::ArrayOp(crate::prim::ArrayOp::Set),
                written,
            ))
        });
    }
    Some(built)
}

/// Каноническая форма вектора: `simdSplat` нулевой дорожкой плюс `simdSet` на
/// каждую остальную.
///
/// Стёртые аргументы - ширина, дорожка, словарь - берутся у разобранного
/// спайна, а не строятся заново: строить их было бы вторым местом, где тип
/// вектора собирается, и разъехалось бы оно молча.
fn canonical(
    width: &Rc<Value>,
    lane: &Rc<Value>,
    dict: &Rc<Value>,
    lanes: &[Rc<Value>],
) -> Rc<Value> {
    use crate::prim::{PrimTy, SimdOp};
    let Some(first) = lanes.first() else {
        // Вектора нулевой ширины не бывает: понижение отвергает его, а машина
        // сюда не доходит - `simdSplat` с нулём не строится ни одной
        // программой. Форма без дорожек всё равно обязана быть значением.
        return Rc::new(Value::Neutral(Head::SimdOp(SimdOp::Splat), Vec::new()));
    };
    let mut built = Rc::new(Value::Neutral(
        Head::SimdOp(SimdOp::Splat),
        vec![
            Elim::App(Rc::clone(lane)),
            Elim::App(Rc::clone(dict)),
            Elim::App(Rc::clone(width)),
            Elim::App(Rc::clone(first)),
        ],
    ));
    for (at, value) in lanes.iter().enumerate().skip(1) {
        let index = Rc::new(Value::Prim(crate::prim::Prim::literal(
            PrimTy::UInt64,
            u64::try_from(at).unwrap_or(u64::MAX),
        )));
        built = Rc::new(Value::Neutral(
            Head::SimdOp(SimdOp::Set),
            vec![
                Elim::App(Rc::clone(width)),
                Elim::App(Rc::clone(lane)),
                Elim::App(Rc::clone(dict)),
                Elim::App(built),
                Elim::App(index),
                Elim::App(Rc::clone(value)),
            ],
        ));
    }
    built
}

/// Значение дорожки `wanted` у вектора `vector`. См. [`laned`].
fn lane_of(vector: &Rc<Value>, wanted: u64) -> Option<Rc<Value>> {
    use crate::prim::{Prim, SimdOp};
    let mut current = Rc::clone(vector);
    loop {
        let Value::Neutral(Head::SimdOp(op), spine) = &*Rc::clone(&current) else {
            return None;
        };
        match (op, spine.as_slice()) {
            (
                SimdOp::Set,
                [
                    Elim::App(_),
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
                if *slot == wanted {
                    return Some(Rc::clone(value));
                }
                current = Rc::clone(inner);
            }
            (
                SimdOp::Splat,
                [
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(width),
                    Elim::App(initial),
                ],
            ) => {
                let Value::Prim(Prim::Lit(_, width)) = &**width else {
                    return None;
                };
                return (wanted < *width).then(|| Rc::clone(initial));
            }
            // Арифметика: чтение проталкивается внутрь обеих сторон, и дальше
            // работает обычная свёртка примитива. Ширина здесь не сверяется -
            // её уже сверил `simdSplat` на дне обеих цепочек.
            (SimdOp::Add | SimdOp::Sub | SimdOp::Mul, spine) => {
                let [
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(left),
                    Elim::App(right),
                ] = spine
                else {
                    return None;
                };
                let arith = op.arith()?;
                let left = lane_of(left, wanted)?;
                let right = lane_of(right, wanted)?;
                let (Value::Prim(Prim::Lit(ty, left)), Value::Prim(Prim::Lit(_, right))) =
                    (&*left, &*right)
                else {
                    return None;
                };
                return Some(Rc::new(Value::Prim(Prim::literal(
                    *ty,
                    arith.fold(*ty, *left, *right)?,
                ))));
            }
            _ => return None,
        }
    }
}

/// Хендл и чтение региона (§3.6): δ-шаг [`Head::Region`].
///
/// Блок здесь - **спайн**, как и массив: `regionNew` заводит цепочку,
/// `regionAlloc` и `regionWrite` её наращивают. Разница с массивом одна и она
/// существенная: ячейки у региона нет, есть **смещение**, и считается оно по
/// укладке нагрузки. Укладку приносит словарь `Flat`, стоящий вторым стёртым
/// аргументом каждой из этих операций, - без него смещения не существует, и
/// ограничение §3.6 держит здесь вторую свою работу помимо той, ради которой
/// написано.
///
/// Не сводится, когда хендл не литерал, когда цепочка упирается не в
/// `regionNew` (блок пришёл переменной) либо когда словарь ещё не решён -
/// обобщённый код над `{Flat a}` считает смещение уже на месте вызова.
fn region_answer(op: crate::prim::RegionOp, spine: &[Elim]) -> Option<Rc<Value>> {
    use crate::prim::{PrimTy, RegionOp};
    let word = |bits: u64| {
        Rc::new(Value::Prim(crate::prim::Prim::literal(
            PrimTy::UInt64,
            bits,
        )))
    };
    match (op, spine) {
        (RegionOp::Last, [Elim::App(block)]) => region_area(block)?.last.map(word),
        (RegionOp::Read, [Elim::App(_), Elim::App(_), Elim::App(block), Elim::App(at)]) => {
            let Value::Prim(crate::prim::Prim::Lit(_, wanted)) = &**at else {
                return None;
            };
            region_stored(block, *wanted)
        }
        _ => None,
    }
}

/// Одна аллокация в журнале области: где лежит, сколько занимает, отдана ли.
#[derive(Clone, Copy)]
struct Cell {
    at: u64,
    size: u64,
    free: bool,
}

/// Раскладка области: курсор, хендл последней аллокации и журнал ячеек.
///
/// Журнал здесь - не второе представление, а прочтение того же спайна: цепочка
/// операций и есть журнал. Рантайм держит его явно (`adamas.h`), потому что
/// цепочки у него нет вовсе, и числа обоих обязаны сойтись.
#[derive(Clone, Default)]
struct Area {
    used: u64,
    last: Option<u64>,
    cells: Vec<Cell>,
}

/// Раскладка области, посчитанная по спайну блока.
///
/// `last` - `None` у пустой области: аллокаций не было, и хендла не существует.
/// Запись курсора не двигает: §3.6 называет `write` операцией над уже
/// размещённым местом, а не аллокацией.
fn region_area(block: &Rc<Value>) -> Option<Area> {
    use crate::prim::RegionOp;
    let Value::Neutral(Head::Region(op), spine) = &**block else {
        return None;
    };
    match (op, spine.as_slice()) {
        // Разделяемая область считается **той же** пустой областью, и это
        // решение, а не заглушка (§3.6, `RegionOp::SharedNew`). Разделяемость
        // есть свойство тождества, а область ядра есть значение: программа,
        // различающая их, - ровно та, на которой машина и рантайм обязаны
        // разойтись. Линейно протянутая область их не различает, и договор
        // трёх вычислителей на ней цел.
        (RegionOp::New | RegionOp::SharedNew, []) => Some(Area::default()),
        (
            RegionOp::Alloc,
            [
                Elim::App(_),
                Elim::App(dict),
                Elim::App(inner),
                Elim::App(_),
            ],
        ) => {
            let mut area = region_area(inner)?;
            let (size, align) = region_layout(dict)?;
            region_place(&mut area, size, align)?;
            Some(area)
        }
        (
            RegionOp::Write,
            [
                Elim::App(_),
                Elim::App(_),
                Elim::App(inner),
                Elim::App(_),
                Elim::App(_),
            ],
        ) => region_area(inner),
        (RegionOp::Recycle, [Elim::App(inner), Elim::App(at)]) => {
            let mut area = region_area(inner)?;
            let at = literal(at)?;
            if let Some(cell) = area
                .cells
                .iter_mut()
                .rev()
                .find(|it| !it.free && it.at == at)
            {
                cell.free = true;
            }
            Some(area)
        }
        (RegionOp::Pop, [Elim::App(inner), Elim::App(at)]) => {
            let mut area = region_area(inner)?;
            let at = literal(at)?;
            if area.cells.last().is_some_and(|it| !it.free && it.at == at) {
                area.cells.pop();
                area.used = at;
                area.last = area.cells.last().map(|it| it.at);
            }
            Some(area)
        }
        _ => None,
    }
}

/// Куда ляжет нагрузка размера `size` по границе `align`.
///
/// Правило одно на все стратегии, и политики в нём нет: **свободная ячейка
/// равного размера, иначе подъём курсора**. Свободные ячейки заводит
/// `regionRecycle`, и у Arena их не бывает вовсе - оттуда и «bump» её обещания.
/// Ищется ячейка с конца: из равных подходит самая поздняя по размещению.
fn region_place(area: &mut Area, size: u64, align: u64) -> Option<()> {
    if let Some(cell) = area
        .cells
        .iter_mut()
        .rev()
        .find(|it| it.free && it.size == size && it.at % align.max(1) == 0)
    {
        cell.free = false;
        area.last = Some(cell.at);
        return Some(());
    }
    let at = aligned(area.used, align);
    area.used = at.checked_add(size)?;
    area.last = Some(at);
    area.cells.push(Cell {
        at,
        size,
        free: false,
    });
    Some(())
}

/// Биты литерала. `None` - значение литералом не является.
fn literal(value: &Rc<Value>) -> Option<u64> {
    match &**value {
        Value::Prim(crate::prim::Prim::Lit(_, bits)) => Some(*bits),
        _ => None,
    }
}

/// Значение, лежащее по смещению `wanted`: последняя запись туда и выигрывает.
///
/// Обход идёт от вершины вниз, как у массива, и останавливается на первой
/// операции, занявшей то же место. Дно цепочки - `regionNew`, где не лежит
/// ничего: чтение неразмещённого места не сводится.
///
/// Возврат ячейки байт не трогает - ни `regionRecycle`, ни `regionPop`, - и
/// обход через них проходит насквозь. Рантайм ведёт себя так же: возврат
/// правит журнал, а не нагрузку. Отсюда общая на оба вычислителя граница:
/// чтение отданной ячейки отдаёт то, что там лежало.
fn region_stored(block: &Rc<Value>, wanted: u64) -> Option<Rc<Value>> {
    use crate::prim::RegionOp;
    let mut current = Rc::clone(block);
    loop {
        let Value::Neutral(Head::Region(op), spine) = &*Rc::clone(&current) else {
            return None;
        };
        match (op, spine.as_slice()) {
            (
                RegionOp::Alloc,
                [
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(inner),
                    Elim::App(value),
                ],
            ) => {
                if region_area(&current)?.last == Some(wanted) {
                    return Some(Rc::clone(value));
                }
                current = Rc::clone(inner);
            }
            (RegionOp::Recycle | RegionOp::Pop, [Elim::App(inner), Elim::App(_)]) => {
                current = Rc::clone(inner);
            }
            (
                RegionOp::Write,
                [
                    Elim::App(_),
                    Elim::App(_),
                    Elim::App(inner),
                    Elim::App(at),
                    Elim::App(value),
                ],
            ) => {
                if literal(at)? == wanted {
                    return Some(Rc::clone(value));
                }
                current = Rc::clone(inner);
            }
            _ => return None,
        }
    }
}

/// Размер и выравнивание из словаря `Flat` (§4.11).
///
/// Словарь есть запись с единственным методом `layout`, а тот - запись из
/// `size` и `align`. Поля читаются **по имени**: порядок их - дело объявления
/// класса, и считать его позицией значило бы завести второе правило.
fn region_layout(dict: &Rc<Value>) -> Option<(u64, u64)> {
    let field = |value: &Rc<Value>, name: &str| match &**value {
        Value::Object(fields) => fields
            .iter()
            .find(|(label, _)| &**label == name)
            .map(|(_, value)| Rc::clone(value)),
        _ => None,
    };
    let bits = |value: &Rc<Value>| match &**value {
        Value::Prim(crate::prim::Prim::Lit(_, bits)) => Some(*bits),
        _ => None,
    };
    let layout = field(dict, "layout")?;
    let size = bits(&field(&layout, "size")?)?;
    let align = bits(&field(&layout, "align")?)?;
    Some((size, align.max(1)))
}

/// Ближайшее сверху кратное `align`. То же правило, что у типовой стороны.
fn aligned(offset: u64, align: u64) -> u64 {
    offset.next_multiple_of(align.max(1))
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
                Head::Cmp(op, ty) => Term::Prim(crate::prim::Prim::Cmp(*op, *ty)),
                Head::Convert(cast) => Term::Prim(crate::prim::Prim::Convert(*cast)),
                Head::Array => Term::Prim(crate::prim::Prim::Array),
                Head::ArrayOp(op) => Term::Prim(crate::prim::Prim::Over(*op)),
                Head::Block(block) => quote_block(size, block),
                Head::Region(op) => Term::Prim(crate::prim::Prim::In(*op)),
                Head::Simd => Term::Prim(crate::prim::Prim::Simd),
                Head::SimdOp(op) => Term::Prim(crate::prim::Prim::Across(*op)),
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

    /// Плоский блок читается обратно теми записями, которыми он сделан (§4.11).
    ///
    /// Форма ответа здесь не косметика. Блока в терме **нет**, и всё, что о нём
    /// знают печать, понижение и проверка типов, приходит через это обратное
    /// чтение; напечатай оно `arrayNew` без надстройки - и `arraySet`,
    /// изменивший ячейку, исчез бы из нормальной формы молча.
    ///
    /// Записи печатаются только для ячеек, отличных от нулевой: `arrayNew 3 7`
    /// уже кладёт семёрку во все три, и `arraySet` той же семёркой был бы
    /// записью, ничего не меняющей. Оттого вторая половина проверки.
    #[test]
    fn a_flat_block_reads_back_as_the_writes_that_made_it() {
        use crate::prim::{ArrayOp, Prim, PrimTy};
        let byte = |bits: u64| Term::Prim(Prim::literal(PrimTy::UInt8, bits));
        let length = Term::Prim(Prim::literal(PrimTy::UInt64, 3));
        let index = |at: u64| Term::Prim(Prim::literal(PrimTy::UInt64, at));
        let elem = Term::Prim(Prim::Ty(PrimTy::UInt8));
        let made =
            Term::Prim(Prim::Over(ArrayOp::New)).apply([elem.clone(), length.clone(), byte(7)]);
        let written = |array: Term, at: u64, bits: u64| {
            Term::Prim(Prim::Over(ArrayOp::Set)).apply([
                length.clone(),
                elem.clone(),
                array,
                index(at),
                byte(bits),
            ])
        };
        assert_eq!(
            normalize(&written(made.clone(), 1, 8)).to_string(),
            "arraySet 3 UInt8 (arrayNew UInt8 3 7) 1 8"
        );
        assert_eq!(
            normalize(&written(made, 1, 7)).to_string(),
            "arrayNew UInt8 3 7",
            "запись, ничего не меняющая, в нормальной форме не остаётся"
        );
    }

    /// Векторная запись оставляет **блок**, а не спайн над ним (§4.9, §4.11).
    ///
    /// Наблюдаемое выбрано формой нормальной формы, и это не косметика: у
    /// спайна над блоком нет адреса, и колонка, записанная `simdStore`, молча
    /// перестала бы одалживаться чужой стороне (§5.3). Ответ у обеих форм
    /// одинаковый - [`cell_of`] читает и ту и другую, - поэтому поймать разницу
    /// можно только здесь.
    ///
    /// До правки трека B волны 2 `simdStore` строил цепочку `arraySet` своими
    /// руками, мимо δ-шага; тогда нормальная форма была бы двумя `arraySet`
    /// поверх `arrayNew`.
    #[test]
    fn a_vector_write_leaves_a_flat_block() {
        use crate::prim::{Prim, PrimTy, SimdOp};
        let word = |bits: u64| Term::Prim(Prim::literal(PrimTy::UInt64, bits));
        let elem = Term::Prim(Prim::Ty(PrimTy::UInt64));
        // Стёртые аргументы - тип дорожки и словарь `Primitive`: ни того ни
        // другого шаг не читает, и здесь на их месте стоит любое значение.
        let erased = || Term::Prim(Prim::Ty(PrimTy::UInt64));
        let array = Term::Prim(Prim::Over(crate::prim::ArrayOp::New)).apply([
            elem.clone(),
            word(2),
            word(0),
        ]);
        let vector =
            Term::Prim(Prim::Across(SimdOp::Splat)).apply([erased(), erased(), word(2), word(7)]);
        let stored = Term::Prim(Prim::Across(SimdOp::Store)).apply([
            word(2),
            elem,
            erased(),
            word(2),
            array,
            word(0),
            vector,
        ]);
        assert_eq!(
            normalize(&stored).to_string(),
            "arrayNew UInt64 2 7",
            "векторная запись обязана идти тем же шагом, что `arraySet`"
        );
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

//! Машина: вычисление терма с перехватом операций.
//!
//! Повторяет [`adamas_core::eval`] в резумпционной монаде. Повторяет не всё:
//! формы, которые вычислением ничего не запускают - переменная, замыкание,
//! типы, сорта, - отданы ядерному `eval` дословно. Операции в них не бывает,
//! и переписывать их значило бы завести второе место, где `Pi` превращается в
//! значение.
//!
//! Считает **машина**, а не `eval`, ровно там, где под вычислением бывает
//! пользовательский код: применение, разбор, `let`, проекция, поле записи и
//! δ-разворот определения.

use std::cell::RefCell;
use std::rc::Rc;

use adamas_core::eval;
use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{Case, Name, Term};
use adamas_core::value::{Elim, Env, Head, StuckBranch, StuckCase, Value};

use crate::outcome::{Cont, Outcome, Performed};

/// Машина: сигнатура и таблица живых резумпций.
pub struct Machine<'a> {
    signature: &'a Signature,
    /// Резумпции по номеру. Номер - это имя `#resume.N` в значении.
    ///
    /// Таблица нужна потому, что [`Value`] хост-функции нести не умеет, а
    /// резумпция ветке отдаётся именно значением - ветка её применяет. Заводить
    /// ради этого вариант в ядре значило бы протащить рантайм в TCB; невыразимое
    /// имя делает то же самое снаружи, и приём тот же, каким названы словарь
    /// класса и сам элиминатор.
    ///
    /// Таблица растёт до конца прогона: резумпция живёт столько же, сколько
    /// значение, в которое она попала, а узнать это без счётчика ссылок нельзя.
    resumptions: RefCell<Vec<Cont>>,
}

impl std::fmt::Debug for Machine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Machine")
            .field("resumptions", &self.resumptions.borrow().len())
            .finish_non_exhaustive()
    }
}

/// Префикс невыразимого имени резумпции.
const RESUME: &str = "#resume.";

impl<'a> Machine<'a> {
    /// Машина над сигнатурой.
    #[must_use]
    pub fn new(signature: &'a Signature) -> Self {
        Self {
            signature,
            resumptions: RefCell::new(Vec::new()),
        }
    }

    /// Сигнатура, над которой идёт исполнение.
    #[must_use]
    pub fn signature(&self) -> &'a Signature {
        self.signature
    }

    /// Вычисляет терм в окружении.
    pub fn eval(&self, env: &Env, term: &Term) -> Outcome {
        match term {
            // Ничего не запускают: значение получается сразу, и ядерный `eval`
            // даёт ровно его. Замыкание сюда входит намеренно - тело его
            // побежит позже, через `apply`, то есть через машину.
            Term::Var(_)
            | Term::Meta(_)
            | Term::Universe(_)
            | Term::Pi(..)
            | Term::Lam(..)
            | Term::Const(..)
            | Term::Record(_)
            | Term::Row(_)
            | Term::RowKind(_)
            | Term::EffectKind => Outcome::Done(eval::eval(env, term)),

            Term::App(callee, argument) => {
                let callee = match self.eval(env, callee) {
                    Outcome::Done(value) => value,
                    Outcome::Performed(performed) => {
                        let (env, argument) = (env.clone(), Rc::clone(argument));
                        return performed
                            .after(Rc::new(move |machine, callee| {
                                machine.applied(&callee, &env, &argument)
                            }))
                            .into();
                    }
                };
                self.applied(&callee, env, argument)
            }

            Term::Let(_, _, _, value, body) => {
                let value = match self.eval(env, value) {
                    Outcome::Done(value) => value,
                    Outcome::Performed(performed) => {
                        let (env, body) = (env.clone(), Rc::clone(body));
                        return performed
                            .after(Rc::new(move |machine, value| {
                                machine.eval(&env.extend(value), &body)
                            }))
                            .into();
                    }
                };
                self.eval(&env.extend(value), body)
            }

            Term::Case(case) => {
                let scrutinee = match self.eval(env, &case.scrutinee) {
                    Outcome::Done(value) => value,
                    Outcome::Performed(performed) => {
                        let (env, case) = (env.clone(), Rc::clone(case));
                        return performed
                            .after(Rc::new(move |machine, scrutinee| {
                                machine.eliminate(scrutinee, &env, &case)
                            }))
                            .into();
                    }
                };
                self.eliminate(scrutinee, env, case)
            }

            Term::Project(record, name) => {
                let record = match self.eval(env, record) {
                    Outcome::Done(value) => value,
                    Outcome::Performed(performed) => {
                        let name = Rc::clone(name);
                        return performed
                            .after(Rc::new(move |machine, record| {
                                machine.project(record, &name)
                            }))
                            .into();
                    }
                };
                self.project(record, name)
            }

            Term::Object(fields) => self.object(env, fields, Vec::new()),

            Term::With(base, fields) => {
                let base = match self.eval(env, base) {
                    Outcome::Done(value) => value,
                    Outcome::Performed(performed) => {
                        let (env, fields) = (env.clone(), Rc::clone(fields));
                        return performed
                            .after(Rc::new(move |machine, base| {
                                machine.overridden(&base, &env, &fields, Vec::new())
                            }))
                            .into();
                    }
                };
                self.overridden(&base, env, fields, Vec::new())
            }
        }
    }

    /// Поля записи по порядку: слева направо, как их пишет автор.
    fn object(
        &self,
        env: &Env,
        fields: &Rc<[(Name, Rc<Term>)]>,
        mut done: Vec<(Name, Rc<Value>)>,
    ) -> Outcome {
        while done.len() < fields.len() {
            let (name, term) = &fields[done.len()];
            match self.eval(env, term) {
                Outcome::Done(value) => done.push((Rc::clone(name), value)),
                Outcome::Performed(performed) => {
                    let (env, fields, name) = (env.clone(), Rc::clone(fields), Rc::clone(name));
                    return performed
                        .after(Rc::new(move |machine, value| {
                            let mut done = done.clone();
                            done.push((Rc::clone(&name), value));
                            machine.object(&env, &fields, done)
                        }))
                        .into();
                }
            }
        }
        Outcome::Done(Rc::new(Value::Object(done.into())))
    }

    /// Переопределяемые поля по порядку, потом само переопределение.
    fn overridden(
        &self,
        base: &Rc<Value>,
        env: &Env,
        fields: &Rc<[(Name, Rc<Term>)]>,
        mut done: Vec<(Name, Rc<Value>)>,
    ) -> Outcome {
        while done.len() < fields.len() {
            let (name, term) = &fields[done.len()];
            match self.eval(env, term) {
                Outcome::Done(value) => done.push((Rc::clone(name), value)),
                Outcome::Performed(performed) => {
                    let (base, env) = (Rc::clone(base), env.clone());
                    let (fields, name) = (Rc::clone(fields), Rc::clone(name));
                    return performed
                        .after(Rc::new(move |machine, value| {
                            let mut done = done.clone();
                            done.push((Rc::clone(&name), value));
                            machine.overridden(&base, &env, &fields, done)
                        }))
                        .into();
                }
            }
        }
        Outcome::Done(eval::with(base, done))
    }

    /// Аргумент применения, когда функция уже посчитана.
    fn applied(&self, callee: &Rc<Value>, env: &Env, argument: &Rc<Term>) -> Outcome {
        let argument = match self.eval(env, argument) {
            Outcome::Done(value) => value,
            Outcome::Performed(performed) => {
                let callee = Rc::clone(callee);
                return performed
                    .after(Rc::new(move |machine, argument| {
                        machine.apply(&callee, argument)
                    }))
                    .into();
            }
        };
        self.apply(callee, argument)
    }

    /// Применяет значение к значению.
    pub fn apply(&self, callee: &Rc<Value>, argument: Rc<Value>) -> Outcome {
        let callee = match self.forced(Rc::clone(callee)) {
            Outcome::Done(value) => value,
            Outcome::Performed(performed) => {
                return performed
                    .after(Rc::new(move |machine, callee| {
                        machine.applying(&callee, Rc::clone(&argument))
                    }))
                    .into();
            }
        };
        self.applying(&callee, argument)
    }

    /// Применение к значению **головной формы**: разворачивать больше нечего.
    fn applying(&self, callee: &Rc<Value>, argument: Rc<Value>) -> Outcome {
        match &**callee {
            Value::Lam(_, _, closure) => {
                let (env, body) = closure.open();
                self.eval(&env.extend(argument), body)
            }
            Value::Neutral(Head::Global(name, levels, rows), spine) => {
                let mut spine = spine.clone();
                spine.push(Elim::App(argument));
                self.dispatch(name, levels, rows, spine)
            }
            // Локальная переменная и дырка: применение копится в спайне, как и
            // в ядре. Значение под связыванием машине не встречается - она
            // считает замкнутое, - но открытое приходит из инертных форм.
            _ => Outcome::Done(eval::apply(callee, argument)),
        }
    }

    /// Разбор по значению.
    fn eliminate(&self, scrutinee: Rc<Value>, env: &Env, case: &Rc<Case>) -> Outcome {
        let scrutinee = match self.forced(scrutinee) {
            Outcome::Done(value) => value,
            Outcome::Performed(performed) => {
                let (env, case) = (env.clone(), Rc::clone(case));
                return performed
                    .after(Rc::new(move |machine, scrutinee| {
                        machine.eliminating(&scrutinee, &env, &case)
                    }))
                    .into();
            }
        };
        self.eliminating(&scrutinee, env, case)
    }

    /// Разбор по значению головной формы.
    fn eliminating(&self, scrutinee: &Rc<Value>, env: &Env, case: &Rc<Case>) -> Outcome {
        let selected = match &**scrutinee {
            Value::Neutral(Head::Global(name, ..), spine) => case
                .branches
                .iter()
                .find(|branch| branch.constructor == *name)
                .map(|branch| (Rc::clone(&branch.body), spine.clone())),
            _ => None,
        };
        let Some((body, spine)) = selected else {
            // Застрял: ветви и мотив вычисляются ядерным `eval`. Тело ветви
            // при этом не побежит - разбор потому и застрял, - так что
            // операции в нём остаться негде.
            return Outcome::Done(eval::eliminate_case(&Rc::new(stuck(env, case)), scrutinee));
        };
        // Ветвь получает поля конструктора - параметры она не связывает.
        let fields: Vec<Rc<Value>> = spine
            .iter()
            .skip(case.params as usize)
            .filter_map(|elim| match elim {
                Elim::App(argument) => Some(Rc::clone(argument)),
                _ => None,
            })
            .collect();
        match self.eval(env, &body) {
            Outcome::Done(body) => self.spread(body, &fields, 0),
            Outcome::Performed(performed) => performed
                .after(Rc::new(move |machine, body| {
                    machine.spread(body, &fields, 0)
                }))
                .into(),
        }
    }

    /// Применяет тело ветви к полям конструктора по одному.
    fn spread(&self, body: Rc<Value>, fields: &[Rc<Value>], from: usize) -> Outcome {
        let mut body = body;
        for index in from..fields.len() {
            match self.apply(&body, Rc::clone(&fields[index])) {
                Outcome::Done(value) => body = value,
                Outcome::Performed(performed) => {
                    let fields = fields.to_vec();
                    return performed
                        .after(Rc::new(move |machine, body| {
                            machine.spread(body, &fields, index + 1)
                        }))
                        .into();
                }
            }
        }
        Outcome::Done(body)
    }

    /// Проекция поля.
    fn project(&self, record: Rc<Value>, name: &Name) -> Outcome {
        let record = match self.forced(record) {
            Outcome::Done(value) => value,
            Outcome::Performed(performed) => {
                let name = Rc::clone(name);
                return performed
                    .after(Rc::new(move |machine, record| {
                        machine.project(record, &name)
                    }))
                    .into();
            }
        };
        Outcome::Done(eval::project(&record, name))
    }

    /// Приводит значение к головной форме: разворачивает определение с телом.
    ///
    /// Разворот идёт **машиной**, а не `eval`: тело определения - обычный
    /// пользовательский код, и операция в нём бывает ровно так же, как в любом
    /// другом месте. Ворот тотальности и запечатывания здесь нет по тому же
    /// доводу, что и у `conv::unfolded`: они стоят у сравнения, которое обязано
    /// завершаться, а исполнение обязано расходиться там, где расходится
    /// программа.
    fn forced(&self, value: Rc<Value>) -> Outcome {
        let Value::Neutral(Head::Global(name, levels, rows), spine) = &*value else {
            return Outcome::Done(value);
        };
        let Some(definition) = self.signature.lookup(name) else {
            return Outcome::Done(Rc::clone(&value));
        };
        let Some(body) = &definition.body else {
            return Outcome::Done(Rc::clone(&value));
        };
        let body = body.substitute_levels(levels);
        let (rows, spine) = (Rc::clone(rows), spine.clone());
        match self.eval(&Env::rowed(rows), &body) {
            Outcome::Done(body) => self.replay(body, &spine, 0),
            Outcome::Performed(performed) => performed
                .after(Rc::new(move |machine, body| {
                    machine.replay(body, &spine, 0)
                }))
                .into(),
        }
    }

    /// Переигрывает спайн развёрнутого определения.
    ///
    /// Применение идёт машиной; прочие элиминаторы - ядром. Разбор в спайне
    /// сюда доходит только от инертных форм, то есть от типов, а типы операций
    /// не производят.
    fn replay(&self, callee: Rc<Value>, spine: &[Elim], from: usize) -> Outcome {
        let mut callee = callee;
        for index in from..spine.len() {
            match &spine[index] {
                Elim::App(argument) => match self.apply(&callee, Rc::clone(argument)) {
                    Outcome::Done(value) => callee = value,
                    Outcome::Performed(performed) => {
                        let spine = spine.to_vec();
                        return performed
                            .after(Rc::new(move |machine, callee| {
                                machine.replay(callee, &spine, index + 1)
                            }))
                            .into();
                    }
                },
                Elim::Case(case) => match eval::try_eliminate_case(case, &callee) {
                    Some(value) => callee = value,
                    None => return Outcome::Done(callee),
                },
                Elim::Project(name) => callee = eval::project(&callee, name),
                Elim::With(fields) => callee = eval::with(&callee, fields.to_vec()),
            }
        }
        // Развёрнутое могло снова оказаться определением с телом: `f = g`.
        match &*callee {
            Value::Neutral(Head::Global(..), _) => self.forced(callee),
            _ => Outcome::Done(callee),
        }
    }

    /// Читает значение в терм, досчитывая его насквозь.
    ///
    /// Читает **машина**, а не `conv`: значение, которое просто вернули, до сих
    /// пор не разворачивалось - разворот стоит у применения, разбора и
    /// проекции, а `Cons answered …` не делает ни того, ни другого, ни
    /// третьего. Дочитывало его обратное чтение ядра, то есть `eval`, и
    /// хендлер под ним оставался нейтралью. Ошибка тем и коварна, что
    /// **половина** ответа при этом верна: то, что попало под разбор, машина
    /// посчитала.
    ///
    /// # Errors
    ///
    /// Операция, дошедшая до чтения, хендлера не встретила: возобновлять её
    /// некуда, чтение и есть конец программы.
    pub fn read(&self, value: Rc<Value>) -> Result<Term, Performed> {
        let value = match self.forced(value) {
            Outcome::Done(value) => value,
            Outcome::Performed(performed) => return Err(performed),
        };
        match &*value {
            Value::Neutral(head @ Head::Global(name, ..), spine)
                if self.constructor(name) && applications(spine) =>
            {
                let base = eval::quote(0, &Rc::new(Value::Neutral(head.clone(), Vec::new())));
                spine.iter().try_fold(base, |callee, elim| {
                    let Elim::App(argument) = elim else {
                        unreachable!("спайн конструктора - одни применения");
                    };
                    Ok(Term::App(
                        Rc::new(callee),
                        Rc::new(self.read(Rc::clone(argument))?),
                    ))
                })
            }
            Value::Object(fields) => Ok(Term::Object(
                fields
                    .iter()
                    .map(|(name, field)| {
                        Ok((Rc::clone(name), Rc::new(self.read(Rc::clone(field))?)))
                    })
                    .collect::<Result<Vec<_>, Performed>>()?
                    .into(),
            )),
            _ => Ok(eval::quote(0, &value)),
        }
    }

    /// Конструктор ли это имя.
    fn constructor(&self, name: &Name) -> bool {
        matches!(
            self.signature.lookup(name).map(|it| &it.kind),
            Some(adamas_core::sig::DefinitionKind::Constructor { .. })
        )
    }

    /// Регистрирует резумпцию и отдаёт её значением.
    pub(crate) fn resumption(&self, cont: Cont) -> Rc<Value> {
        let mut table = self.resumptions.borrow_mut();
        let index = table.len();
        table.push(cont);
        Rc::new(Value::Neutral(
            Head::Global(
                Rc::from(format!("{RESUME}{index}")),
                Rc::from([] as [Level; 0]),
                Rc::from([] as [Row<Rc<Value>>; 0]),
            ),
            Vec::new(),
        ))
    }

    /// Что делать с насыщенным глобальным именем.
    fn dispatch(
        &self,
        name: &Name,
        levels: &Rc<[Level]>,
        rows: &Rc<[Row<Rc<Value>>]>,
        spine: Vec<Elim>,
    ) -> Outcome {
        if let Some(index) = name.strip_prefix(RESUME).and_then(|it| it.parse().ok()) {
            return self.resumed(index, &spine);
        }
        if let Some(outcome) = self.effectful(name, &spine) {
            return outcome;
        }
        Outcome::Done(Rc::new(Value::Neutral(
            Head::Global(Rc::clone(name), Rc::clone(levels), Rc::clone(rows)),
            spine,
        )))
    }

    /// Вызов резумпции. Аргумент у неё один - место операции.
    fn resumed(&self, index: usize, spine: &[Elim]) -> Outcome {
        let cont = {
            let table = self.resumptions.borrow();
            match table.get(index) {
                Some(cont) => Rc::clone(cont),
                None => unreachable!("резумпция {index} не заведена"),
            }
        };
        let Some(Elim::App(argument)) = spine.last() else {
            unreachable!("резумпция без аргумента");
        };
        cont(self, Rc::clone(argument))
    }
}

/// Все ли элиминаторы спайна - применения.
fn applications(spine: &[Elim]) -> bool {
    spine.iter().all(|elim| matches!(elim, Elim::App(_)))
}

/// Застрявший разбор: мотив и ветви как значения.
fn stuck(env: &Env, case: &Case) -> StuckCase {
    StuckCase {
        data: Rc::clone(&case.data),
        levels: Rc::clone(&case.levels),
        params: case.params,
        consumed: case.consumed,
        motive: eval::eval(env, &case.motive),
        branches: case
            .branches
            .iter()
            .map(|branch| StuckBranch {
                constructor: Rc::clone(&branch.constructor),
                body: eval::eval(env, &branch.body),
            })
            .collect(),
    }
}

impl From<Performed> for Outcome {
    fn from(performed: Performed) -> Self {
        Self::Performed(performed)
    }
}

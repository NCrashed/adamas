//! Машина: вычисление терма с явным стеком продолжения.
//!
//! Повторяет [`adamas_core::eval`] по смыслу, но не по устройству: у ядра
//! рекурсия по кадрам Rust, здесь - цикл над состоянием в куче. Разница
//! наблюдаема: `even (times 100 20)` - обычная структурная рекурсия -
//! роняла процесс `SIGABRT`'ом около полутора тысяч уровней, причём порог
//! двигался от профиля сборки **компилятора**, то есть свойством программы не
//! был вовсе.
//!
//! Повторяет не всё: формы, которые вычислением ничего не запускают -
//! переменная, замыкание, типы, сорта, - отданы ядерному `eval` дословно.
//! Операции в них не бывает, и переписывать их значило бы завести второе место,
//! где `Pi` превращается в значение.

use std::cell::RefCell;
use std::rc::Rc;

use adamas_core::eval;
use adamas_core::level::Level;
use adamas_core::row::Row;
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::term::{Case, Name, Term};
use adamas_core::value::{Elim, Env, Head, StuckBranch, StuckCase, Value};

use crate::RunError;
use crate::frame::{Frame, Kont};

/// Машина: сигнатура и таблица живых резумпций.
pub struct Machine<'a> {
    signature: &'a Signature,
    /// Резумпции по номеру: сегмент стека и была ли она позвана.
    ///
    /// Сегмент - и есть продолжение: положить его обратно значит возобновить.
    /// Мультишот копирует его на каждый вызов, поэтому кадры и сделаны дёшево
    /// клонируемыми.
    ///
    /// Отметка нужна одному - обрыву: ветка вернулась значением, не позвав
    /// продолжение, значит оно мертво, и деструкторы из него пора запускать.
    /// Работает это ровно потому, что резумпция при `handle` **аффинна**
    /// (§3.4); у `handleMulti` довод не держится, и оттуда ресурсы запрещены.
    resumptions: RefCell<Vec<Resumption>>,
}

impl std::fmt::Debug for Machine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Machine")
            .field("resumptions", &self.resumptions.borrow().len())
            .finish_non_exhaustive()
    }
}

/// Префикс невыразимого имени резумпции.
pub(crate) const RESUME: &str = "#resume.";

/// Что машина делает на следующем шаге.
pub(crate) enum Step {
    /// Вычислить терм в окружении.
    Eval(Env, Rc<Term>),
    /// Применить значение к значению.
    Apply(Rc<Value>, Rc<Value>),
    /// Отдать значение верхнему кадру.
    Return(Rc<Value>),
}

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

    /// Считает терм до значения.
    ///
    /// # Errors
    ///
    /// Операция, не встретившая хендлера.
    pub fn evaluate(&self, env: &Env, term: &Term) -> Result<Rc<Value>, RunError> {
        let mut kont: Kont = Vec::new();
        self.driving(Step::Eval(env.clone(), Rc::new(term.clone())), &mut kont)
    }

    /// Крутит машину, пока стек не опустеет.
    ///
    /// Здесь и живёт вся глубина исполнения: цикл вместо рекурсии, состояние в
    /// куче вместо кадров Rust.
    fn driving(&self, start: Step, kont: &mut Kont) -> Result<Rc<Value>, RunError> {
        let mut step = start;
        loop {
            step = match step {
                Step::Eval(env, term) => Self::evaluating(&env, &term, kont),
                Step::Apply(callee, argument) => self.forcing(&callee, argument, kont)?,
                Step::Return(value) => match kont.pop() {
                    None => return Ok(value),
                    Some(frame) => self.resuming(frame, value, kont)?,
                },
            };
        }
    }

    /// Приводит значение к головной форме: разворачивает определение с телом.
    ///
    /// # Errors
    ///
    /// Операция, не встретившая хендлера: тело определения - обычный код.
    pub(crate) fn forced(&self, value: Rc<Value>) -> Result<Rc<Value>, RunError> {
        let mut current = value;
        loop {
            let mut kont: Kont = Vec::new();
            let Some(step) = self.unfolding(&current, &mut kont) else {
                return Ok(current);
            };
            current = self.driving(step, &mut kont)?;
        }
    }

    /// Шаг по терму.
    fn evaluating(env: &Env, term: &Rc<Term>, kont: &mut Kont) -> Step {
        match &**term {
            // Ничего не запускают: значение получается сразу. Замыкание сюда
            // входит намеренно - тело его побежит позже, через применение.
            Term::Var(_)
            | Term::Meta(_)
            | Term::Universe(_)
            | Term::Pi(..)
            | Term::Lam(..)
            | Term::Const(..)
            | Term::Record(_)
            | Term::Row(_)
            | Term::RowKind(_)
            | Term::EffectKind => Step::Return(eval::eval(env, term)),

            Term::App(callee, argument) => {
                kont.push(Frame::Argument(env.clone(), Rc::clone(argument)));
                Step::Eval(env.clone(), Rc::clone(callee))
            }
            Term::Let(_, _, _, value, body) => {
                kont.push(Frame::Bind(env.clone(), Rc::clone(body)));
                Step::Eval(env.clone(), Rc::clone(value))
            }
            Term::Case(case) => {
                kont.push(Frame::Scrutinee(env.clone(), Rc::clone(case)));
                Step::Eval(env.clone(), Rc::clone(&case.scrutinee))
            }
            Term::Project(record, name) => {
                kont.push(Frame::Project(Rc::clone(name)));
                Step::Eval(env.clone(), Rc::clone(record))
            }
            Term::Object(fields) => Self::object(env, fields, Rc::from([]), kont),
            Term::With(base, fields) => {
                kont.push(Frame::Overriding(
                    env.clone(),
                    Rc::clone(fields),
                    Rc::from([]),
                    // База ещё не посчитана; кадр ждёт её первой.
                    None,
                ));
                Step::Eval(env.clone(), Rc::clone(base))
            }
        }
    }

    /// Следующее поле записи или готовая запись.
    fn object(
        env: &Env,
        fields: &Rc<[(Name, Rc<Term>)]>,
        done: Rc<[(Name, Rc<Value>)]>,
        kont: &mut Kont,
    ) -> Step {
        let Some((_, term)) = fields.get(done.len()) else {
            return Step::Return(Rc::new(Value::Object(done)));
        };
        let term = Rc::clone(term);
        kont.push(Frame::Object(env.clone(), Rc::clone(fields), done));
        Step::Eval(env.clone(), term)
    }

    /// Следующее переопределяемое поле или готовое переопределение.
    fn overriding(
        env: &Env,
        fields: &Rc<[(Name, Rc<Term>)]>,
        done: Rc<[(Name, Rc<Value>)]>,
        base: &Rc<Value>,
        kont: &mut Kont,
    ) -> Step {
        let Some((_, term)) = fields.get(done.len()) else {
            return Step::Return(eval::with(base, done.to_vec()));
        };
        let term = Rc::clone(term);
        kont.push(Frame::Overriding(
            env.clone(),
            Rc::clone(fields),
            done,
            Some(Rc::clone(base)),
        ));
        Step::Eval(env.clone(), term)
    }

    /// Применение: сперва привести функцию к головной форме.
    ///
    /// δ-разворот идёт **шагом**, а не рекурсией: тело определения - обычный
    /// пользовательский код, и глубина его та же, что у программы. Ворот
    /// тотальности и запечатывания здесь нет по тому же доводу, что и у
    /// `conv::unfolded`: они стоят у сравнения, которое обязано завершаться, а
    /// исполнение обязано расходиться там, где расходится программа.
    fn forcing(
        &self,
        callee: &Rc<Value>,
        argument: Rc<Value>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        match self.unfolding(callee, kont) {
            Some(step) => {
                // Кадр применения стоит **под** переигрыванием спайна: сперва
                // развёрнутое доберётся до головной формы, потом применится.
                let position = kont.len() - 1;
                kont.insert(position, Frame::Forcing(argument));
                Ok(step)
            }
            None => self.applying(callee, argument, kont),
        }
    }

    /// δ-шаг, если значение его требует.
    fn unfolding(&self, value: &Rc<Value>, kont: &mut Kont) -> Option<Step> {
        let Value::Neutral(Head::Global(name, levels, rows), spine) = &**value else {
            return None;
        };
        let body = self.signature.lookup(name)?.body.as_ref()?;
        let body = Rc::new(body.substitute_levels(levels));
        kont.push(Frame::Spine(spine.as_slice().into(), 0));
        Some(Step::Eval(Env::rowed(Rc::clone(rows)), body))
    }

    /// Применение к значению головной формы.
    fn applying(
        &self,
        callee: &Rc<Value>,
        argument: Rc<Value>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        match &**callee {
            Value::Lam(_, _, closure) => {
                let (env, body) = closure.open();
                Ok(Step::Eval(env.extend(argument), Rc::clone(body)))
            }
            Value::Neutral(Head::Global(name, levels, rows), spine) => {
                let mut spine = spine.clone();
                spine.push(Elim::App(argument));
                self.dispatch(name, levels, rows, spine, kont)
            }
            // Локальная переменная и дырка: применение копится в спайне, как и
            // в ядре.
            _ => Ok(Step::Return(eval::apply(callee, argument))),
        }
    }

    /// Что делать с насыщенным глобальным именем.
    fn dispatch(
        &self,
        name: &Name,
        levels: &Rc<[Level]>,
        rows: &Rc<[Row<Rc<Value>>]>,
        spine: Vec<Elim>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        if let Some(index) = name.strip_prefix(RESUME).and_then(|it| it.parse().ok()) {
            return Ok(self.resumed(index, &spine, kont));
        }
        if let Some(step) = self.effectful(name, &spine, kont)? {
            return Ok(step);
        }
        Ok(Step::Return(Rc::new(Value::Neutral(
            Head::Global(Rc::clone(name), Rc::clone(levels), Rc::clone(rows)),
            spine,
        ))))
    }

    /// Шаг по кадру, которому пришло значение.
    #[allow(
        clippy::too_many_lines,
        reason = "разбор кадров - одна таблица, и делить её значило бы прятать её половину"
    )]
    fn resuming(&self, frame: Frame, value: Rc<Value>, kont: &mut Kont) -> Result<Step, RunError> {
        match frame {
            Frame::Argument(env, argument) => {
                kont.push(Frame::Callee(value));
                Ok(Step::Eval(env, argument))
            }
            Frame::Callee(callee) => Ok(Step::Apply(callee, value)),
            Frame::Forcing(argument) => Ok(Step::Apply(value, argument)),
            Frame::Bind(env, body) => Ok(Step::Eval(env.extend(value), body)),
            Frame::Scrutinee(env, case) => Ok(self.eliminating(&value, &env, &case, kont)),
            Frame::Fields(fields, index) => Ok(Self::spreading(value, &fields, index, kont)),
            Frame::Project(name) => match self.unfolding(&value, kont) {
                Some(step) => {
                    let position = kont.len() - 1;
                    kont.insert(position, Frame::Project(name));
                    Ok(step)
                }
                None => Ok(Step::Return(eval::project(&value, &name))),
            },
            Frame::Object(env, fields, done) => {
                let (name, _) = &fields[done.len()];
                let done = extended(&done, Rc::clone(name), value);
                Ok(Self::object(&env, &fields, done, kont))
            }
            // Первой приходит база, дальше - поля по порядку.
            Frame::Overriding(env, fields, done, None) => {
                Ok(Self::overriding(&env, &fields, done, &value, kont))
            }
            Frame::Overriding(env, fields, done, Some(base)) => {
                let (name, _) = &fields[done.len()];
                let done = extended(&done, Rc::clone(name), value);
                Ok(Self::overriding(&env, &fields, done, &base, kont))
            }
            Frame::Spine(spine, index) => Ok(Self::replaying(value, &spine, index, kont)),
            Frame::Handler(handler) => Ok(Self::handled(value, &handler)),
            Frame::Branch(slot) => Ok(self.settled(slot, value, kont)),
            Frame::Closing(close) => {
                // Нормальный выход: деструктор, потом значение тела.
                kont.push(Frame::Closed(value));
                let unit = self.unit()?;
                Ok(Step::Apply(close, unit))
            }
            Frame::Closed(held) => Ok(Step::Return(held)),
            Frame::Unwinding(segment, index, held) => {
                Ok(self.unwinding(&segment, index, held, kont))
            }
            // Маскированное вычисление договорило: кадр снят, и следующие
            // операции той же метки снова видят ближайший хендлер.
            Frame::Masking(_) | Frame::Suppressing(_) => Ok(Step::Return(value)),
            Frame::Passing(given, index) => Ok(Self::passing(value, &given, index, kont)),
        }
    }

    /// Разбор по значению.
    fn eliminating(
        &self,
        scrutinee: &Rc<Value>,
        env: &Env,
        case: &Rc<Case>,
        kont: &mut Kont,
    ) -> Step {
        if let Some(step) = self.unfolding(scrutinee, kont) {
            let position = kont.len() - 1;
            kont.insert(position, Frame::Scrutinee(env.clone(), Rc::clone(case)));
            return step;
        }
        let selected = match &**scrutinee {
            Value::Neutral(Head::Global(name, ..), spine) => case
                .branches
                .iter()
                .find(|branch| branch.constructor == *name)
                .map(|branch| (Rc::clone(&branch.body), spine.clone())),
            _ => None,
        };
        let Some((body, spine)) = selected else {
            // Застрял: ветви и мотив вычисляются ядерным `eval`. Тело ветви при
            // этом не побежит - разбор потому и застрял.
            return Step::Return(eval::eliminate_case(&Rc::new(stuck(env, case)), scrutinee));
        };
        // Ветвь получает поля конструктора - параметры она не связывает.
        let fields: Rc<[Rc<Value>]> = spine
            .iter()
            .skip(case.params as usize)
            .filter_map(|elim| match elim {
                Elim::App(argument) => Some(Rc::clone(argument)),
                _ => None,
            })
            .collect();
        kont.push(Frame::Fields(fields, 0));
        Step::Eval(env.clone(), body)
    }

    /// Тело ветви к полям конструктора по одному.
    fn spreading(body: Rc<Value>, fields: &Rc<[Rc<Value>]>, index: usize, kont: &mut Kont) -> Step {
        let Some(field) = fields.get(index) else {
            return Step::Return(body);
        };
        kont.push(Frame::Fields(Rc::clone(fields), index + 1));
        Step::Apply(body, Rc::clone(field))
    }

    /// Аргументы ветке хендлера по одному.
    pub(crate) fn passing(
        branch: Rc<Value>,
        given: &Rc<[Rc<Value>]>,
        index: usize,
        kont: &mut Kont,
    ) -> Step {
        let Some(argument) = given.get(index) else {
            return Step::Return(branch);
        };
        kont.push(Frame::Passing(Rc::clone(given), index + 1));
        Step::Apply(branch, Rc::clone(argument))
    }

    /// Переигрывание спайна развёрнутого определения.
    fn replaying(callee: Rc<Value>, spine: &Rc<[Elim]>, index: usize, kont: &mut Kont) -> Step {
        let Some(elim) = spine.get(index) else {
            return Step::Return(callee);
        };
        match elim {
            Elim::App(argument) => {
                kont.push(Frame::Spine(Rc::clone(spine), index + 1));
                Step::Apply(callee, Rc::clone(argument))
            }
            // Прочие элиминаторы сюда доходят только от инертных форм, то есть
            // от типов, а типы операций не производят.
            Elim::Case(case) => match eval::try_eliminate_case(case, &callee) {
                Some(value) => Self::replaying(value, spine, index + 1, kont),
                None => Step::Return(callee),
            },
            Elim::Project(name) => {
                Self::replaying(eval::project(&callee, name), spine, index + 1, kont)
            }
            Elim::With(fields) => {
                Self::replaying(eval::with(&callee, fields.to_vec()), spine, index + 1, kont)
            }
        }
    }

    /// Заводит резумпцию из сегмента и отдаёт её значением.
    pub(crate) fn resumption(&self, segment: Rc<[Frame]>, multi: bool) -> (Rc<Value>, usize) {
        let mut table = self.resumptions.borrow_mut();
        let index = table.len();
        table.push(Resumption {
            segment,
            invoked: false,
            multi,
        });
        let value = Rc::new(Value::Neutral(
            Head::Global(
                Rc::from(format!("{RESUME}{index}")),
                Rc::from([] as [Level; 0]),
                Rc::from([] as [Row<Rc<Value>>; 0]),
            ),
            Vec::new(),
        ));
        (value, index)
    }

    /// Сегмент резумпции по номеру.
    pub(crate) fn segment(&self, index: usize) -> Option<Rc<[Frame]>> {
        self.resumptions
            .borrow()
            .get(index)
            .map(|it| Rc::clone(&it.segment))
    }

    /// Звали ли резумпцию хоть раз.
    pub(crate) fn invoked(&self, index: usize) -> bool {
        self.resumptions
            .borrow()
            .get(index)
            .is_some_and(|it| it.invoked)
    }

    /// Возобновление: сегмент кладётся обратно, значение идёт ему.
    fn resumed(&self, index: usize, spine: &[Elim], kont: &mut Kont) -> Step {
        let segment = {
            let mut table = self.resumptions.borrow_mut();
            match table.get_mut(index) {
                Some(entry) => {
                    entry.invoked = true;
                    // Аффинная резумпция второго вызова не имеет по
                    // построению (§3.4), поэтому её сегмент после первого
                    // отпускается. Держать его до конца прогона стоило
                    // квадрата: сегмент над хендлером растёт с глубиной
                    // рекурсии, а таблица только пополнялась, и шесть тысяч
                    // операций требовали четырёх гигабайт при ответе в одно
                    // число (ревью 2026-09-05). Мультишотной сегмент нужен
                    // и дальше - там повтор и есть её смысл.
                    if entry.multi {
                        Rc::clone(&entry.segment)
                    } else {
                        std::mem::replace(&mut entry.segment, Rc::from([] as [Frame; 0]))
                    }
                }
                None => unreachable!("резумпция {index} не заведена"),
            }
        };
        let Some(Elim::App(argument)) = spine.last() else {
            unreachable!("резумпция без аргумента");
        };
        kont.extend(segment.iter().cloned());
        Step::Return(Rc::clone(argument))
    }
}

/// Список полей с дописанным.
fn extended(
    done: &Rc<[(Name, Rc<Value>)]>,
    name: Name,
    value: Rc<Value>,
) -> Rc<[(Name, Rc<Value>)]> {
    done.iter()
        .cloned()
        .chain(std::iter::once((name, value)))
        .collect()
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

/// Конструктор ли это имя.
pub(crate) fn constructor(signature: &Signature, name: &Name) -> bool {
    matches!(
        signature.lookup(name).map(|it| &it.kind),
        Some(DefinitionKind::Constructor { .. })
    )
}

/// Запись таблицы резумпций: сегмент, звали ли её и мультишотна ли она.
///
/// Мультишотность нужна ровно затем, чтобы решить, отпускать ли сегмент после
/// первого возобновления: у аффинной второго вызова не бывает по построению
/// (§3.4), а у мультишотной повтор и есть её смысл.
struct Resumption {
    segment: Rc<[Frame]>,
    invoked: bool,
    multi: bool,
}

//! Файберы: несколько вычислений под одним питомником (§5.2).
//!
//! Файбер здесь - **сегмент того же стека**, а не второй стек и не поток.
//! Переключение поэтому есть перекладывание указателей на звенья: `cut` снимает
//! сегмент от кадра питомника до вершины, `restore` кладёт его обратно. Копий не
//! делается ни одной, и в этом вся разница с планировщиком, написанным на языке
//! (`eval/fibers.adamas`): тот держится на `ω`-резумпции, а `ω`-резумпция копирует
//! сегмент и не отпускает его до конца прогона.
//!
//! **Резумпция файбера аффинна**, потому что возобновляют его ровно один раз: он
//! либо стоит в очереди, либо бежит. Отсюда достаётся то, чего у написанного
//! планировщика нет по построению: сегмент отпускается после возобновления, и
//! ресурс внутри задачи законен.
//!
//! # Что машина знает по имени
//!
//! Пять имён, ровно как `Unit`: `withNursery` - постулат, чьё тело даёт машина;
//! `suspend`, `spawnDetached`, `spawn` и `await` - операции, которые она
//! обслуживает сама. Ни одной новой формы в языке для этого не нужно, объявляет
//! их автор обычным `effect` и типы пишет сам.
//!
//! Тип задачи вшитым именем **не** является: машина берёт его из написанного
//! результата `spawn` и требует от него двух вещей - один конструктор и одно
//! поле, куда встанет невыразимое имя файбера. Не сошлось - отказ на месте.
//!
//! Обслуживает она их **только под питомником и только если он ближе хендлера**:
//! написанный `handle` над той же меткой продолжает работать и значит ровно то,
//! что написано. Ближайший выигрывает - то же правило, по которому выбирается
//! хендлер.

use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::DefinitionKind;
use adamas_core::term::{Mults, Name, Term};
use adamas_core::value::{Elim, Head, Value};

use crate::RunError;
use crate::frame::{Frame, Kont, Segment};
use crate::machine::{Machine, Step};

/// Имя постулата, запускающего питомник.
pub(crate) const NURSERY: &str = "withNursery";
/// Операция уступки: файбер уходит в хвост очереди.
pub(crate) const SUSPEND: &str = "suspend";
/// Порождение без результата (§5.2, `spawnDetached`): вычисление - файбером.
pub(crate) const SPAWN: &str = "spawnDetached";
/// Порождение задачи (§5.2, `spawn`): отвечает значением, называющим файбер.
pub(crate) const TASK: &str = "spawn";
/// Ожидание чужого ответа (§5.2, `await`).
pub(crate) const AWAIT: &str = "await";

/// Префикс невыразимого имени, которым значение задачи называет свой файбер.
///
/// Приём тот же, что у резумпции: написать его автор не может, а `await` и
/// печать читают из него номер. Стоит оно **аргументом объявленного
/// конструктора**, поэтому `drop (MkTask n)` разбирается как обычно.
const FIBER: &str = "#fiber.";

/// Приостановленный файбер.
enum Suspended {
    /// Ещё не начатый: приостановленное вычисление, которое запустит питомник.
    Fresh(Rc<Value>),
    /// Уступивший: сегмент стека от кадра питомника до вершины и то, чем
    /// возобновление ему ответит.
    ///
    /// Ответ хранится **при файбере**, а не берётся у пробуждающего: уступка
    /// отвечает единицей, а ожидание - значением дождавшейся задачи, и
    /// различить их в момент пробуждения нечем. Пока `waking` отвечала
    /// единицей всегда, `await`, которому пришлось ждать, отдавал `MkUnit` в
    /// позицию чужого типа - при том что тот же `await` над уже договорившей
    /// задачей отдавал верное значение (ревью 2026-09-07).
    Parked(Segment, Rc<Value>),
}

/// Файбер очереди.
struct Fiber {
    /// Номер: им задача названа в значении `Task`.
    id: usize,
    /// Корневой ли: его значением питомник и отвечает.
    root: bool,
    state: Suspended,
}

/// Питомник: очередь готовых файберов и ответ корневого.
///
/// Питомник **дожидается** всех - structured concurrency в смысле Trio, на
/// который §5.2 и ссылается: порождённое не переживает своей области видимости.
#[derive(Default)]
pub(crate) struct Nursery {
    /// Готовые к исполнению, в порядке круга.
    queue: Vec<Fiber>,
    /// Ждущие чужого ответа: номер ожидаемого файбера и сам ждущий.
    ///
    /// Ждущий стоит **не** в очереди: круг его не касается, пока ожидаемый не
    /// договорил. Пустая очередь при непустом этом списке и есть взаимная
    /// блокировка - её видно по построению, а не по зависанию.
    blocked: Vec<(usize, Fiber)>,
    /// Ответы договоривших: номер файбера и его значение.
    done: Vec<(usize, Rc<Value>)>,
    /// Ответ корневого файбера, когда он договорил.
    result: Option<Rc<Value>>,
    /// Кто бежит сейчас: номер файбера и корневой ли он.
    running: Option<(usize, bool)>,
    /// Следующий свободный номер файбера.
    next: usize,
}

impl Machine<'_> {
    /// Обслуживает ли операцию питомник. `None` - идти к хендлеру, как обычно.
    ///
    /// # Errors
    ///
    /// Единица не объявлена: запускать приостановленное вычисление нечем.
    pub(crate) fn scheduled(
        &self,
        name: &Name,
        effect: &Name,
        arguments: &[Rc<Value>],
        kont: &mut Kont,
    ) -> Result<Option<Step>, RunError> {
        if !matches!(&**name, SUSPEND | SPAWN | TASK | AWAIT) {
            return Ok(None);
        }
        let Some((link, id)) = kont.nested() else {
            return Ok(None);
        };
        // Ближайший выигрывает - то же правило, по которому выбирается хендлер.
        // Написанный `handle` **внутри** питомника значит ровно то, что написан.
        if let Some((_, handler)) = kont.catching(effect)
            && handler > link
        {
            return Ok(None);
        }
        if &**name == SUSPEND {
            return self.parking(id, link, kont).map(Some);
        }
        // Ведущие аргументы операции - параметры метки, свой идёт за ними.
        let params = match self.signature().lookup(effect).map(|it| &it.kind) {
            Some(DefinitionKind::Effect { params, .. }) => *params as usize,
            _ => return Ok(None),
        };
        let Some(own) = arguments.get(params) else {
            return Ok(None);
        };
        if &**name == AWAIT {
            return self.awaiting(id, link, own, kont).map(Some);
        }
        let task = &**name == TASK;
        self.spawning(id, Rc::clone(own), task, name).map(Some)
    }

    /// Запускает питомник: корневой файбер под свежим кадром.
    pub(crate) fn nursing(&self, body: &Rc<Value>, kont: &mut Kont) -> Result<Step, RunError> {
        let id = {
            let mut table = self.nurseries.borrow_mut();
            table.push(Nursery {
                next: 1,
                ..Nursery::default()
            });
            table.len() - 1
        };
        self.nurseries.borrow_mut()[id].running = Some((0, true));
        self.starting(id, Rc::clone(body), kont)
    }

    /// Файбер отдал значение питомнику: он договорил.
    ///
    /// Ответ корневого запоминается, дальше идёт следующий из очереди. Пустая
    /// очередь означает, что дожидаться больше некого.
    pub(crate) fn nursed(
        &self,
        id: usize,
        value: &Rc<Value>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            let Some((fiber, root)) = nursery.running else {
                return Err(RunError::NoFiber);
            };
            if root {
                nursery.result = Some(Rc::clone(value));
            }
            nursery.done.push((fiber, Rc::clone(value)));
            // Ждавшие его возвращаются в круг: чужой ответ готов - и он же
            // становится тем, чем возобновление им ответит. Единицу тут
            // положить нельзя: `await` объявлен отдающим `a` задачи (§5.2).
            for (awaited, mut waiting) in std::mem::take(&mut nursery.blocked) {
                if awaited == fiber {
                    if let Suspended::Parked(_, answer) = &mut waiting.state {
                        *answer = Rc::clone(value);
                    }
                    nursery.queue.push(waiting);
                } else {
                    nursery.blocked.push((awaited, waiting));
                }
            }
        }
        self.scheduling(id, kont)
    }

    /// Уступка: текущий файбер уходит в хвост очереди, бежит следующий.
    pub(crate) fn parking(
        &self,
        id: usize,
        link: usize,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        // Сегмент включает сам кадр питомника - тем же приёмом, что у хендлера:
        // возобновление ставит его обратно, и файбер снова оказывается под своим
        // питомником, а не под чужим.
        let segment = kont.cut(link);
        let current = self.halted(id, segment)?;
        self.nurseries.borrow_mut()[id].queue.push(current);
        self.scheduling(id, kont)
    }

    /// Ожидание: ждущий уходит из круга, пока ожидаемый не договорит.
    ///
    /// Готовый ответ отдаётся сразу - тогда ждущий и не останавливается.
    fn awaiting(
        &self,
        id: usize,
        link: usize,
        task: &Rc<Value>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        let awaited = fiber_of(task).ok_or(RunError::NoFiber)?;
        if let Some(value) = self.nurseries.borrow()[id]
            .done
            .iter()
            .find(|(fiber, _)| *fiber == awaited)
            .map(|(_, value)| Rc::clone(value))
        {
            return Ok(Step::Return(value));
        }
        let segment = kont.cut(link);
        let current = self.halted(id, segment)?;
        self.nurseries.borrow_mut()[id]
            .blocked
            .push((awaited, current));
        self.scheduling(id, kont)
    }

    /// Снимает бегущий файбер со стека: сегмент и его номер.
    fn halted(&self, id: usize, segment: Segment) -> Result<Fiber, RunError> {
        let mut table = self.nurseries.borrow_mut();
        let nursery = &mut table[id];
        let Some((fiber, root)) = nursery.running else {
            return Err(RunError::NoFiber);
        };
        Ok(Fiber {
            id: fiber,
            root,
            state: Suspended::Parked(segment, self.unit()?),
        })
    }

    /// Порождение: вычисление встаёт в очередь, а звавший бежит дальше.
    ///
    /// `task` - нужен ли звавшему ответ. Тогда значением идёт объявленный
    /// конструктор, применённый к невыразимому имени файбера; иначе единица.
    fn spawning(
        &self,
        id: usize,
        body: Rc<Value>,
        task: bool,
        operation: &Name,
    ) -> Result<Step, RunError> {
        let fiber = {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            let fiber = nursery.next;
            nursery.next += 1;
            nursery.queue.push(Fiber {
                id: fiber,
                root: false,
                state: Suspended::Fresh(body),
            });
            fiber
        };
        if !task {
            return Ok(Step::Return(self.unit()?));
        }
        Ok(Step::Return(self.handle_value(operation, fiber)?))
    }

    /// Значение задачи: конструктор её типа при невыразимом имени файбера.
    ///
    /// Тип берётся из **написанного** результата операции, а не из вшитого
    /// имени: `spawn : … -> Task` называет его сам. Требований к нему два, и
    /// оба проверяются здесь, а не молча предполагаются: один конструктор и
    /// одно поле под номер.
    fn handle_value(&self, operation: &Name, fiber: usize) -> Result<Rc<Value>, RunError> {
        let unsuitable = || RunError::TaskShape {
            operation: operation.to_string(),
        };
        let definition = self.signature().lookup(operation).ok_or_else(unsuitable)?;
        let Some(ty) = result_head(&definition.ty) else {
            return Err(unsuitable());
        };
        // Параметров у семейства быть не должно, и это третье требование, а не
        // придирка: значение собирается спайном из одного применения, а
        // стёртые параметры в спайне обязаны стоять маркерами - как их ставит
        // обычное применение конструктора. Пока их не спрашивали, `data Task
        // (a : Type)` проходило, поле не связывалось, и всякий разбор над
        // задачей выпускал наружу лямбду вместо значения (ревью 2026-09-07).
        //
        // §5.2 пишет `Task eff a`, то есть параметризованную задачу; когда она
        // понадобится, дописывать надо **маркеры в спайн**, а не снимать этот
        // отказ.
        if self
            .signature()
            .lookup(&ty)
            .and_then(adamas_core::sig::Definition::data_shape)
            .is_none_or(|(params, _)| params != 0)
        {
            return Err(unsuitable());
        }
        let Some([only]) = self.signature().constructors(&ty) else {
            return Err(unsuitable());
        };
        let held = self.signature().lookup(only).ok_or_else(unsuitable)?;
        if fields_of(&held.ty) != 1 {
            return Err(unsuitable());
        }
        let marker = Value::constant(
            Rc::from(format!("{FIBER}{fiber}")),
            &[],
            Rc::from([] as [Row<Rc<Value>>; 0]),
            Mults::none(),
        );
        Ok(Rc::new(Value::Neutral(
            Head::Global(
                Rc::clone(only),
                Rc::from([] as [Level; 0]),
                Rc::from([] as [Row<Rc<Value>>; 0]),
                Mults::none(),
            ),
            vec![Elim::App(marker)],
        )))
    }

    /// Снимает один брошенный файбер питомника: его сегмент надо раскрутить.
    ///
    /// Зовётся раскруткой, когда кадр питомника попал в выброшенный сегмент.
    /// По одному, потому что раскрутка одного сегмента - один шаг машины;
    /// снятый обратно не кладётся, поэтому обход конечен. `Fresh` отбрасывается
    /// молча: тело его не начиналось, и закрывать в нём нечего.
    ///
    /// Ждущие чужого ответа брошены наравне с очередью: ответа им теперь не
    /// будет ни от кого.
    pub(crate) fn parked_of(&self, id: usize) -> Option<Segment> {
        let mut table = self.nurseries.borrow_mut();
        let nursery = &mut table[id];
        while let Some(fiber) = nursery.queue.pop() {
            if let Suspended::Parked(segment, _) = fiber.state {
                return Some(segment);
            }
        }
        while let Some((_, fiber)) = nursery.blocked.pop() {
            if let Suspended::Parked(segment, _) = fiber.state {
                return Some(segment);
            }
        }
        None
    }

    /// Следующий файбер очереди либо ответ питомника, если её больше нет.
    fn scheduling(&self, id: usize, kont: &mut Kont) -> Result<Step, RunError> {
        let next = {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            if nursery.queue.is_empty() {
                // Круг пуст, а ждущие есть - ждать им друг друга до конца
                // времён. Видно это по построению, а не по зависанию.
                if !nursery.blocked.is_empty() {
                    return Err(RunError::Deadlock);
                }
                let result = nursery.result.take();
                return match result {
                    Some(value) => Ok(Step::Return(value)),
                    None => Ok(Step::Return(self.unit()?)),
                };
            }
            nursery.queue.remove(0)
        };
        self.nurseries.borrow_mut()[id].running = Some((next.id, next.root));
        match next.state {
            Suspended::Fresh(body) => self.starting(id, body, kont),
            Suspended::Parked(segment, answer) => Ok(Self::waking(segment, answer, kont)),
        }
    }

    /// Запускает ещё не начатый файбер под кадром питомника.
    fn starting(&self, id: usize, body: Rc<Value>, kont: &mut Kont) -> Result<Step, RunError> {
        let unit = self.unit()?;
        kont.push(Frame::Nursery(id));
        Ok(Step::Apply(body, unit))
    }

    /// Возвращает уступивший файбер на стек: сегмент несёт свой кадр питомника.
    fn waking(segment: Segment, answer: Rc<Value>, kont: &mut Kont) -> Step {
        kont.restore(segment);
        // Чем отвечать, решено при парковке: уступка кладёт единицу - тем же
        // ответила бы написанная ветка `suspend -> resume MkUnit`, - а
        // ожидание получает значение дождавшейся задачи, когда та договорит.
        Step::Return(answer)
    }
}

/// Номер файбера из значения задачи. `None` - значение собрано не питомником.
///
/// Читается из **аргумента** конструктора: там стоит невыразимое имя, которое
/// автор написать не может, а разбор `drop (MkTask n)` связывает как обычно.
fn fiber_of(task: &Rc<Value>) -> Option<usize> {
    let Value::Neutral(_, spine) = &**task else {
        return None;
    };
    let Some(Elim::App(argument)) = spine.last() else {
        return None;
    };
    let Value::Neutral(Head::Global(name, ..), _) = &**argument else {
        return None;
    };
    name.strip_prefix(FIBER)?.parse().ok()
}

/// Голова написанного результата определения. `None` - результат не имя.
fn result_head(ty: &Term) -> Option<Name> {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    let mut head = current;
    while let Term::App(callee, _) = head {
        head = callee;
    }
    match head {
        Term::Const(name, ..) => Some(Rc::clone(name)),
        _ => None,
    }
}

/// Сколько полей у конструктора: связывания сверх параметров семейства.
fn fields_of(ty: &Term) -> usize {
    let mut current = ty;
    let mut count = 0;
    while let Term::Pi(binder, _, _, _, codomain) = current {
        if binder.mult != Mult::Zero {
            count += 1;
        }
        current = codomain;
    }
    count
}

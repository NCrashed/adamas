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
//! Три имени, ровно как `Unit`: `nursery` - постулат, чьё тело даёт машина;
//! `suspend` и `spawn` - операции, которые она обслуживает сама. Ни одной новой
//! формы в языке для этого не нужно, объявляет их автор обычным `effect`.
//!
//! Обслуживает она их **только под питомником и только если он ближе хендлера**:
//! написанный `handle` над той же меткой продолжает работать и значит ровно то,
//! что написано. Ближайший выигрывает - то же правило, по которому выбирается
//! хендлер.

use std::rc::Rc;

use adamas_core::sig::DefinitionKind;
use adamas_core::term::Name;
use adamas_core::value::Value;

use crate::RunError;
use crate::frame::{Frame, Kont, Segment};
use crate::machine::{Machine, Step};

/// Имя постулата, запускающего питомник.
pub(crate) const NURSERY: &str = "withNursery";
/// Операция уступки: файбер уходит в хвост очереди.
pub(crate) const SUSPEND: &str = "suspend";
/// Порождение без результата (§5.2, `spawnDetached`): вычисление - файбером.
pub(crate) const SPAWN: &str = "spawnDetached";

/// Приостановленный файбер.
enum Suspended {
    /// Ещё не начатый: приостановленное вычисление, которое запустит питомник.
    Fresh(Rc<Value>),
    /// Уступивший: сегмент стека от кадра питомника до вершины.
    Parked(Segment),
}

/// Файбер очереди.
struct Fiber {
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
    /// Ответ корневого файбера, когда он договорил.
    result: Option<Rc<Value>>,
    /// Корневой ли файбер бежит сейчас.
    running: bool,
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
        if &**name != SUSPEND && &**name != SPAWN {
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
        // Ведущие аргументы операции - параметры метки, тело идёт за ними.
        let params = match self.signature().lookup(effect).map(|it| &it.kind) {
            Some(DefinitionKind::Effect { params, .. }) => *params as usize,
            _ => return Ok(None),
        };
        let Some(body) = arguments.get(params) else {
            return Ok(None);
        };
        self.spawning(id, Rc::clone(body)).map(Some)
    }

    /// Запускает питомник: корневой файбер под свежим кадром.
    pub(crate) fn nursing(&self, body: &Rc<Value>, kont: &mut Kont) -> Result<Step, RunError> {
        let id = {
            let mut table = self.nurseries.borrow_mut();
            table.push(Nursery::default());
            table.len() - 1
        };
        self.nurseries.borrow_mut()[id].running = true;
        self.starting(id, Rc::clone(body), kont)
    }

    /// Файбер отдал значение питомнику: он договорил.
    ///
    /// Ответ корневого запоминается, дальше идёт следующий из очереди. Пустая
    /// очередь означает, что дожидаться больше некого.
    pub(crate) fn nursed(
        &self,
        id: usize,
        value: Rc<Value>,
        kont: &mut Kont,
    ) -> Result<Step, RunError> {
        {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            if nursery.running {
                nursery.result = Some(value);
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
        {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            let root = nursery.running;
            nursery.queue.push(Fiber {
                root,
                state: Suspended::Parked(segment),
            });
        }
        self.scheduling(id, kont)
    }

    /// Порождение: вычисление встаёт в очередь, а звавший бежит дальше.
    pub(crate) fn spawning(&self, id: usize, body: Rc<Value>) -> Result<Step, RunError> {
        self.nurseries.borrow_mut()[id].queue.push(Fiber {
            root: false,
            state: Suspended::Fresh(body),
        });
        Ok(Step::Return(self.unit()?))
    }

    /// Следующий файбер очереди либо ответ питомника, если её больше нет.
    fn scheduling(&self, id: usize, kont: &mut Kont) -> Result<Step, RunError> {
        let next = {
            let mut table = self.nurseries.borrow_mut();
            let nursery = &mut table[id];
            if nursery.queue.is_empty() {
                let result = nursery.result.take();
                return match result {
                    Some(value) => Ok(Step::Return(value)),
                    None => Ok(Step::Return(self.unit()?)),
                };
            }
            nursery.queue.remove(0)
        };
        self.nurseries.borrow_mut()[id].running = next.root;
        match next.state {
            Suspended::Fresh(body) => self.starting(id, body, kont),
            Suspended::Parked(segment) => self.waking(segment, kont),
        }
    }

    /// Запускает ещё не начатый файбер под кадром питомника.
    fn starting(&self, id: usize, body: Rc<Value>, kont: &mut Kont) -> Result<Step, RunError> {
        let unit = self.unit()?;
        kont.push(Frame::Nursery(id));
        Ok(Step::Apply(body, unit))
    }

    /// Возвращает уступивший файбер на стек: сегмент несёт свой кадр питомника.
    fn waking(&self, segment: Segment, kont: &mut Kont) -> Result<Step, RunError> {
        kont.restore(segment);
        // Уступка отвечает единицей - тем же, чем ответила бы написанная ветка
        // `suspend -> resume MkUnit`.
        Ok(Step::Return(self.unit()?))
    }
}

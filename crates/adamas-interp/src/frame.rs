//! Кадр отложенной работы и стек продолжения.
//!
//! Стек здесь **явный**, а не кадры Rust, и это не про глубину одну. Пока
//! продолжение было цепочкой замыканий, всё, что о нём нужно знать, велось
//! рядом: список отложенных деструкторов, долг, отметка «звали ли резумпцию».
//! Сведения о продолжении и само продолжение живут порознь ровно до первого
//! расхождения, и оно случилось трижды.
//!
//! Со стеком резумпция **есть** сегмент кадров. Деструктор в ней виден обходом,
//! а не списком, и рассинхронизировать их нечем: список один.

use std::rc::Rc;

use adamas_core::term::{Case, Name, Term};
use adamas_core::value::{Elim, Env, Value};

/// Ветки хендлера, снятые со спайна элиминатора.
pub(crate) struct Handler {
    /// Метка, которую он снимает.
    pub effect: Name,
    /// Сколько ведущих аргументов операции - параметры метки.
    pub params: usize,
    /// Операции метки в порядке объявления - он же порядок веток.
    pub operations: Rc<[Name]>,
    /// Сколько аргументов связывает ветка каждой операции.
    pub written: Rc<[usize]>,
    /// Ветви в том же порядке.
    pub branches: Rc<[Rc<Value>]>,
    /// Ветвь `return`.
    pub returned: Rc<Value>,
    /// Мультишотна ли резумпция: `handleMulti` против `handle`.
    ///
    /// Различает их элиминатор, и машине разница нужна ровно в одном месте -
    /// можно ли отпустить сегмент после первого возобновления. У аффинной
    /// резумпции второго вызова не бывает по построению (§3.4), и держать её
    /// сегмент до конца прогона незачем.
    pub multi: bool,
}

/// Отложенная работа: чем занять место, когда придёт значение.
///
/// Клонируется дёшево - всё внутри `Rc`, - и это существенно: мультишотная
/// резумпция копирует свой сегмент на каждый вызов.
#[derive(Clone)]
pub(crate) enum Frame {
    /// Считается функция; аргумент ждёт своей очереди.
    Argument(Env, Rc<Term>),
    /// Считается аргумент; функция готова.
    Callee(Rc<Value>),
    /// Считается **функция** - её разворачивают; аргумент готов.
    Forcing(Rc<Value>),
    /// Тело `let` под связыванием.
    Bind(Env, Rc<Term>),
    /// Разбор: считается разбираемое.
    Scrutinee(Env, Rc<Case>),
    /// Тело ветви применяется к полям конструктора по одному.
    Fields(Rc<[Rc<Value>]>, usize),
    /// Проекция поля записи.
    Project(Name),
    /// Поля записи по порядку: написанные, уже посчитанные, номер текущего.
    Object(Env, Rc<[(Name, Rc<Term>)]>, Rc<[(Name, Rc<Value>)]>),
    /// То же для переопределения. База - `None`, пока её саму считают.
    Overriding(
        Env,
        Rc<[(Name, Rc<Term>)]>,
        Rc<[(Name, Rc<Value>)]>,
        Option<Rc<Value>>,
    ),
    /// Спайн развёрнутого определения переигрывается по одному элиминатору.
    Spine(Rc<[Elim]>, usize),
    /// Хендлер, под которым идёт вычисление.
    Handler(Rc<Handler>),
    /// Маска: ближайший хендлер этой метки операция пропускает (§3.4, §10
    /// вопрос 72).
    ///
    /// Кадр стоит **внутри** того хендлера, мимо которого идут: поиск идёт
    /// изнутри наружу, встречает маску раньше и на её счёт пропускает первый
    /// подходящий хендлер. Снимается кадр, когда маскированное вычисление
    /// договорило.
    Masking(Name),
    /// Раскручиваемый хендлер: его метка на время деструкторов (§3.3).
    ///
    /// Ветка обрыва уже дала ответ, и хендлер со стека снят - иначе ветка
    /// работала бы внутри себя. Деструкторы же раскрутки обязаны видеть **тот
    /// же** хендлер, которому погашение отдало их ряд: без этого статика и
    /// динамика расходятся молча, и `fail` деструктора уходит к внешнему
    /// хендлеру вместо своего (ревью 2026-09-05).
    ///
    /// Кадр ставится на время каждого деструктора и метку хендлера
    /// **подавляет**: второй ответ хендлеру деть некуда - первый уже дан
    /// веткой, - поэтому операция, дошедшая сюда, обрывает свой деструктор, а
    /// раскрутка идёт дальше. Прецедент - suppressed exceptions в Java: там
    /// вторичное исключение из `close` тоже не заменяет первичное.
    Suppressing(Name),
    /// Ветка хендлера договорила: пора решать, жив ли остаток.
    Branch(usize),
    /// Scope, держащий ресурс: деструктор ждёт выхода.
    Closing(Rc<Value>),
    /// Деструктор отработал - вернуть значение, ради которого его ждали.
    Closed(Rc<Value>),
    /// Раскрутка выброшенного сегмента: что осталось пройти и что вернуть.
    Unwinding(Segment, usize, Rc<Value>),
    /// Аргументы ветке по одному.
    Passing(Rc<[Rc<Value>]>, usize),
}

/// Что кадр значит для поиска хендлера.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mark {
    /// Хендлер метки.
    Handler,
    /// Маска: пропускает один подходящий хендлер.
    Masking,
    /// Раскручиваемый хендлер: метка на время деструкторов.
    Suppressing,
}

impl Frame {
    /// Метка кадра, если поиск хендлера его различает.
    fn marked(&self) -> Option<(Mark, Name)> {
        match self {
            Self::Handler(handler) => Some((Mark::Handler, Rc::clone(&handler.effect))),
            Self::Masking(name) => Some((Mark::Masking, Rc::clone(name))),
            Self::Suppressing(name) => Some((Mark::Suppressing, Rc::clone(name))),
            _ => None,
        }
    }
}

/// Звено стека: кадры снизу вверх.
type Link = Vec<Frame>;

/// Сегмент продолжения - звенья снизу вверх, первый кадр нижнего есть хендлер.
///
/// Звенья, а не плоский список кадров, и в этом вся стоимость (§10 вопрос 94).
/// Захват сегмента двигает **указатели на звенья**, а не кадры: их единицы, и
/// число их не растёт с глубиной рекурсии. Плоский список копировался целиком -
/// 10000 операций перекладывали 100 020 000 кадров.
#[derive(Clone, Default)]
pub(crate) struct Segment {
    links: Rc<Vec<Link>>,
    total: usize,
}

impl Segment {
    /// Кадров в сегменте.
    pub(crate) fn len(&self) -> usize {
        self.total
    }

    /// Нижний кадр - им стоит хендлер, чей ряд снят.
    pub(crate) fn first(&self) -> Option<&Frame> {
        self.links.first()?.first()
    }

    /// Кадр по сквозной позиции снизу.
    ///
    /// Звенья перебираются, а не индексируются: обход этот идёт только по
    /// раскрутке брошенного сегмента, то есть редко, и звеньев в нём единицы.
    pub(crate) fn at(&self, index: usize) -> &Frame {
        let mut left = index;
        for link in self.links.iter() {
            if left < link.len() {
                return &link[left];
            }
            left -= link.len();
        }
        unreachable!("позиция за пределами сегмента")
    }
}

/// Стек продолжения: снизу вверх, вершина - ближайшая работа.
///
/// **Звеньями, а не одним списком.** Кадр хендлера, маски и раскручиваемого
/// начинает новое звено, поэтому разрез по хендлеру приходится ровно на границу
/// звена - и снимается перекладыванием указателей. Одношотная резумпция
/// возвращает звенья **владением**, то есть тоже даром; мультишотная копирует, и
/// это та самая названная цена, ради которой две формы и различаются.
///
/// Рядом ведётся **указатель меток**: позиции звеньев, которые различает поиск
/// хендлера. Поиск шёл обходом стека до хендлера, то есть по длине сегмента.
#[derive(Default)]
pub(crate) struct Kont {
    links: Vec<Link>,
    marks: Vec<(Mark, Name, usize)>,
}

impl Kont {
    /// Кладёт кадр на вершину.
    pub(crate) fn push(&mut self, frame: Frame) {
        if let Some((mark, name)) = frame.marked() {
            self.marks.push((mark, name, self.links.len()));
            self.links.push(vec![frame]);
            return;
        }
        match self.links.last_mut() {
            Some(link) => link.push(frame),
            None => self.links.push(vec![frame]),
        }
    }

    /// Снимает вершину.
    pub(crate) fn pop(&mut self) -> Option<Frame> {
        let link = self.links.last_mut()?;
        let frame = link.pop()?;
        if link.is_empty() {
            self.links.pop();
            if frame.marked().is_some() {
                self.marks.pop();
            }
        }
        Some(frame)
    }

    /// Кладёт кадр **под** вершину: сперва сработает верхний, потом этот.
    ///
    /// Меткой такой кадр не бывает - это `Forcing`, `Project` и `Scrutinee`.
    /// Вершина же бывает, и тогда класть надо в предыдущее звено: метка стоит
    /// первым кадром своего, и под неё в нём места нет.
    pub(crate) fn tuck(&mut self, frame: Frame) {
        debug_assert!(frame.marked().is_none(), "под вершину кладут не метку");
        let last = self.links.len();
        if let Some(link) = self.links.last_mut()
            && link.len() >= 2
        {
            link.insert(link.len() - 1, frame);
            return;
        }
        if last >= 2 {
            self.links[last - 2].push(frame);
            return;
        }
        self.links.insert(0, vec![frame]);
        for mark in &mut self.marks {
            mark.2 += 1;
        }
    }

    /// Обрезает стек по звено `link` включительно.
    pub(crate) fn truncate(&mut self, link: usize) {
        self.links.truncate(link);
        self.marks.retain(|(_, _, at)| *at < link);
    }

    /// Снимает сегмент от звена `link` до вершины.
    pub(crate) fn cut(&mut self, link: usize) -> Segment {
        let links: Vec<Link> = self.links.drain(link..).collect();
        let total = links.iter().map(Vec::len).sum();
        self.marks.retain(|(_, _, at)| *at < link);
        Segment {
            links: Rc::new(links),
            total,
        }
    }

    /// Ставит сегмент обратно на вершину.
    ///
    /// Владением, если сегмент больше никому не нужен, - это одношотный случай,
    /// и он даром. Мультишотный копирует: повтор и есть его смысл.
    pub(crate) fn restore(&mut self, segment: Segment) {
        let Segment { links, .. } = segment;
        let base = self.links.len();
        match Rc::try_unwrap(links) {
            Ok(owned) => self.links.extend(owned),
            Err(shared) => self.links.extend(shared.iter().cloned()),
        }
        for (offset, link) in self.links[base..].iter().enumerate() {
            if let Some((mark, name)) = link.first().and_then(Frame::marked) {
                self.marks.push((mark, name, base + offset));
            }
        }
    }

    /// Ближайший хендлер метки с учётом масок. `None` - его нет.
    ///
    /// Маски считаются по дороге наружу: каждая пропускает один подходящий
    /// хендлер. Стоят они внутри того, мимо кого идут, поэтому поиск изнутри
    /// встречает их раньше - и счёт получается сам собой (§10 вопрос 72).
    pub(crate) fn catching(&self, effect: &Name) -> Option<(Mark, usize)> {
        let mut masked = 0usize;
        for (mark, name, at) in self.marks.iter().rev() {
            if name != effect {
                continue;
            }
            match mark {
                Mark::Masking => masked += 1,
                Mark::Handler | Mark::Suppressing => {
                    if masked > 0 {
                        masked -= 1;
                    } else {
                        return Some((*mark, *at));
                    }
                }
            }
        }
        None
    }

    /// Первый кадр звена - им стоит метка, которую отдал [`Kont::catching`].
    pub(crate) fn guard(&self, link: usize) -> &Frame {
        &self.links[link][0]
    }
}

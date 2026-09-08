//! `Flat` - класс представления и структурный вывод его инстансов (§4.11).
//!
//! Класс объявляется программой, как объявляются `Bool` для `if` и `Zero` со
//! `Succ` для литерала: ядро имени `Flat` не знает, а сахар без него не
//! разворачивается. Всё остальное делает компилятор - **инстансы руками не
//! пишутся**, и объявление такого инстанса отвергается.
//!
//! # Почему вывод, а не реестр
//!
//! Инстанс `Flat` не выбирается: он вычисляется по представлению типа, и
//! ответ у типа один. Поэтому кандидат сюда не кладётся вовсе - разрешение
//! зовёт вывод, а тот отвечает словарём либо отказом. Отсюда же когерентность
//! по построению (§4.11): выбирать нечего, значит и разъехаться нечему, и
//! запрет §4.8 на class-констрейнты в запечатывающей сигнатуре сюда не
//! распространяется - он охраняет от осадки **выбора**.
//!
//! # Что здесь не считается
//!
//! Примитивов в языке ещё нет (§4.3, §4.9 - Фаза 6), поэтому база вывода
//! сегодня - тег семейства: `data` из двух пустых конструкторов занимает байт,
//! и из таких байтов складывается всё прочее. Правила укладки от этого не
//! зависят: они те же, что в §4.11, и на примитивных размерах дают названные
//! там числа - `Vec3` из трёх `Float32` в 12 байт при выравнивании 4,
//! `Option Int64` в 16 байт, а не в 8.

use std::rc::Rc;

use adamas_core::check::check_within;
use adamas_core::conv::whnf_solved;
use adamas_core::ctx::Ctx;
use adamas_core::eval::eval;
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Env, Head, Lvl, Telescope, Value};
use adamas_parser::ast::Symbol;

use crate::class::{abstracted, binders_of};
use crate::error::ElabError;
use crate::expr::{SUCC, ZERO};
use crate::own::Owned;

/// Имя класса представления. Соглашение то же, каким `if` берёт `Bool`.
pub(crate) const FLAT: &str = "Flat";

/// Единственный метод класса: дескриптор укладки.
pub(crate) const LAYOUT: &str = "layout";

/// Поля дескриптора - как они написаны в §4.11.
const SIZE: &str = "size";
const ALIGN: &str = "align";

/// Укладка значения: сколько байт занимает и по какой границе стоит.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Layout {
    /// Размер в байтах.
    size: u32,
    /// Выравнивание в байтах. Не меньше единицы: нулевое не делит ничего.
    align: u32,
}

impl Layout {
    /// Пустая укладка: ни байта, ни требований к границе.
    const EMPTY: Self = Self { size: 0, align: 1 };

    /// Укладка примитива: выравнивание по его же размеру.
    #[cfg(test)]
    const fn primitive(size: u32) -> Self {
        Self { size, align: size }
    }
}

/// Ближайшее сверху кратное `align`.
fn aligned(offset: u32, align: u32) -> u32 {
    let align = align.max(1);
    offset.next_multiple_of(align)
}

/// Поля подряд: каждое встаёт по своей границе, размер округляется до общей.
///
/// Это и есть правило §4.11 для записи и для конструктора: «укладка
/// последовательная, выравнивание по максимальному `align` полей».
fn sequential(fields: &[Layout]) -> Layout {
    let mut size = 0;
    let mut align = 1;
    for field in fields {
        size = aligned(size, field.align).saturating_add(field.size);
        align = align.max(field.align);
    }
    Layout {
        size: aligned(size, align),
        align,
    }
}

/// Ширина тега: сколько байт нужно, чтобы различить `count` конструкторов.
///
/// Один конструктор тега не требует вовсе - различать нечего, и `data` с ним
/// укладывается как запись (§4.11). Пустое семейство тем же счётом занимает
/// ноль байт: значений у него нет, и укладывать нечего.
///
/// Ширина растёт ступенями по степеням двойки - §4.11 её не называет, потому
/// что перечисления из трёхсот конструкторов в примерах не встречается. Правило
/// здесь названо, чтобы укладка оставалась правилом, а не результатом анализа.
fn tag(count: usize) -> Layout {
    match count {
        0 | 1 => Layout::EMPTY,
        2..=256 => Layout { size: 1, align: 1 },
        257..=65536 => Layout { size: 2, align: 2 },
        _ => Layout { size: 4, align: 4 },
    }
}

/// Тег плюс payload размера максимума (§4.11).
///
/// Названная там цена воспроизводится числом: `Option Int64` занимает 16 байт,
/// а не 8, потому что payload встаёт по своей границе, а перед ним стоит тег.
fn tagged(count: usize, payload: Layout) -> Layout {
    let tag = tag(count);
    if tag.size == 0 {
        return payload;
    }
    let align = tag.align.max(payload.align);
    let offset = aligned(tag.size, payload.align);
    Layout {
        size: aligned(offset.saturating_add(payload.size), align),
        align,
    }
}

/// Наибольшая из двух укладок - по каждой мерке отдельно.
fn widest(left: Layout, right: Layout) -> Layout {
    Layout {
        size: left.size.max(right.size),
        align: left.align.max(right.align),
    }
}

/// Почему тип не плоский. Перечень - §4.11, «Не `Flat`».
#[derive(Clone, Copy, Debug)]
enum Why {
    /// Функция или замыкание.
    Closure,
    /// Семейство рекурсивно: уравнения на размер у него нет.
    Recursive,
    /// `unique data` либо `resource` (§3.3).
    Owned,
    /// Представление неизвестно: постулат либо запечатанное.
    Abstract,
    /// Переменная: чем она окажется, здесь неизвестно.
    Rigid,
    /// Открытая запись: полей у неё не перечислить.
    Open,
    /// Значений у этого нет вовсе - укладывать нечего.
    Alien,
    /// Вложенность кончилась раньше представления.
    Deep,
}

impl Why {
    /// Хвост сообщения - после «он» либо «она». Род подлежащего зависит от
    /// того, названо ли место именем, поэтому причина, встречающаяся в обоих
    /// видах, написана без согласования по роду; рекурсия, владение и
    /// абстрактность бывают только про названный тип, а замыкание и
    /// переменная - только про безымянную форму, и там род известен.
    const fn face(self) -> &'static str {
        match self {
            Self::Closure => "несёт замыкание, то есть указатель наружу",
            Self::Recursive => "рекурсивен, и размер значения ничем не ограничен",
            Self::Owned => "владеемый (§3.3), а такое значение живёт в куче",
            Self::Abstract => {
                "объявлен без представления: тела нет либо оно запечатано; \
                 словарь запечатанного берётся значением - членом его сигнатуры \
                 вида `flat : Flat T` (§4.11)"
            }
            Self::Rigid => "ещё ничем не определена - напишите `{Flat …}` в контексте",
            Self::Open => "оставляет хвост открытым, и полей в нём не перечислить",
            Self::Alien => "значений не имеет, и укладывать нечего",
            Self::Deep => "уходит глубже, чем вывод готов идти",
        }
    }
}

/// Сколько полей вглубь разрешено уйти выводу.
///
/// Обход конечен и без предела: рекурсия ловится по объявлению, а вложенность
/// применений ограничена самой целью. Предел стоит **страховкой**: дыра в
/// первом даёт не отказ, а переполнение стека, то есть падение компилятора на
/// пользовательской программе. Порядок величины тот же, что у предела
/// вложенности контекстов инстансов.
const DEPTH_LIMIT: u32 = 64;

/// Слово вместо имени - в двух падежах, которых требует сообщение.
///
/// Все слова женского рода: с ним согласованы причины, которые про безымянные
/// формы и бывают.
#[derive(Clone, Copy, Debug)]
struct Word {
    /// Подлежащим: «это функция».
    one: &'static str,
    /// После «для»: «не выводится для функции».
    of: &'static str,
}

/// Функция или лямбда.
const FUNCTION: Word = Word {
    one: "функция",
    of: "функции",
};

/// Тип-запись.
const RECORD: Word = Word {
    one: "запись",
    of: "записи",
};

/// Связывание контекста либо нерешённая дырка.
const VARIABLE: Word = Word {
    one: "переменная",
    of: "переменной",
};

/// Универсум.
const UNIVERSE: Word = Word {
    one: "вселенная",
    of: "вселенной",
};

/// Всё прочее: значений у него нет.
const FORM: Word = Word {
    one: "форма",
    of: "формы",
};

/// Как тип назван в сообщении.
#[derive(Clone, Debug)]
enum Shown {
    /// Определение: пишется в кавычках, и по имени его сравнивают.
    Named(Symbol),
    /// Форма, имени не имеющая.
    Word(Word),
}

impl Shown {
    /// Подлежащим либо после «типа».
    fn text(&self) -> String {
        match self {
            Self::Named(name) => format!("`{name}`"),
            Self::Word(word) => word.one.to_owned(),
        }
    }

    /// После «для»: так называется тип, о котором спросили.
    fn asked(&self) -> Symbol {
        match self {
            Self::Named(name) => Rc::from(format!("`{name}`").as_str()),
            Self::Word(word) => Rc::from(word.of),
        }
    }

    /// Имя определения, если оно есть.
    const fn name(&self) -> Option<&Symbol> {
        match self {
            Self::Named(name) => Some(name),
            Self::Word(_) => None,
        }
    }
}

/// Отказ вывода вместе с тем, где он случился.
struct Blame {
    /// Владелец и поле, на котором вывод остановился. `None` - сам тип, о
    /// котором спросили.
    at: Option<(Shown, Symbol)>,
    /// Тип, оказавшийся не плоским.
    found: Shown,
    why: Why,
}

impl Blame {
    /// Отказ про сам тип.
    const fn alone(found: Shown, why: Why) -> Self {
        Self {
            at: None,
            found,
            why,
        }
    }

    /// Приписывает отказу поле, чей тип и оказался не плоским.
    ///
    /// `of` - тип этого поля. Место переезжает наружу ровно до него: у `Node` с
    /// полем `Nat` указать надо на поле `Node`, а не на рекурсию внутри `Nat`,
    /// которую автор не правит. Дальше место не едет - поле типа `Node` уже
    /// названо своим, и §4.11 требует именно конкретного поля.
    fn located(mut self, owner: &Shown, field: Symbol, of: &Shown) -> Self {
        let same = matches!((of.name(), self.found.name()), (Some(it), Some(found)) if it == found);
        if self.at.is_none() || same {
            self.at = Some((owner.clone(), field));
        }
        self
    }

    /// Отказ элаборации: `ty` - тип, для которого искался словарь.
    fn into_error(self, ty: &Shown, span: Span) -> ElabError {
        let why = match &self.at {
            None => match &self.found {
                Shown::Named(_) => format!("он {}", self.why.face()),
                Shown::Word(_) => format!("она {}", self.why.face()),
            },
            Some((owner, field)) => {
                // Имя владельца пишется, только если оно не то же самое: «поле
                // 1 конструктора `MkBox` типа `Box`» у самого `Box` повторяет
                // уже сказанное.
                let of = match (owner.name(), ty.name()) {
                    (Some(it), Some(asked)) if it == asked => String::new(),
                    _ => format!(" типа {}", owner.text()),
                };
                match &self.found {
                    Shown::Named(name) => {
                        format!("{field}{of} имеет тип `{name}`, а он {}", self.why.face())
                    }
                    Shown::Word(word) => {
                        format!("{field}{of} - это {}, а она {}", word.one, self.why.face())
                    }
                }
            }
        };
        ElabError::NotFlat {
            ty: ty.asked(),
            why: Rc::from(why.as_str()),
            span,
        }
    }
}

/// Словарь `Flat τ`, выведенный структурно, - решение дырки разрешения.
///
/// `ty` - тип дырки: телескоп, оканчивающийся целью; `goal` - сама цель,
/// приведённая к нормальной форме под этим телескопом.
///
/// # Errors
///
/// Тип не плоский - отказ называет поле; либо класс объявлен не так, как
/// написано в §4.11.
pub(crate) fn derive(
    signature: &Signature,
    metas: &mut Metas,
    owned: &Owned,
    ty: &Term,
    goal: &Term,
    span: Span,
) -> Result<Rc<Value>, ElabError> {
    let binders = binders_of(ty);
    let mut ctx = Ctx::new(signature);
    for (mult, name, domain) in &binders {
        let value = ctx.eval(domain);
        ctx = ctx.bind(Rc::clone(name), *mult, value);
    }
    // Цель - применение класса к единственному аргументу: форму `class Flat a`
    // проверяет объявление, поэтому здесь она уже такая.
    let Term::App(_, argument) = goal else {
        return Err(ElabError::FlatShape {
            why: "класс `Flat` объявляется одним параметром (§4.11)",
            span,
        });
    };
    let subject = ctx.eval(argument);
    let mut walk = Walk {
        signature,
        owned,
        level: ctx.size(),
        depth: 0,
    };
    let asked = shown(&subject, &subject);
    let layout = walk
        .layout(metas, &subject)
        .map_err(|blame| blame.into_error(&asked, span))?;
    let dictionary = descriptor(signature, metas, layout, span)?;
    let solution = abstracted(&binders, dictionary);
    // Проверка связывает аргументы уровня у `Zero` и `Succ`: цель полиморфна по
    // уровню, а числа - нет, и решить их дырки может только это сравнение (тот
    // же порядок, что у реализации сигнатуры в `class::implementing`).
    check_within(&Ctx::new(signature), metas, &solution, ty).map_err(|_| ElabError::FlatShape {
        why: "словарь `Flat` не сошёлся с объявленным классом: метод у него один - \
              `layout : Layout`, а `Layout` есть `{ size : Nat, align : Nat }` (§4.11)",
        span,
    })?;
    Ok(eval(&Env::default(), &solution))
}

/// Словарь `{ layout = { size = …, align = … } }` термом.
///
/// Числа записываются `Zero` и `Succ` - тем же соглашением, каким
/// разворачивается литерал (§4.3): примитивного числа в ядре нет.
fn descriptor(
    signature: &Signature,
    metas: &mut Metas,
    layout: Layout,
    span: Span,
) -> Result<Term, ElabError> {
    let missing = ElabError::FlatShape {
        why: "вывод `Flat` записывает размер числом, а `Zero` и `Succ` не объявлены (§4.3)",
        span,
    };
    let (Some(zero), Some(successor)) = (
        signature.instantiate(ZERO, metas),
        signature.instantiate(SUCC, metas),
    ) else {
        return Err(missing);
    };
    let numeral = |value: u32| {
        (0..value).fold(zero.clone(), |built, _| {
            Term::App(Rc::new(successor.clone()), Rc::new(built))
        })
    };
    let written = Term::Object(Rc::from([
        (Name::from(SIZE), Rc::new(numeral(layout.size))),
        (Name::from(ALIGN), Rc::new(numeral(layout.align))),
    ]));
    Ok(Term::Object(Rc::from([(
        Name::from(LAYOUT),
        Rc::new(written),
    )])))
}

/// Обход представления: тип в укладку либо в отказ.
struct Walk<'a> {
    signature: &'a Signature,
    owned: &'a Owned,
    /// Свободный уровень: им связываются поля, чтобы читать следующие.
    level: u32,
    /// Сколько полей пройдено вглубь.
    depth: u32,
}

impl Walk<'_> {
    /// Укладка типа. Отказ несёт причину и место.
    fn layout(&mut self, metas: &Metas, ty: &Rc<Value>) -> Result<Layout, Blame> {
        let value = whnf_solved(self.signature, metas, ty);
        let shown = shown(ty, &value);
        if self.depth >= DEPTH_LIMIT {
            return Err(Blame::alone(shown, Why::Deep));
        }
        match &*value {
            Value::Pi(..) | Value::Lam(..) => Err(Blame::alone(shown, Why::Closure)),
            Value::Record(telescope) => self.record(metas, &shown, telescope),
            Value::Neutral(Head::Global(name, ..), spine) => {
                self.global(metas, &shown, name, spine)
            }
            Value::Neutral(..) => Err(Blame::alone(shown, Why::Rigid)),
            _ => Err(Blame::alone(shown, Why::Alien)),
        }
    }

    /// Укладка поля - на шаг глубже.
    fn deeper(&mut self, metas: &Metas, ty: &Rc<Value>) -> Result<Layout, Blame> {
        self.depth = self.depth.saturating_add(1);
        let found = self.layout(metas, ty);
        self.depth = self.depth.saturating_sub(1);
        found
    }

    /// Запись: поля подряд (§4.11).
    fn record(
        &mut self,
        metas: &Metas,
        owner: &Shown,
        telescope: &Telescope,
    ) -> Result<Layout, Blame> {
        if telescope.is_open() {
            return Err(Blame::alone(owner.clone(), Why::Open));
        }
        let mut earlier = Vec::with_capacity(telescope.fields().len());
        let mut fields = Vec::with_capacity(telescope.fields().len());
        for (index, field) in telescope.fields().iter().enumerate() {
            let ty = telescope.at(index, &earlier);
            earlier.push(Value::var(Lvl(self.level)));
            self.level = self.level.saturating_add(1);
            // Стёртое поле рантайма не занимает - укладывать нечего.
            if field.mult == Mult::Zero {
                continue;
            }
            let of = shown(&ty, &ty);
            let inner = self.deeper(metas, &ty).map_err(|blame| {
                blame.located(
                    owner,
                    Rc::from(format!("поле `{}`", field.name).as_str()),
                    &of,
                )
            })?;
            fields.push(inner);
        }
        Ok(sequential(&fields))
    }

    /// Определение в голове: семейство укладывается, всё прочее - нет.
    fn global(
        &mut self,
        metas: &Metas,
        owner: &Shown,
        name: &Name,
        spine: &[adamas_core::value::Elim],
    ) -> Result<Layout, Blame> {
        if self.owned.how(name).is_some() {
            return Err(Blame::alone(owner.clone(), Why::Owned));
        }
        let Some((params, _)) = self.signature.lookup(name).and_then(|it| it.data_shape()) else {
            // Постулат или запечатанное: `whnf` его не развернул, и знать о
            // представлении здесь нечего.
            return Err(Blame::alone(owner.clone(), Why::Abstract));
        };
        if recursive(self.signature, name) {
            return Err(Blame::alone(owner.clone(), Why::Recursive));
        }
        let arguments: Vec<Rc<Value>> = spine
            .iter()
            .filter_map(|elim| match elim {
                adamas_core::value::Elim::App(argument) => Some(Rc::clone(argument)),
                _ => None,
            })
            .collect();
        if arguments.len() < params as usize {
            return Err(Blame::alone(owner.clone(), Why::Alien));
        }
        let constructors: Vec<Name> = self
            .signature
            .constructors(name)
            .unwrap_or_default()
            .to_vec();
        let mut payload = Layout::EMPTY;
        for constructor in &constructors {
            let fields = self.fields(constructor, &arguments, params);
            let mut written = Vec::with_capacity(fields.len());
            for (at, (field, ty)) in fields.iter().enumerate() {
                let of = shown(ty, ty);
                let inner = self
                    .deeper(metas, ty)
                    .map_err(|blame| blame.located(owner, position(field, at, constructor), &of))?;
                written.push(inner);
            }
            payload = widest(payload, sequential(&written));
        }
        Ok(tagged(constructors.len(), payload))
    }

    /// Поля конструктора при подставленных параметрах семейства.
    ///
    /// Стёртые связывания полями не считаются: индекс семейства и собственный
    /// параметр конструктора в рантайме отсутствуют (§3.3), а укладка - про
    /// рантайм.
    fn fields(
        &mut self,
        constructor: &Name,
        arguments: &[Rc<Value>],
        params: u32,
    ) -> Vec<(Name, Rc<Value>)> {
        let Some(definition) = self.signature.lookup(constructor) else {
            return Vec::new();
        };
        // Аргументы стёртых сортов вывод не читает: укладка от уровня, ряда и
        // кратности не зависит, а подставить что-то обязан всякий, кто берёт
        // тип определения.
        let levels: Vec<Level> = vec![Level::Zero; definition.level_arity as usize];
        let rows: Vec<Row<Term>> = vec![Row::empty(); definition.row_arity as usize];
        let mults: Vec<Mult> = definition
            .mult_allowed
            .iter()
            .map(|allowed| allowed.first().copied().unwrap_or(Mult::Many))
            .collect();
        let mut current = definition.instantiate_type(&levels, &rows, &mults);
        for argument in arguments.iter().take(params as usize) {
            let Value::Pi(_, _, _, _, codomain) = &*Rc::clone(&current) else {
                return Vec::new();
            };
            current = codomain.apply(Rc::clone(argument));
        }
        let mut found = Vec::new();
        while let Value::Pi(binder, name, domain, _, codomain) = &*Rc::clone(&current) {
            if binder.mult != Mult::Zero {
                found.push((Rc::clone(name), Rc::clone(domain)));
            }
            let bound = Value::var(Lvl(self.level));
            self.level = self.level.saturating_add(1);
            current = codomain.apply(bound);
        }
        found
    }
}

/// Ссылается ли представление семейства на само себя.
///
/// Свойство **объявления**, а не применения: §4.11 называет не плоским `List`
/// как таковой, а не `List Nat` отдельно от `List Bit`. Ровно поэтому его и
/// нельзя считать стеком обхода: `Box (Box Bit)` прошёл бы по имени за
/// рекурсию, хотя вложен конечно и укладывается в байт.
///
/// Косвенная рекурсия ловится тем же: достижимость идёт по всем именам, которые
/// стоят в полях, - через соседа по группе, через синоним, через запись. Обход
/// конечен, потому что имён в сигнатуре конечное число.
fn recursive(signature: &Signature, of: &Name) -> bool {
    let mut seen: Vec<Name> = Vec::new();
    let mut queue = mentioned(signature, of);
    while let Some(name) = queue.pop() {
        if name == *of {
            return true;
        }
        if seen.contains(&name) {
            continue;
        }
        queue.extend(mentioned(signature, &name));
        seen.push(name);
    }
    false
}

/// Имена, стоящие в представлении определения.
///
/// У семейства это поля конструкторов, у синонима и записи - тело. Стёртые
/// связывания не считаются: индекс семейства в рантайме отсутствует (§3.3), а
/// речь о представлении.
fn mentioned(signature: &Signature, name: &Name) -> Vec<Name> {
    let mut found = Vec::new();
    let Some(definition) = signature.lookup(name) else {
        return found;
    };
    if definition.data_shape().is_some() {
        for constructor in signature.constructors(name).unwrap_or_default() {
            let Some(declared) = signature.lookup(constructor) else {
                continue;
            };
            let mut current = &declared.ty;
            while let Term::Pi(binder, _, domain, _, codomain) = current {
                if binder.mult != Mult::Zero {
                    constants(domain, &mut found);
                }
                current = codomain;
            }
            // Заключение конструктора не читается: оно называет само семейство,
            // и всякое семейство оказалось бы рекурсивным.
        }
    } else if let Some(body) = &definition.body {
        constants(body, &mut found);
    }
    found
}

/// Имена определений, стоящие в терме.
fn constants(term: &Term, into: &mut Vec<Name>) {
    match term {
        Term::Const(name, ..) => into.push(Rc::clone(name)),
        Term::Var(_) | Term::Universe(_) | Term::RowKind(_) | Term::EffectKind | Term::Meta(_) => {}
        Term::Record(fields) | Term::Row(fields) => {
            for field in fields.iter() {
                constants(&field.ty, into);
            }
            if let Some(tail) = &fields.tail {
                constants(tail, into);
            }
        }
        Term::Object(fields) => {
            for (_, value) in fields.iter() {
                constants(value, into);
            }
        }
        Term::With(base, fields) => {
            constants(base, into);
            for (_, value) in fields.iter() {
                constants(value, into);
            }
        }
        Term::Project(record, _) => constants(record, into),
        Term::Lam(_, _, body) => constants(body, into),
        Term::App(callee, argument) => {
            constants(callee, into);
            constants(argument, into);
        }
        Term::Pi(_, _, domain, row, codomain) => {
            constants(domain, into);
            constants(codomain, into);
            for label in row.labels() {
                for argument in &label.arguments {
                    constants(argument, into);
                }
            }
        }
        Term::Let(_, _, ty, value, body) => {
            constants(ty, into);
            constants(value, into);
            constants(body, into);
        }
        Term::Case(case) => {
            constants(&case.scrutinee, into);
            constants(&case.motive, into);
            for branch in &case.branches {
                constants(&branch.body, into);
            }
        }
    }
}

/// Как назвать поле в сообщении: именем, если оно написано, иначе номером.
fn position(field: &Name, at: usize, constructor: &Name) -> Symbol {
    let shown = if &**field == "_" {
        format!("{}", at + 1)
    } else {
        format!("`{field}`")
    };
    Rc::from(format!("поле {shown} конструктора `{constructor}`").as_str())
}

/// Как назвать тип в сообщении.
///
/// Читается **написанное**: `type Handle = …` в отказе полезнее развёрнутого
/// представления. Развёрнутое берётся, только если у написанного имени нет.
fn shown(before: &Rc<Value>, after: &Rc<Value>) -> Shown {
    if let Some(name) = named(before).or_else(|| named(after)) {
        return Shown::Named(name);
    }
    Shown::Word(match &**after {
        Value::Pi(..) | Value::Lam(..) => FUNCTION,
        Value::Record(..) => RECORD,
        Value::Universe(..) => UNIVERSE,
        Value::Neutral(Head::Local(..) | Head::Meta(..), _) => VARIABLE,
        _ => FORM,
    })
}

/// Имя головы, если она определение.
fn named(value: &Rc<Value>) -> Option<Symbol> {
    match &**value {
        Value::Neutral(Head::Global(name, ..), _) => Some(Rc::clone(name)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{Layout, sequential, tagged};

    /// Числа §4.11 воспроизводятся правилом, а не пересказываются.
    ///
    /// `Vec3` из трёх `Float32` - 12 байт при выравнивании 4; поля идут подряд,
    /// и дырок между ними нет.
    #[test]
    fn a_record_of_primitives_lies_end_to_end() {
        let float = Layout::primitive(4);
        assert_eq!(
            sequential(&[float, float, float]),
            Layout { size: 12, align: 4 }
        );
    }

    /// Хендл §4.11 - два `UInt32`, восемь байт.
    #[test]
    fn a_handle_takes_eight_bytes() {
        let word = Layout::primitive(4);
        assert_eq!(sequential(&[word, word]), Layout { size: 8, align: 4 });
    }

    /// Цена, названная §4.11: `Option Int64` занимает 16 байт, а не 8.
    ///
    /// Тег стоит перед payload, payload встаёт по своей границе - отсюда
    /// семь байт заполнителя, которых не было бы у niche-оптимизации. Она §4.11
    /// стартово отвергнута, и это число - её цена.
    #[test]
    fn a_tagged_union_pays_for_its_tag() {
        let payload = Layout::primitive(8);
        assert_eq!(tagged(2, payload), Layout { size: 16, align: 8 });
    }

    /// Один конструктор тега не требует: различать нечего.
    #[test]
    fn a_single_constructor_carries_no_tag() {
        let payload = Layout::primitive(4);
        assert_eq!(tagged(1, payload), payload);
    }

    /// Перечисление без полей - один байт тега.
    #[test]
    fn an_enumeration_is_its_tag() {
        assert_eq!(tagged(2, Layout::EMPTY), Layout { size: 1, align: 1 });
    }

    /// Тег растёт вместе с числом конструкторов.
    #[test]
    fn a_wide_enumeration_widens_its_tag() {
        assert_eq!(tagged(256, Layout::EMPTY), Layout { size: 1, align: 1 });
        assert_eq!(tagged(257, Layout::EMPTY), Layout { size: 2, align: 2 });
    }
}

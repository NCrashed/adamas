//! Выражения и паттерны поверхностного языка в термы ядра.
//!
//! Границы фрагмента и причина каждой - в [`crate`] и в [`Missing`]; правило
//! регистра - у [`is_reference`]. Здесь - сами правила элаборации, по одному
//! на форму, и то, что из них следует: тому же порядку следует обратный проход
//! маршрута ([`crate::route`]).

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::check::{infer, is_type};
use adamas_core::ctx::Ctx;
use adamas_core::eval::{eval, quote};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern as CorePattern, PatternError, compile};
use adamas_core::row::Row;
use adamas_core::sig::{Definition, DefinitionKind, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Binder, Field as CoreField, Fields, Name as CoreName, Term};
use adamas_core::value::{Env, Value};
use adamas_parser::ast::{
    self, Binding, Block, Expr, ExprKind, LamParamKind, Pattern, PatternKind, Stmt, StmtKind,
    Symbol, Visibility,
};

use crate::error::{ElabError, Missing};
use crate::live;
use crate::own::Owned;

/// Разбирает ли имя (заглавное) или связывает (строчное).
///
/// §4.1: заглавное имя ссылается на объявленное - в паттерне разбирает, в типе
/// обязано быть известным; строчное связывает. Правило локально, поэтому чтобы
/// прочитать клаузу, не нужно знать, что объявлено выше, и опечатка в имени
/// конструктора называется там, где написана, вместо переменной, ловящей всё.
///
/// Письменности без регистра попадают в «строчные»: конструкторов ими не
/// назвать, и это названная цена решения от 2026-08-25.
#[must_use]
pub fn is_reference(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_uppercase)
}

/// Поднятое в implicit-параметр имя (§4.1, §4.2).
///
/// Свободное имя типа и row-переменная записи поднимаются одним механизмом и
/// различаются только сортом связывания: у первого - дырка, у второй -
/// `Row ℓ`.
struct Lifted {
    /// Имя, под которым связывание встанет в телескоп.
    name: Symbol,
    /// Ряд ли это.
    row: bool,
}

/// Сколько записей написано в сигнатуре на верхнем уровне.
///
/// Каждая получает свою row-переменную (§4.2: auto-lift в позиции аргумента и
/// результата). Вложенная в другую запись не считается: там она поле, а поле -
/// это тип, и закрывает его та же запись, что его объявила.
fn written_rows(expr: &Expr) -> usize {
    match &expr.kind {
        ExprKind::RecordType(_) => 1,
        ExprKind::App(left, right)
        | ExprKind::TypeApp(left, right)
        | ExprKind::Arrow(left, right) => written_rows(left) + written_rows(right),
        ExprKind::Pi { binders, codomain } => {
            binders
                .iter()
                .filter_map(|it| it.ty.as_ref())
                .map(written_rows)
                .sum::<usize>()
                + written_rows(codomain)
        }
        _ => 0,
    }
}

/// Параметр семейства - уже элаборированный.
///
/// Живёт отдельно от [`ast::Binder`], потому что переиспользуется: kind и все
/// конструкторы обязаны нести один и тот же телескоп, а элаборация написанного
/// дважды дала бы два разных набора дырок уровня.
pub(crate) struct Param {
    /// Кратность параметра - написанная либо `ω` по умолчанию (§4.1).
    pub mult: Mult,
    /// Имя, каким оно написано: под ним параметр виден в типах конструкторов.
    pub name: Symbol,
    /// Тип параметра. `data Pair a b` его не пишет, и там стоит дырка.
    pub ty: Rc<Term>,
}

/// Член объявляемой группы (§10 вопрос 50).
///
/// Пока группа объявляется, в сигнатуре её нет, а ссылаться на членов надо:
/// конструктор называет своё семейство, тело определения - само определение.
/// Значит всё, что о члене знает вставка имени, приходит отсюда.
pub(crate) struct Member {
    /// Имя, каким оно написано.
    pub name: Symbol,
    /// Аргументы уровня - общие на всё объявление; их считает вызывающий
    /// обобщением по типу члена, и это §10 вопрос 63.
    pub levels: Rc<[Level]>,
    /// Уже элаборированный тип. По нему вставляются имплиситы: спросить его у
    /// сигнатуры нельзя, там члена ещё нет.
    pub ty: Rc<Term>,
}

/// Связывание написанного типа: что о нём известно до элаборации тела.
#[derive(Clone, Debug)]
struct Argument {
    /// Кратность из `Pi`.
    mult: Mult,
    /// Домен - тип, который получит связывание.
    ///
    /// Живёт под теми же связываниями, что и в исходном телескопе, а
    /// элаборация связывает их в том же порядке, поэтому вычислять его можно
    /// прямо в её контексте. Держится это на том, что параметров у семейств
    /// пока нет (§10 вопрос про `FamilyParameters`): появись они, телескоп
    /// конструктора начинался бы с них, а паттерн - нет.
    domain: Rc<Term>,
    /// Имя связывания. Имплиситу оно нужно как имя переменной: аргумента ему
    /// никто не писал, а тело вправе его назвать - тем именем, под которым его
    /// подняли (см. `lifting`).
    name: CoreName,
    /// Выводится ли аргумент вместо того, чтобы писаться.
    implicit: bool,
    /// Объявлена ли голова домена `unique` или `resource`.
    owned: bool,
    /// Функция ли это - домен сам `Pi`.
    functional: bool,
    /// Деструктор, если голова домена - ресурсный тип.
    drop: Option<Symbol>,
}

impl Argument {
    /// Привязано ли связывание к своему scope.
    ///
    /// §3.3: «параметр кратности `1` функционального типа наследует то же
    /// ограничение внутри вызываемой функции». Без этого правила функция,
    /// возвращающая свой аргумент, выносит наружу захваченное замыкание, и
    /// запрет на позицию возврата обходится в одну строку.
    fn scoped(&self) -> bool {
        self.functional && self.mult == Mult::One
    }

    /// Закрывается ли связывание автоматически, когда о нём забыли.
    ///
    /// Стёртое не закрывается: `drop` расходует ресурс, а стёртое связывание
    /// расходовать нечем - вставка отвергала бы корректную программу (§3.3,
    /// §10 вопрос 71).
    fn closes(&self) -> Option<&Symbol> {
        self.drop.as_ref().filter(|_| self.mult != Mult::Zero)
    }
}

/// Локальное связывание: имя, видно ли оно поиску (см. `hiding`), владеет ли
/// оно (§3.3) и не привязано ли к своему scope.
struct Bound {
    name: Symbol,
    /// Кратность, с которой связывание объявлено.
    mult: Mult,
    /// Тип связывания. Нужен вставке имплиситов: дырка замкнута телескопом
    /// контекста, и построить её тип без типов связываний нечем.
    ty: Rc<Value>,
    visible: bool,
    owned: bool,
    /// Значение связывания, если оно `let`. Вычисление его подставляет,
    /// поэтому переменной такое связывание не остаётся - см. `fresh_meta`.
    value: Option<Rc<Term>>,
    /// Значение, которое не вправе покинуть scope: замыкание над владеющим
    /// связыванием, связывание, инициализированное таким замыканием, и
    /// `1`-параметр функционального типа (§3.3).
    scoped: bool,
}

impl Bound {
    fn visible(name: &Symbol, mult: Mult, ty: Rc<Value>) -> Self {
        Self {
            name: Rc::clone(name),
            mult,
            ty,
            visible: true,
            owned: false,
            scoped: false,
            value: None,
        }
    }

    fn owning(name: &Symbol, mult: Mult, ty: Rc<Value>, owned: bool) -> Self {
        Self {
            owned,
            ..Self::visible(name, mult, ty)
        }
    }

    fn owning_scoping(name: &Symbol, mult: Mult, ty: Rc<Value>, owned: bool, scoped: bool) -> Self {
        Self {
            owned,
            scoped,
            ..Self::visible(name, mult, ty)
        }
    }
}

/// Где стоит элаборируемое выражение - для правила scope-bound (§3.3).
///
/// Значение, привязанное к scope, применяется и передаётся аргументом, но не
/// возвращается и не кладётся в поле конструктора. Позиция синтаксическая, но
/// проверять её на лямбда-литерале недостаточно: §3.3 прямо показывает обход
/// через `let`, и есть ещё два - функция, возвращающая свой аргумент, и
/// конструктор. Поэтому позиция здесь встречается со **свойством значения**,
/// которое элаборация считает и распространяет.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Position {
    /// Аргумент, голова применения, значение `let` - откуда значение не уедет.
    Inner,
    /// Возвращаемое значение функции: тело клаузы, тело лямбды, хвост блока.
    Returned,
    /// Аргумент конструктора: значение уедет внутри собранного.
    Field,
}

impl Position {
    /// Как это называется в сообщении; `None` - позиция, откуда не уедет.
    fn face(self) -> Option<&'static str> {
        match self {
            Self::Inner => None,
            Self::Returned => Some("возвращается"),
            Self::Field => Some("кладётся в поле конструктора"),
        }
    }
}

/// Состояние элаборации: сигнатура, хранилище дырок и локальные связывания.
pub(crate) struct Elaborator<'a> {
    /// Уже объявленное. Элаборация её не меняет - объявляет вызывающий.
    pub signature: &'a Signature,
    /// Хранилище дырок уровня: одно на прогон (§10 вопрос 51).
    pub metas: &'a mut Metas,
    /// Типы, объявленные `unique` или `resource` (§3.3). Как и хранилище
    /// дырок, приходит снаружи: прогон элаборации - модуль целиком.
    pub owned: &'a Owned,
    /// Локальные связывания снаружи внутрь; индекс де Брёйна - расстояние от
    /// конца.
    scope: Vec<Bound>,
    /// Типовой контекст, двигающийся вместе с областью видимости.
    ///
    /// Тот же, которым пользуется ядро: имена, кратности и типы связываний
    /// плюс окружение вычисления. Заводить свой значило бы держать второй
    /// источник истины о том, что связано.
    ctx: Ctx<'a>,
    /// Члены объявляемой группы вместе с арностью параметров уровня.
    ///
    /// В сигнатуре их ещё нет - она увидит группу целиком (§10 вопрос 50), - а
    /// ссылаться на них надо: конструктор называет своё семейство, тело
    /// называет само определение. Спросить арность у сигнатуры поэтому нечего,
    /// и её считает вызывающий обобщением по типу члена; это и есть §10
    /// вопрос 63.
    group: Vec<Member>,
    /// Связывания написанного типа - по одному на `Pi` его спайна.
    ///
    /// Лямбда в ядре несёт кратность, и `check` требует, чтобы она совпадала с
    /// кратностью `Pi`. Вывести её элаборация не может - она не
    /// типонаправленная, - но здесь и выводить нечего: тип **написан**, и
    /// спайн его виден синтаксически. Оттуда же берётся деструктор: голова
    /// домена видна тем же взглядом. Дальше видимого спайна (кодомен -
    /// константа, разворачивающаяся в `Pi`) записи кончаются, и лямбда снова
    /// берёт `ω` без закрытия.
    declared: Vec<Argument>,
    /// Записи, ожидающие ближайшую лямбду. Их выставляет тот, кто знает
    /// написанный тип: клауза - остатком спайна после своих паттернов, `let` -
    /// спайном своей аннотации.
    expected: Vec<Argument>,
    /// Идёт ли элаборация в позиции типа - см. `typing`.
    types: bool,
    /// Сколько row-переменных сигнатуры уже роздано записям (§4.2).
    ///
    /// `usize::MAX` - записи закрыты: так элаборируются алиас `type` и всё,
    /// что сигнатурой не является. Auto-lift применяется только там, где
    /// row-переменную есть кому связать.
    rows: usize,
    /// Запрещена ли вставка имплиситов ближайшему имени - см. `type_app`.
    bare: bool,
    /// Где стоит ближайший подтерм - см. [`Position`].
    position: Position,
    /// Привязано ли к scope значение, которое только что собрано, и каким
    /// именем оно к нему привязано.
    ///
    /// Обратный канал правила scope-bound: свойство считается снизу вверх -
    /// лямбда привязана захватом, имя привязано своим связыванием, блок
    /// привязан своим хвостом, - а запрещает его позиция, известная сверху.
    /// Применение свойство **не** передаёт: результат применения к scope не
    /// привязан, а построить возвращающее замыкание нельзя - запрет на
    /// позицию возврата не даёт собрать его вовсе.
    produced: Option<Symbol>,
    /// Аргументы уровня, уже выданные имени в этом объявлении.
    ///
    /// Одно имя - один набор дырок, а не свежий на каждое вхождение. Иначе
    /// `f : D -> D` над полиморфным по уровню `D` читается как `∀u v. D{u} ->
    /// D{v}`: обобщение идёт до проверки тела, связать два параметра потом
    /// нечем, и тождество над таким семейством не пишется. Тот же довод уже
    /// стоял за общими дырками у члена группы (`self_levels` в
    /// [`crate::decl`]), здесь он распространён на объявленное.
    ///
    /// Цена названа: два вхождения одного имени на разных уровнях в одной
    /// сигнатуре теперь несовместимы. Написать их всё равно нечем - уровни в
    /// поверхностном языке не именуются, - и появится это вместе с
    /// имплиситами (§4.1).
    instantiated: HashMap<Symbol, Term>,
}

impl<'a> Elaborator<'a> {
    /// Элаборатор с пустым локальным контекстом.
    pub(crate) fn new(signature: &'a Signature, metas: &'a mut Metas, owned: &'a Owned) -> Self {
        Self::with_group(signature, metas, owned, Vec::new())
    }

    /// То же, но с членами объявляемой группы.
    pub(crate) fn with_group(
        signature: &'a Signature,
        metas: &'a mut Metas,
        owned: &'a Owned,
        group: Vec<Member>,
    ) -> Self {
        Self {
            signature,
            metas,
            owned,
            ctx: Ctx::new(signature),
            scope: Vec::new(),
            group,
            declared: Vec::new(),
            expected: Vec::new(),
            bare: false,
            rows: usize::MAX,
            types: false,
            position: Position::Inner,
            produced: None,
            instantiated: HashMap::new(),
        }
    }

    /// Кратности написанного типа - те, что достанутся лямбдам тела.
    pub(crate) fn declaring(mut self, ty: &Term) -> Self {
        self.declared = pi_arguments(ty, self.owned);
        self
    }

    /// Выполняет `body` в позиции типа.
    ///
    /// Несвязанное строчное имя означает здесь не опечатку, а свободную
    /// переменную, которую §4.1 поднимает в implicit-параметр, - и отвечать
    /// на неё «имя не найдено» значит отправить искать опечатку там, где её
    /// нет.
    pub(crate) fn typing<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.types, true);
        let outcome = body(self);
        self.types = outer;
        outcome
    }

    /// Телескоп параметров семейства: `data Vect (a : Type) : … where`.
    ///
    /// Элаборируется **один раз** на объявление и переиспользуется: kind и
    /// каждый конструктор обязаны нести один и тот же телескоп, а не два
    /// одинаково выглядящих. Домен, которого не написали (`data Pair a b`), -
    /// дырка: чем параметр окажется, скажет его употребление, ровно как у
    /// поднятого имени.
    ///
    /// # Errors
    ///
    /// Если тип параметра не элаборируется либо имя заглавное.
    pub(crate) fn telescope(&mut self, params: &[ast::Binder]) -> Result<Vec<Param>, ElabError> {
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        let mut found = Vec::new();
        for binder in params {
            for name in &binder.names {
                Self::binds(name)?;
                // Ненаписанный тип параметра - `Type`, а не общая дырка:
                // `data Pair a b` называет типы, а параметр иного рода
                // пишется (`(0 n : Nat)`). Универсум семейства обязан
                // вместить уровни своих параметров, и без этого умолчания
                // считать их было бы нечем.
                let domain = match &binder.ty {
                    Some(ty) => self.typing(|it| it.expr(ty, Mult::Many))?,
                    None => Term::Universe(self.metas.fresh_level()),
                };
                let mult = match &binder.ty {
                    Some(ty) => self.binder_mult(binder.mult, ty, Mult::Many, binder.span)?,
                    None => Self::multiplicity(binder.mult, Mult::Many),
                };
                let bound = self.typed(&domain);
                self.ctx = self
                    .ctx
                    .bind(CoreName::from(&*name.text), mult, Rc::clone(&bound));
                self.scope.push(Bound::visible(&name.text, mult, bound));
                found.push(Param {
                    mult,
                    name: Rc::clone(&name.text),
                    ty: Rc::new(domain),
                });
            }
        }
        self.scope.truncate(depth);
        self.ctx = outer;
        Ok(found)
    }

    /// Уровень универсума, в котором обязано жить семейство с такими
    /// параметрами.
    ///
    /// Поле конструктора типа `a` живёт там же, где `a`, то есть в универсуме
    /// параметра. Значит семейство обязано быть не ниже, иначе предикативность
    /// (§3.2) обходится через data-декларацию. Берётся максимум - наименьшее,
    /// что подходит; так же, как `Type 0` был наименьшим у семейства без
    /// параметров.
    #[must_use]
    pub(crate) fn sort(params: &[Param], written: Level) -> Level {
        params
            .iter()
            .fold(written, |found, param| match &*param.ty {
                Term::Universe(level) => found.max(level.clone()),
                _ => found,
            })
    }

    /// Выполняет `body` под параметрами и оборачивает результат в `Pi`.
    ///
    /// `implicit` - у kind параметры пишутся (`Vect a n`), у конструктора
    /// выводятся (`Nil`, а не `Nil Int`).
    pub(crate) fn wrapped(
        &mut self,
        params: &[Param],
        implicit: bool,
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            return body(self);
        };
        let bound = self.typed(&param.ty);
        let inner = self.binding(Bound::visible(&param.name, param.mult, bound), |it| {
            it.wrapped(rest, implicit, body)
        })?;
        let binder = if implicit {
            Binder::implicit(param.mult)
        } else {
            Binder::explicit(param.mult)
        };
        Ok(Term::Pi(
            binder,
            CoreName::from(&*param.name),
            Rc::clone(&param.ty),
            Row::empty(),
            Rc::new(inner),
        ))
    }

    /// Написанный тип объявления - со свободными именами, поднятыми в
    /// implicit-параметры (§4.1).
    ///
    /// `Nil : Vect a 0` объявляется как `{0 a : ?t} -> Vect a 0`. Кратность
    /// `0`: поднятое имя живёт в стёртом фрагменте, и платить за него в
    /// рантайме не за что.
    ///
    /// Тип связывания - **дырка**, а не `Type`: подъём не знает, чем имя
    /// окажется. `Cons : a -> Vect a n -> Vect a (n + 1)` поднимает `n`, и что
    /// это `Nat`, говорит только kind семейства. Дырку решает проверка - там же,
    /// где решает всё прочее.
    pub(crate) fn declaration(&mut self, ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        let mut lifted: Vec<Lifted> = self
            .free(ty)
            .into_iter()
            .map(|name| Lifted { name, row: false })
            .collect();
        // Записи сигнатуры получают row-переменную каждая своя, и считаются
        // они синтаксически - до элаборации, ровно как свободные имена: имя
        // связывания нужно знать раньше, чем оно понадобится.
        for index in 0..written_rows(ty) {
            lifted.push(Lifted {
                name: Rc::from(format!("#row{index}").as_str()),
                row: true,
            });
        }
        self.rows = 0;
        self.lifting(&lifted, ty, default)
    }

    fn lifting(&mut self, lifted: &[Lifted], ty: &Expr, default: Mult) -> Result<Term, ElabError> {
        let Some((first, rest)) = lifted.split_first() else {
            return self.typing(|it| it.expr(ty, default));
        };
        let level = self.metas.fresh_level();
        let domain = if first.row {
            Term::RowKind(level)
        } else {
            let sort = Rc::new(Value::Universe(level));
            self.fresh_meta(&sort)
        };
        let bound = self.ctx.eval(&domain);
        let body = self.under(&first.name, Mult::Zero, bound, |it| {
            it.lifting(rest, ty, default)
        })?;
        Ok(Term::Pi(
            Binder::implicit(Mult::Zero),
            CoreName::from(&*first.name),
            Rc::new(domain),
            Row::empty(),
            Rc::new(body),
        ))
    }

    /// Свободные имена написанного типа - те, что §4.1 поднимает в
    /// implicit-параметры.
    ///
    /// Порядок - первого появления в тексте: `Vect n a` даёт `{n} {a}`, и
    /// автор видит их там же, где написал. Отбираются строчные имена, которые
    /// ничем не разрешаются: заглавное обязано быть объявленным (правило
    /// регистра §4.1), а разрешившееся - не свободно.
    pub(crate) fn free(&self, expr: &Expr) -> Vec<Symbol> {
        let mut found = Vec::new();
        let mut bound: Vec<Symbol> = Vec::new();
        self.free_in(expr, &mut bound, &mut found);
        found
    }

    fn free_in(&self, expr: &Expr, bound: &mut Vec<Symbol>, found: &mut Vec<Symbol>) {
        match &expr.kind {
            ExprKind::Name(name) => self.free_name(name, bound, found),
            ExprKind::App(callee, argument) | ExprKind::TypeApp(callee, argument) => {
                self.free_in(callee, bound, found);
                self.free_in(argument, bound, found);
            }
            ExprKind::Arrow(domain, codomain) => {
                self.free_in(domain, bound, found);
                self.free_in(codomain, bound, found);
            }
            ExprKind::Chain(chain) => {
                self.free_in(&chain.head, bound, found);
                for (operator, operand) in &chain.tail {
                    self.free_name(operator, bound, found);
                    self.free_in(operand, bound, found);
                }
            }
            // Связывание закрывает своё имя для всего, что под ним. Тип группы
            // `(x y : A)` при этом читается до обоих имён - как и в самой
            // элаборации, где та же группа прячет их от собственного домена.
            ExprKind::Pi { binders, codomain } => {
                let depth = bound.len();
                for binder in binders {
                    if let Some(ty) = &binder.ty {
                        self.free_in(ty, bound, found);
                    }
                    bound.extend(binder.names.iter().map(|it| Rc::clone(&it.text)));
                }
                self.free_in(codomain, bound, found);
                bound.truncate(depth);
            }
            // Тип записи связывает свои поля для последующих: телескоп.
            ExprKind::RecordType(fields) => {
                let depth = bound.len();
                for field in fields {
                    self.free_in(&field.ty, bound, found);
                    bound.push(Rc::clone(&field.name.text));
                }
                bound.truncate(depth);
            }
            ExprKind::Record(fields) => {
                for (_, value) in fields {
                    self.free_in(value, bound, found);
                }
            }
            ExprKind::Project(record, _) => self.free_in(record, bound, found),
            ExprKind::Lam { params, body } => {
                let depth = bound.len();
                for param in params {
                    match &param.kind {
                        LamParamKind::Pattern(pattern) => binds_names(pattern, bound),
                        LamParamKind::Binder(binder) => {
                            bound.extend(binder.names.iter().map(|it| Rc::clone(&it.text)));
                        }
                    }
                }
                self.free_in(body, bound, found);
                bound.truncate(depth);
            }
            // Формы, до которых элаборация типа не доходит вовсе: искать в них
            // свободные имена значило бы поднять параметр ради того, что всё
            // равно ответит `Missing`.
            ExprKind::Block(_)
            | ExprKind::If { .. }
            | ExprKind::Case { .. }
            | ExprKind::Tuple(_)
            | ExprKind::List(_)
            | ExprKind::Lit(_)
            | ExprKind::Hole => {}
        }
    }

    fn free_name(&self, name: &ast::Name, bound: &[Symbol], found: &mut Vec<Symbol>) {
        let known = is_reference(&name.text)
            || &*name.text == "Type"
            || bound.contains(&name.text)
            || found.contains(&name.text)
            || self.local(&name.text).is_some()
            || self.group.iter().any(|member| member.name == name.text)
            || self.signature.lookup(&name.text).is_some();
        if !known {
            found.push(Rc::clone(&name.text));
        }
    }

    /// Свежая дырка терма, стоящая в текущем контексте.
    ///
    /// Тип её - телескоп по контексту, оканчивающийся целью: дырка замкнута, и
    /// зависимость от связываний выражена применением к ним. Кратности
    /// телескопа - `0`: дырку заводят на месте типа, а тип живёт в стёртом
    /// фрагменте, и применение к контексту не должно ничего расходовать.
    fn fresh_meta(&mut self, goal: &Rc<Value>) -> Term {
        let size = self.ctx.size();
        let mut telescope = quote(size, goal);
        let mut spine = Vec::new();
        for (depth, bound) in self.scope.iter().enumerate().rev() {
            let depth = u32::try_from(depth).unwrap_or(u32::MAX);
            let ty = Rc::new(quote(depth, &bound.ty));
            let name = CoreName::from(&*bound.name);
            // Связывание со значением идёт `Let`ом: индексы цели считаны по
            // всему контексту, и пропустить его значило бы их сдвинуть.
            // Вычисление телескопа его подставит - ровно так же, как подставит
            // проверка, - и параметром дырки оно не станет.
            telescope = if let Some(value) = &bound.value {
                Term::Let(Mult::Zero, name, ty, Rc::clone(value), Rc::new(telescope))
            } else {
                spine.push(depth);
                Term::Pi(
                    Binder::explicit(Mult::Zero),
                    name,
                    ty,
                    Row::empty(),
                    Rc::new(telescope),
                )
            };
        }
        spine.reverse();
        let closed = eval(&Env::default(), &telescope);
        self.metas.fresh_term_over(closed, &spine, size)
    }

    /// Тип связывания как значение - настолько, насколько он известен.
    ///
    /// **Проверка обязательна перед вычислением, а не желательна:** `eval`
    /// вправе паниковать на нетипизированном входе, а элаборация вычисляет то,
    /// что ядро ещё не смотрело. Без этой проверки первый же неверно
    /// написанный домен ронял бы процесс вместо отказа.
    ///
    /// **Отказ ядра здесь не отказ элаборации, а «типа пока нет».** Причин
    /// две, и обе законные. Тип может быть неверен - тогда об этом скажет
    /// `check`, которому терм и уйдёт: он авторитет, а не этот проход. И тип
    /// может называть члена объявляемой группы (`Succ : Nat -> Nat`), которого
    /// в сигнатуре ещё нет по построению (§10 вопрос 50), - здесь это не
    /// ошибка вовсе.
    ///
    /// Контекст элаборации поэтому **best-effort**: он нужен ей самой - чтобы
    /// строить типы дырок, - и полнота его не влияет ни на принимаемые
    /// программы, ни на отвергаемые. Названная цена: под связыванием, тип
    /// которого не сошёлся, вставка имплиситов знает меньше.
    fn typed(&mut self, term: &Term) -> Rc<Value> {
        if is_type(&self.ctx, self.metas, term).is_err() {
            return self.hole();
        }
        self.ctx.eval(term)
    }

    /// Дырка на месте типа, которого не написали.
    fn hole(&mut self) -> Rc<Value> {
        let level = self.metas.fresh_level();
        let sort = Rc::new(Value::Universe(level));
        let meta = self.fresh_meta(&sort);
        self.ctx.eval(&meta)
    }

    /// Выполняет `body` под связыванием `name` типа `ty`.
    fn under<T>(
        &mut self,
        name: &Symbol,
        mult: Mult,
        ty: Rc<Value>,
        body: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.binding(Bound::visible(name, mult, ty), body)
    }

    /// То же, но связывание несёт свойства владения и привязки к scope (§3.3).
    ///
    /// Область видимости и типовой контекст двигаются вместе и только здесь:
    /// разойдись они, индекс де Брёйна указывал бы на одно связывание, а тип -
    /// на другое.
    fn binding<T>(&mut self, bound: Bound, body: impl FnOnce(&mut Self) -> T) -> T {
        let inner = self.ctx.bind(
            CoreName::from(&*bound.name),
            bound.mult,
            Rc::clone(&bound.ty),
        );
        let outer = std::mem::replace(&mut self.ctx, inner);
        self.scope.push(bound);
        let outcome = body(self);
        self.scope.pop();
        self.ctx = outer;
        outcome
    }

    /// Чем лямбда привязана к scope: захваченным владеющим связыванием либо
    /// захваченным значением, которое само привязано.
    ///
    /// Сам по себе захват законен - §3.3 разрешает применить такую лямбду и
    /// передать её аргументом. Незаконен **побег**, и его ловит позиция.
    fn captured(&self, body: &Expr) -> Option<&Symbol> {
        self.scope
            .iter()
            .rev()
            .find(|bound| {
                bound.visible && (bound.owned || bound.scoped) && self.mentions(&bound.name, body)
            })
            .map(|bound| &bound.name)
    }

    /// Расходуется ли `name` в теле - правило вставки `drop` (см.
    /// [`crate::live`]). Кратности параметров берутся из сигнатуры, а
    /// локальные имена - из текущей области видимости: затенённая голова
    /// применения чужих кратностей не получает.
    fn mentions(&self, name: &str, body: &Expr) -> bool {
        self.mentions_beside(name, body, &[])
    }

    /// То же, но связывания, которых в области видимости ещё нет: решение о
    /// вставке принимается **до** того, как переменные клаузы и параметры
    /// лямбды туда попадут, а затенять голову они уже вправе.
    fn mentions_beside(&self, name: &str, body: &Expr, beside: &[Symbol]) -> bool {
        let mut locals = self.locals();
        locals.extend_from_slice(beside);
        live::Spent::new(self.signature, &locals).mentions(name, body)
    }

    /// То же для того, что стоит после связывания `let`.
    fn mentioned_later(&self, name: &str, tail: &[Binding], rest: &[Stmt]) -> bool {
        let locals = self.locals();
        live::Spent::new(self.signature, &locals).in_bindings_body(name, tail, rest)
    }

    /// Видимые локальные имена.
    fn locals(&self) -> Vec<Symbol> {
        self.scope
            .iter()
            .filter(|bound| bound.visible)
            .map(|bound| Rc::clone(&bound.name))
            .collect()
    }

    /// Привязано ли имя к scope своим связыванием.
    fn scoped_name(&self, name: &str) -> Option<&Symbol> {
        self.scope
            .iter()
            .rev()
            .find(|bound| bound.visible && bound.scoped && &*bound.name == name)
            .map(|bound| &bound.name)
    }

    /// Выполняет `body` в позиции `position`.
    fn placed<T>(&mut self, position: Position, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.position, position);
        let outcome = body(self);
        self.position = outer;
        outcome
    }

    /// Выполняет `body`, спрятав `count` последних связываний.
    ///
    /// Спрятанное связывание место в контексте занимает, а имени не имеет:
    /// индексы де Брёйна остаются верными, а поиск по имени сквозь него
    /// проходит наружу. Нужно это ровно группе `(x y : A)`, где `A` написано
    /// раньше обоих имён и видеть их не может.
    fn hiding<T>(&mut self, count: usize, body: impl FnOnce(&mut Self) -> T) -> T {
        let from = self.scope.len() - count;
        for bound in &mut self.scope[from..] {
            bound.visible = false;
        }
        let outcome = body(self);
        for bound in &mut self.scope[from..] {
            bound.visible = true;
        }
        outcome
    }

    /// Индекс де Брёйна локального связывания.
    fn local(&self, name: &str) -> Option<u32> {
        self.scope
            .iter()
            .rposition(|bound| bound.visible && &*bound.name == name)
            .and_then(|position| u32::try_from(self.scope.len() - 1 - position).ok())
    }

    /// Имя, которое связывает, обязано быть строчным (§4.1).
    ///
    /// Заглавное ссылается на объявленное, и связывать им значило бы заслонить
    /// то, на что оно ссылается: `let Zero : Nat = …` делал конструктор
    /// недостижимым до конца блока.
    fn binds(name: &ast::Name) -> Result<(), ElabError> {
        if is_reference(&name.text) {
            return Err(ElabError::UppercaseBinding {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        }
        Ok(())
    }

    /// Кратность связывания: написанная либо умолчание позиции (§4.1).
    fn multiplicity(written: Option<ast::MultAnn>, default: Mult) -> Mult {
        written.map_or(default, |ann| match ann.mult {
            ast::Mult::Zero => Mult::Zero,
            ast::Mult::One => Mult::One,
            ast::Mult::Many => Mult::Many,
        })
    }

    /// То же, с поправкой на владение (§3.3).
    ///
    /// Связывание unique- или resource-типа получает `1`, если не объявлено
    /// `0`: стёртые упоминания в доказательствах законны, а вот явное `ω` -
    /// ошибка **на самом связывании**. Так закрывается дыра ω→1: значений
    /// такого типа при кратности `ω` не существует, потому что не существует
    /// связывания, которое их удержало бы.
    fn binder_mult(
        &self,
        written: Option<ast::MultAnn>,
        ty: &Expr,
        default: Mult,
        span: Span,
    ) -> Result<Mult, ElabError> {
        let Some(owned) = self.owned.of(ty) else {
            return Ok(Self::multiplicity(written, default));
        };
        match written.map(|ann| ann.mult) {
            None | Some(ast::Mult::One) => Ok(Mult::One),
            Some(ast::Mult::Zero) => Ok(Mult::Zero),
            Some(ast::Mult::Many) => Err(ElabError::UnrestrictedOwned {
                owned,
                span: written.map_or(span, |ann| ann.span),
            }),
        }
    }

    /// Выражение в терм.
    ///
    /// `default` - кратность связываний, у которых она не написана: `ω` у
    /// параметра функции, `1` у поля конструктора (§4.1). Умолчание
    /// **позиционное**: оно расходуется на связывание, к которому пришло, и
    /// доходит только до кодомена - там стоит следующий параметр той же
    /// сигнатуры. В домен и в любой другой подтерм элаборация уходит с `ω`:
    /// `(Nat -> Nat) -> C` берёт поле типа «функция», а не поле с кратностью
    /// поля.
    pub(crate) fn expr(&mut self, expr: &Expr, default: Mult) -> Result<Term, ElabError> {
        // Кратности ждут ближайшую лямбду и только её: подтерм, до которого
        // спустились иначе, написанным типом не накрыт.
        let expected = std::mem::take(&mut self.expected);
        // То же с позицией: её выставляет тот, кто спускается, и достаётся она
        // ближайшему подтерму, а не всему, что под ним.
        let position = std::mem::replace(&mut self.position, Position::Inner);
        // Свойство «привязано к scope» считается снизу вверх, и каждый разбор
        // отвечает за своё: собранное здесь не наследует чужого.
        self.produced = None;
        let term = self.form(expr, default, &expected, position)?;
        // Позиция встречается со свойством: привязанное к scope значение
        // возвращать и класть в поле конструктора нельзя (§3.3).
        if let (Some(face), Some(name)) = (position.face(), self.produced.as_ref()) {
            return Err(ElabError::ScopeBound {
                name: Rc::clone(name),
                face,
                span: expr.span,
            });
        }
        Ok(term)
    }

    /// Форма выражения - без правила позиции, которое стоит вокруг неё.
    fn form(
        &mut self,
        expr: &Expr,
        default: Mult,
        expected: &[Argument],
        position: Position,
    ) -> Result<Term, ElabError> {
        let missing = |what| {
            Err(ElabError::Missing {
                what,
                span: expr.span,
            })
        };
        match &expr.kind {
            ExprKind::Name(name) => {
                if let Some(scoped) = self.scoped_name(&name.text) {
                    self.produced = Some(Rc::clone(scoped));
                }
                self.name(name)
            }
            // Спайн собирается циклом. Рекурсия по `callee` уходила на глубину
            // числа аргументов, а его ограничивает только длина файла: предел
            // вложенности парсера на плоское `f a b c …` не тратится, и тысячи
            // аргументов роняли процесс вместо отказа (§10 вопрос 62).
            ExprKind::App(..) => {
                let mut arguments = Vec::new();
                let mut head = expr;
                while let ExprKind::App(callee, argument) = &head.kind {
                    arguments.push(&**argument);
                    head = callee;
                }
                // Аргумент конструктора уезжает внутри собранного значения, а
                // аргумент функции - нет: §3.3 разрешает замыканию над
                // владеющим связыванием применяться и передаваться.
                let inside = if self.constructs(head) {
                    Position::Field
                } else {
                    Position::Inner
                };
                let mut term = self.placed(Position::Inner, |it| it.expr(head, Mult::Many))?;
                for argument in arguments.into_iter().rev() {
                    let argument = self.placed(inside, |it| it.expr(argument, Mult::Many))?;
                    term = Term::App(Rc::new(term), Rc::new(argument));
                }
                // Результат применения к scope не привязан: собрать замыкание,
                // которое его возвращает, не даёт правило позиции.
                self.produced = None;
                Ok(term)
            }
            ExprKind::Arrow(domain, codomain) => {
                // Стрелка связывает так же, как `(x : A) ->`, только без
                // имени, поэтому правило владения (§3.3) действует и здесь:
                // `drop : File -> Unit` даёт `(1 _ : File) -> Unit`, и писать
                // кратность руками не нужно.
                let mult = self.binder_mult(None, domain, default, expr.span)?;
                let domain = self.expr(domain, Mult::Many)?;
                let anonymous: Symbol = Rc::from("_");
                let bound = self.typed(&domain);
                let codomain = self.under(&anonymous, mult, bound, |inner| {
                    inner.expr(codomain, default)
                })?;
                Ok(Term::Pi(
                    // Стрелка пишется без скобок, поэтому связывание у неё
                    // явное: выводить нечего, аргумент стоит в месте вызова.
                    Binder::explicit(mult),
                    CoreName::from("_"),
                    Rc::new(domain),
                    // Эффектов в поверхностном языке ещё нет (§3.4, Фаза 4),
                    // поэтому всякая написанная стрелка чиста.
                    Row::empty(),
                    Rc::new(codomain),
                ))
            }
            ExprKind::Pi { binders, codomain } => self.pi(binders, codomain, default),
            ExprKind::Lam { params, body } => {
                // Захват - то, чем лямбда привязывается к scope. Позиция
                // решает снаружи; здесь только считается свойство, и ставится
                // оно **после** сборки: тело - тоже выражение, и свой ответ
                // оно затрёт своим.
                let captured = self.captured(body).cloned();
                let term = self.lam(params, body, expected)?;
                self.produced = captured;
                Ok(term)
            }
            ExprKind::Block(block) => self.block(block, position),
            ExprKind::Chain(chain) => self.chain(chain, expr.span),

            // Тип записи - телескоп: каждое следующее поле элаборируется под
            // предыдущими, потому что вправе на них ссылаться (§4.2).
            ExprKind::RecordType(fields) => self.record_type(fields),
            ExprKind::Record(fields) => self.record(fields),
            ExprKind::Project(record, name) => {
                let inner = self.placed(Position::Inner, |it| it.expr(record, Mult::Many))?;
                Ok(Term::Project(Rc::new(inner), CoreName::from(&*name.text)))
            }
            ExprKind::TypeApp(..) => self.type_app(expr),

            // `_` - дырка терма: решать её теперь есть чем, и нерешённая
            // доезжает до объявления своим отказом (`AmbiguousTerm`), а не
            // «механизма нет».
            ExprKind::Hole => {
                let goal = self.hole();
                Ok(self.fresh_meta(&goal))
            }
            ExprKind::Lit(_) => missing(Missing::Literal),
            // `if` - разбор по `Bool` (§4.1), и записывается он ровно им:
            // отдельного узла в ядре нет, а различать их было бы двумя путями
            // к одному терму.
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let alts = conditional(then_branch, else_branch);
                self.case(cond, &alts, expr.span)
            }
            ExprKind::Case { scrutinee, alts } => self.case(scrutinee, alts, expr.span),
            ExprKind::Tuple(items) if items.is_empty() => missing(Missing::Unit),
            ExprKind::Tuple(_) => missing(Missing::Tuple),
            ExprKind::List(_) => missing(Missing::List),
        }
    }

    /// `case e of …` - разбор выражением (§4.1).
    ///
    /// # Разбор компилируется тем же компилятором, что и клаузы
    ///
    /// Вложенные паттерны, порядок «побеждает первая совпавшая» и проверка
    /// полноты уже написаны ([`adamas_core::pattern`]), и второй экземпляр
    /// этого не нужен ни здесь, ни где-либо ещё. Компилятор работает с
    /// **замкнутым** типом и клаузами над телескопом его аргументов, а `case`
    /// стоит внутри тела, где в области видимости есть локальные связывания.
    /// Поэтому разбор поднимается в функцию от всего контекста и тут же к нему
    /// применяется: `case e of …` в контексте `Γ` есть `(\Γ x -> match x) Γ e`.
    ///
    /// Подъём не бесплатен - лямбда по всему контексту на каждый `case`, - но
    /// плата эта времени сборки: кратности связываний сохраняются, поэтому
    /// применение к `Γ` расходует ровно столько же, сколько расходовало бы
    /// прямое употребление, и линейность не ломается.
    ///
    /// # Мотив недепендентный, и это названная граница
    ///
    /// Тип результата - дырка, заведённая **до** связывания разбираемого,
    /// поэтому от него он зависеть не может. `case` над `Vect a n`, чей
    /// результат меняется от ветви к ветви, отсюда не пишется; ему нужен
    /// написанный мотив, и это отдельный срез.
    fn case(&mut self, scrutinee: &Expr, alts: &[ast::Alt], span: Span) -> Result<Term, ElabError> {
        if alts.is_empty() {
            return Err(ElabError::EmptyCase { span });
        }
        let value = self.placed(Position::Inner, |it| it.expr(scrutinee, Mult::Many))?;
        let Some(ty) = self.synthesized(&value) else {
            return Err(ElabError::NotMatchable { span });
        };
        let domain = quote(self.ctx.size(), &ty);
        let consumed = self.consumption(scrutinee, &domain);

        // Тип поднятой функции: телескоп контекста, затем разбираемое, затем
        // дырка результата. Дырка заводится в `Γ`, а стоит под ещё одним
        // связыванием, поэтому читается обратно на единицу глубже.
        let sort = Rc::new(Value::Universe(self.metas.fresh_level()));
        let result = self.fresh_meta(&sort);
        let result = quote(self.ctx.size() + 1, &self.ctx.eval(&result));
        let lifted = self.lifted(Term::Pi(
            Binder::explicit(consumed),
            CoreName::from("_"),
            Rc::new(domain),
            Row::empty(),
            Rc::new(result),
        ));

        // Связывания контекста идут первыми паттернами: компилятор нумерует
        // переменные слева направо, и порядок совпадает с областью видимости,
        // в которой элаборируется тело ветви.
        let outer: Vec<CorePattern> = self
            .scope
            .iter()
            .map(|bound| CorePattern::Var(CoreName::from(&*bound.name)))
            .collect();
        let mut clauses = Vec::with_capacity(alts.len());
        for alt in alts {
            let pattern = self.pattern(&alt.pattern)?;
            let mut patterns = outer.clone();
            patterns.push(pattern.clone());
            let body = self.branch(&alt.pattern, &pattern, &alt.body)?;
            clauses.push(Clause { patterns, body });
        }

        let outer = u32::try_from(outer.len()).unwrap_or(u32::MAX);
        let tree = compile(self.signature, self.metas, &lifted, &clauses).map_err(|error| {
            let error = uncovered(error, outer);
            ElabError::Clauses {
                span: alts
                    .get(clause_of(&error))
                    .map_or(span, |alt: &ast::Alt| alt.span),
                error: Box::new(error),
            }
        })?;
        // Поднятое связывается `let`ом, а не применяется на месте: тип
        // цепочки лямбд не синтезируется, а `let` несёт аннотацию - ту самую,
        // по которой её и собрали.
        let size = self.ctx.size();
        // Под связыванием `let` всё съезжает на единицу; читается обратно на
        // ту же единицу глубже.
        let scrutinee = quote(size + 1, &self.ctx.eval(&value));
        let applied = (0..size).fold(Term::var(0), |term, depth| {
            Term::App(Rc::new(term), Rc::new(Term::var(size - depth)))
        });
        self.produced = None;
        Ok(Term::Let(
            Mult::Many,
            CoreName::from("case"),
            Rc::new(lifted),
            Rc::new(tree),
            Rc::new(Term::App(Rc::new(applied), Rc::new(scrutinee))),
        ))
    }

    /// Тип терма - у ядра, а если оно не знает, то у объявляемой группы.
    ///
    /// Рекурсивный вызов в разбираемом (`if even k then …` внутри `even`)
    /// сигнатуре ещё не известен по построению (§10 вопрос 50), а тип его
    /// известен группе. Считается он тем же правилом применения: спайн
    /// снимает по связыванию за аргумент.
    fn synthesized(&mut self, term: &Term) -> Option<Rc<Value>> {
        if let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Zero, term) {
            return Some(ty);
        }
        let mut arguments = Vec::new();
        let mut head = term;
        while let Term::App(callee, argument) = head {
            arguments.push(&**argument);
            head = callee;
        }
        arguments.reverse();
        let Term::Const(name, levels) = head else {
            return None;
        };
        let member = self.group.iter().find(|it| *it.name == **name)?;
        let mut ty = eval(&Env::default(), &member.ty.substitute_levels(levels));
        for argument in arguments {
            let Value::Pi(_, _, _, _, codomain) = &*ty else {
                return None;
            };
            let codomain = codomain.clone();
            ty = codomain.apply(self.ctx.eval(argument));
        }
        Some(ty)
    }

    /// Тело одной ветви - под переменными её паттерна.
    fn branch(
        &mut self,
        written: &Pattern,
        compiled: &CorePattern,
        body: &Expr,
    ) -> Result<Term, ElabError> {
        let mut names = Vec::new();
        variables_of(compiled, &mut names);
        let mut bound = Vec::new();
        self.pattern_variables(Some(written), compiled, None, body, &names, &mut bound);
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        for variable in &bound {
            let ty = match &variable.domain {
                Some(domain) => self.typed(domain),
                None => self.hole(),
            };
            self.ctx = self.ctx.bind(
                CoreName::from(&*variable.name),
                variable.mult,
                Rc::clone(&ty),
            );
            self.scope.push(Bound::owning_scoping(
                &variable.name,
                variable.mult,
                ty,
                variable.owned,
                variable.scoped,
            ));
        }
        let term = self.expr(body, Mult::Many);
        self.scope.truncate(depth);
        self.ctx = outer;
        term
    }

    /// Оборачивает тип в телескоп контекста - с теми же кратностями.
    ///
    /// Кратности сохраняются, иначе применение к `Γ` масштабировало бы
    /// использование: `1`-связывание, поданное в ω-параметр, отвергалось бы
    /// на каждом `case` внутри его области видимости.
    fn lifted(&self, inner: Term) -> Term {
        let mut telescope = inner;
        for (depth, bound) in self.scope.iter().enumerate().rev() {
            let depth = u32::try_from(depth).unwrap_or(u32::MAX);
            telescope = Term::Pi(
                Binder::explicit(bound.mult),
                CoreName::from(&*bound.name),
                Rc::new(quote(depth, &bound.ty)),
                Row::empty(),
                Rc::new(telescope),
            );
        }
        telescope
    }

    /// Кратность, с которой разбор потребляет разбираемое (§3.3, вопрос 65).
    ///
    /// У написанного имени берётся кратность его связывания: разбирается
    /// именно оно. У составного выражения связывания нет, и решает голова
    /// типа - владеемое потребляется однажды, прочее неограниченно.
    fn consumption(&self, scrutinee: &Expr, ty: &Term) -> Mult {
        if let ExprKind::Name(name) = &scrutinee.kind {
            if let Some(bound) = self
                .scope
                .iter()
                .rev()
                .find(|bound| bound.visible && bound.name == name.text)
            {
                return bound.mult;
            }
        }
        let mut head = ty;
        while let Term::App(callee, _) = head {
            head = callee;
        }
        match head {
            Term::Const(name, _) if self.owned.owns(name) => Mult::One,
            _ => Mult::Many,
        }
    }

    /// `{ x : A, y : B }` - телескоп полей.
    ///
    /// Поле кратности `1` (§4.1): запись кладёт значение однажды - тот же
    /// довод, что у поля конструктора.
    fn record_type(&mut self, fields: &[ast::RecordField]) -> Result<Term, ElabError> {
        // Хвост берётся один раз на запись - до полей: связывание его стоит
        // снаружи них, и внутри индекс был бы уже другим.
        let tail = self.row_variable();
        let inner = self.record_fields(fields)?;
        Ok(Term::Record(Fields {
            fields: inner.into(),
            tail,
        }))
    }

    /// Row-переменная этой записи, если сигнатура их раздаёт (§4.2).
    ///
    /// Закрыты записи в алиасе `type` и всюду, где связать переменную нечем:
    /// раздаёт их `declaration`, и раздаёт ровно столько, сколько насчитала.
    fn row_variable(&mut self) -> Option<Rc<Term>> {
        let index = self
            .rows
            .checked_add(1)
            .filter(|_| self.rows != usize::MAX)?;
        let name: Symbol = Rc::from(format!("#row{}", self.rows).as_str());
        self.rows = index;
        self.local(&name).map(|it| Rc::new(Term::var(it)))
    }

    /// Поля записи телескопом - каждое под предыдущими.
    fn record_fields(&mut self, fields: &[ast::RecordField]) -> Result<Vec<CoreField>, ElabError> {
        let Some((field, rest)) = fields.split_first() else {
            return Ok(Vec::new());
        };
        Self::binds(&field.name)?;
        let ty = self.typing(|it| it.expr(&field.ty, Mult::Many))?;
        let bound = self.typed(&ty);
        let tail = self.binding(Bound::visible(&field.name.text, Mult::One, bound), |it| {
            it.record_fields(rest)
        })?;
        let head = CoreField {
            name: CoreName::from(&*field.name.text),
            mult: Mult::One,
            ty: Rc::new(ty),
        };
        Ok(std::iter::once(head).chain(tail).collect())
    }

    /// `{ x = a, y }` - значение записи.
    fn record(&mut self, fields: &[(ast::Name, Expr)]) -> Result<Term, ElabError> {
        let mut written = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            // Поле уезжает внутрь собранного - та же позиция, что у аргумента
            // конструктора (§3.3).
            let value = self.placed(Position::Field, |it| it.expr(value, Mult::One))?;
            written.push((CoreName::from(&*name.text), Rc::new(value)));
        }
        self.produced = None;
        Ok(Term::Object(written.into()))
    }

    /// `f @A @B` - выводимый аргумент, написанный явно (§4.1).
    ///
    /// Голова элаборируется **без** вставки: `@` пишет ровно те аргументы,
    /// которые иначе стали бы дырками, и вставленную дырку `@` уже не заменит.
    /// Остаток ведущих имплиситов вставляется после цепочки, поэтому `g @Nat x`
    /// при `g : {a} -> {b} -> a -> b -> …` пишет `a` и выводит `b`.
    ///
    /// Цепочка снимается циклом по той же причине, что и спайн применения:
    /// длину её ограничивает только текст.
    fn type_app(&mut self, expr: &Expr) -> Result<Term, ElabError> {
        let mut written = Vec::new();
        let mut head = expr;
        while let ExprKind::TypeApp(callee, argument) = &head.kind {
            written.push(&**argument);
            head = callee;
        }
        let mut term = self.placed(Position::Inner, |it| {
            if matches!(head.kind, ExprKind::Name(_)) {
                it.bare(|it| it.expr(head, Mult::Many))
            } else {
                it.expr(head, Mult::Many)
            }
        })?;
        let mut ty = infer(&self.ctx, self.metas, Mult::Zero, &term)
            .map(|(ty, _)| ty)
            .map_err(|_| ElabError::NoImplicitParameter { span: expr.span })?;
        for argument in written.into_iter().rev() {
            let Value::Pi(binder, _, _, _, codomain) = &*ty else {
                return Err(ElabError::NoImplicitParameter {
                    span: argument.span,
                });
            };
            if !binder.visibility.is_implicit() {
                return Err(ElabError::NoImplicitParameter {
                    span: argument.span,
                });
            }
            let codomain = codomain.clone();
            // Написанный аргумент - тип, и подходит ли он домену, скажет
            // `check`: авторитет он, а не этот проход.
            let written = self.typing(|it| it.expr(argument, Mult::Zero))?;
            let value = self.typed(&written);
            term = Term::App(Rc::new(term), Rc::new(written));
            ty = codomain.apply(value);
        }
        // Применение к scope результат к нему не привязывает - см. `App`.
        self.produced = None;
        Ok(self.implicits(term, ty))
    }

    /// Выполняет `body`, не вставляя имплиситы ближайшему имени.
    fn bare<T>(&mut self, body: impl FnOnce(&mut Self) -> T) -> T {
        let outer = std::mem::replace(&mut self.bare, true);
        let outcome = body(self);
        self.bare = outer;
        outcome
    }

    /// Собирает ли применение с такой головой значение - то есть конструктор
    /// ли она.
    ///
    /// Аргумент конструктора уезжает внутри собранного, и §3.3 запрещает
    /// класть туда привязанное к scope; аргумент функции таким свойством не
    /// обладает.
    fn constructs(&self, head: &Expr) -> bool {
        let ExprKind::Name(name) = &head.kind else {
            return false;
        };
        self.builds(name)
    }

    /// То же по имени: у оператора головы-выражения нет, а конструктором он
    /// быть может - `(::)` кладёт аргумент в ячейку списка так же, как `Cons`.
    fn builds(&self, name: &ast::Name) -> bool {
        self.local(&name.text).is_none()
            && self
                .signature
                .lookup(&name.text)
                .is_some_and(|it| matches!(it.kind, DefinitionKind::Constructor { .. }))
    }

    /// Имя: связывание, `Type` или ссылка на объявленное.
    fn name(&mut self, name: &ast::Name) -> Result<Term, ElabError> {
        if let Some(index) = self.local(&name.text) {
            return Ok(Term::var(index));
        }
        // `Type` заслоняется локальным связыванием, но не определением: имя
        // занято языком, и переопределить его нечем.
        if &*name.text == "Type" {
            return Ok(Term::Universe(self.metas.fresh_level()));
        }
        // Член объявляемой группы: аргументы уровня - дырки, числом в арность,
        // посчитанную вызывающим. Тип его сигнатура ещё не знает (§10 вопрос
        // 50), поэтому имплиситы вставляются по типу, принесённому в группе.
        if let Some(member) = self.group.iter().find(|it| it.name == name.text) {
            let term = Term::Const(CoreName::from(&*name.text), Rc::clone(&member.levels));
            if self.bare || !opens_implicit(&member.ty) {
                return Ok(term);
            }
            let ty = eval(&Env::default(), &member.ty);
            return Ok(self.implicits(term, ty));
        }
        // Аргументы уровня подставляются дырками - это implicit UP со стороны
        // места использования (§3.2), - и одному имени они выдаются один раз
        // на объявление (см. `instantiated`).
        if let Some(term) = self.instantiated.get(&name.text).cloned() {
            return Ok(self.implicit_use(&name.text, term));
        }
        let term = self
            .signature
            .instantiate(&name.text, self.metas)
            .ok_or_else(|| {
                if self.types && !is_reference(&name.text) {
                    return ElabError::Missing {
                        what: Missing::FreeTypeVariable,
                        span: name.span,
                    };
                }
                ElabError::UnknownName {
                    name: Rc::clone(&name.text),
                    span: name.span,
                }
            })?;
        self.instantiated
            .insert(Rc::clone(&name.text), term.clone());
        Ok(self.implicit_use(&name.text, term))
    }

    /// Вставляет выводимые аргументы имени, тип которого знает ядро.
    ///
    /// Под `@` не вставляет ничего: аргументы там пишутся, и дырка на месте
    /// первого из них заняла бы его место.
    ///
    /// Кэш `instantiated` держит имя **без** них: аргументы уровня у имени в
    /// объявлении общие, а имплиситы - нет. `id x` и `id y` в одном теле стоят
    /// при разных типах, и общая дырка связала бы их в один.
    fn implicit_use(&mut self, name: &str, term: Term) -> Term {
        // Отбор по объявленному типу идёт до `infer`: тот вычисляет тип
        // целиком, а имён без имплиситов в обычной программе подавляющее
        // большинство, и платить за них этим вычислением не за что.
        let opens = self
            .signature
            .lookup(name)
            .is_some_and(|definition| opens_implicit(&definition.ty));
        if self.bare || !opens {
            return term;
        }
        let Ok((ty, _)) = infer(&self.ctx, self.metas, Mult::Zero, &term) else {
            // Тип не сошёлся - вставлять нечего, а сказать об этом полагается
            // `check`: авторитет он, а не этот проход (см. `typed`).
            return term;
        };
        self.implicits(term, ty)
    }

    /// Применяет `term` к дырке на каждое ведущее implicit-связывание его типа.
    ///
    /// Вставка **энергичная**: аргумент выводится там, где имя встретилось, а
    /// не там, где до него доберётся проверка. Названная цена - `f = id`:
    /// имплисит вставится и останется нерешённым, потому что обобщать его
    /// нечем. Отложенная вставка требует двунаправленной элаборации, и это
    /// отдельный срез.
    fn implicits(&mut self, mut term: Term, mut ty: Rc<Value>) -> Term {
        loop {
            let Value::Pi(binder, _, domain, _, codomain) = &*ty else {
                return term;
            };
            if !binder.visibility.is_implicit() {
                return term;
            }
            let (domain, codomain) = (Rc::clone(domain), codomain.clone());
            let argument = self.fresh_meta(&domain);
            let value = self.ctx.eval(&argument);
            term = Term::App(Rc::new(term), Rc::new(argument));
            ty = codomain.apply(value);
        }
    }

    /// `(q x y : A) (r z : B) -> C`.
    ///
    /// Группы разворачиваются в плоский список связываний: `(x y : A)` - это
    /// два `Pi`, и второй видит первое связывание, поэтому тип элаборируется
    /// заново под каждым именем. Заново - но не в другой области видимости:
    /// `A` написано раньше обоих имён, и собственные имена группы для него
    /// спрятаны (`hiding`), иначе `(0 t : Type) -> (0 t x : t) -> …` дало бы
    /// `x` тип соседа по группе вместо написанного снаружи. Отсюда третье
    /// поле плоского списка - сколько имён группы стоит перед этим.
    ///
    /// Дырки уровня у каждого имени свои: общий `Type` в записи не значит
    /// общий универсум, а более общее прочтение здесь безопасно.
    fn pi(
        &mut self,
        binders: &[ast::Binder],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let mut flat: Vec<(Mult, Symbol, &Expr, usize)> = Vec::new();
        for binder in binders {
            if binder.visibility == Visibility::Implicit {
                return Err(ElabError::Missing {
                    what: Missing::ImplicitBinder,
                    span: binder.span,
                });
            }
            // Связывание без написанного типа бывает у параметра семейства
            // (`data Pair a b`), и туда этот путь не ведёт: `(a) -> Nat`
            // разбирается как применение в скобках, а не как связывание.
            let Some(ty) = &binder.ty else {
                return Err(ElabError::Missing {
                    what: Missing::TypelessBinder,
                    span: binder.span,
                });
            };
            let mult = self.binder_mult(binder.mult, ty, default, binder.span)?;
            for (position, name) in binder.names.iter().enumerate() {
                Self::binds(name)?;
                flat.push((mult, Rc::clone(&name.text), ty, position));
            }
        }
        self.pi_flat(&flat, codomain, default)
    }

    fn pi_flat(
        &mut self,
        binders: &[(Mult, Symbol, &Expr, usize)],
        codomain: &Expr,
        default: Mult,
    ) -> Result<Term, ElabError> {
        let Some(((mult, name, ty, siblings), rest)) = binders.split_first() else {
            return self.expr(codomain, default);
        };
        let domain = self.hiding(*siblings, |inner| inner.expr(ty, Mult::Many))?;
        let owns = self.owned.of(ty).is_some();
        let bound = self.typed(&domain);
        let body = self.binding(Bound::owning(name, *mult, bound, owns), |inner| {
            inner.pi_flat(rest, codomain, default)
        })?;
        Ok(Term::Pi(
            Binder::explicit(*mult),
            CoreName::from(&**name),
            Rc::new(domain),
            Row::empty(),
            Rc::new(body),
        ))
    }

    /// `\x y -> body`.
    ///
    /// `expected` - связывания написанного типа, по одному на параметр.
    /// Кончились (тип не написан, кодомен не виден насквозь) - берётся `ω` без
    /// закрытия, и лямбда под не-`ω` связыванием остаётся невыразимой.
    ///
    /// Ресурс закрывается здесь по тому же правилу, что и аргумент клаузы:
    /// `f = \h -> True` и `f h = True` - одно определение, записанное дважды,
    /// и вести себя обязаны одинаково.
    fn lam(
        &mut self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
    ) -> Result<Term, ElabError> {
        // Считается до спуска: индексы закрываемых меряются от тела, то есть
        // от точки, где связаны все параметры этой лямбды.
        let drops = self.closing_params(params, body, expected);
        self.lam_params(params, body, expected, &drops)
    }

    fn lam_params(
        &mut self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
        drops: &[(u32, Symbol)],
    ) -> Result<Term, ElabError> {
        let Some((param, rest)) = params.split_first() else {
            // Остаток спайна достаётся телу: `\x -> \y -> e` - две лямбды под
            // теми же `Pi`, что и `\x y -> e`.
            self.expected = expected.to_vec();
            // Тело лямбды - её возвращаемое значение, и правило §3.3 стоит
            // здесь так же, как у тела клаузы.
            return self.closing_all(drops, |it| {
                it.placed(Position::Returned, |it| it.expr(body, Mult::Many))
            });
        };
        let name = match &param.kind {
            LamParamKind::Binder(_) => {
                return Err(ElabError::Missing {
                    what: Missing::LambdaAnnotation,
                    span: param.span,
                });
            }
            LamParamKind::Pattern(pattern) => match &pattern.kind {
                PatternKind::Name(name) if !is_reference(&name.text) => Rc::clone(&name.text),
                PatternKind::Wildcard => Rc::from("_"),
                PatternKind::Tuple(items) if items.is_empty() => {
                    return Err(ElabError::Missing {
                        what: Missing::Unit,
                        span: pattern.span,
                    });
                }
                _ => {
                    // Разбор в параметре лямбды - это `case` без мотива.
                    return Err(ElabError::Missing {
                        what: Missing::LambdaPattern,
                        span: pattern.span,
                    });
                }
            },
        };
        let (mult, deeper) = expected
            .split_first()
            .map_or((Mult::Many, expected), |(argument, rest)| {
                (argument.mult, rest)
            });
        // Тип параметра приходит из написанного типа; там, где он не
        // написан, лямбда и кратности не получает, и связывание берёт тип
        // дырки - решать её потом будет проверка.
        let ty = match expected.first() {
            Some(argument) => {
                let domain = Rc::clone(&argument.domain);
                self.typed(&domain)
            }
            None => self.hole(),
        };
        let bound = expected.first().map_or_else(
            || Bound::visible(&name, mult, Rc::clone(&ty)),
            |argument| {
                Bound::owning_scoping(
                    &name,
                    mult,
                    Rc::clone(&ty),
                    argument.owned,
                    argument.scoped(),
                )
            },
        );
        let inner = self.binding(bound, |inner| inner.lam_params(rest, body, deeper, drops))?;
        Ok(Term::Lam(mult, CoreName::from(&*name), Rc::new(inner)))
    }

    /// Параметры лямбды, которые она обязана закрыть сама.
    ///
    /// Правило то же, что у аргументов клаузы: ресурс, не упомянутый в теле,
    /// закрывается. Разбор в параметре сюда не попадает - его элаборация
    /// отвергает, - а `_` попадает: имени у него нет, упоминанию взяться
    /// неоткуда, и закрыть его обязаны всегда.
    fn closing_params(
        &self,
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
    ) -> Vec<(u32, Symbol)> {
        // Параметры связывают тело и затеняют в нём головы применений, а в
        // области видимости их ещё нет - решение принимается до спуска.
        let beside: Vec<Symbol> = params
            .iter()
            .filter_map(|param| match &param.kind {
                LamParamKind::Pattern(pattern) => match &pattern.kind {
                    PatternKind::Name(name) => Some(Rc::clone(&name.text)),
                    _ => None,
                },
                LamParamKind::Binder(_) => None,
            })
            .collect();
        let mut found: Vec<(u32, Symbol)> = Vec::new();
        for (position, param) in params.iter().enumerate() {
            let Some(drop) = expected.get(position).and_then(Argument::closes) else {
                continue;
            };
            let LamParamKind::Pattern(pattern) = &param.kind else {
                continue;
            };
            let mentioned = match &pattern.kind {
                PatternKind::Name(name) if !is_reference(&name.text) => {
                    self.mentions_beside(&name.text, body, &beside)
                }
                PatternKind::Wildcard => false,
                _ => continue,
            };
            if mentioned {
                continue;
            }
            let index = u32::try_from(params.len() - 1 - position).unwrap_or(u32::MAX);
            found.push((index, drop.clone()));
        }
        lifo(&mut found);
        found
    }

    /// Блок операторов: цепочка `let` и значение последним.
    fn block(&mut self, block: &Block, position: Position) -> Result<Term, ElabError> {
        // Закрываемые копятся до конца блока: их область видимости кончается
        // там же, где блок, и закрыть их раньше значило бы закрыть не на
        // выходе из scope (§3.3).
        let mut closing = Vec::new();
        self.statements(&block.stmts, &mut closing, position)
    }

    fn statements(
        &mut self,
        stmts: &[Stmt],
        closing: &mut Vec<(u32, Symbol)>,
        position: Position,
    ) -> Result<Term, ElabError> {
        let Some((first, rest)) = stmts.split_first() else {
            // Пустых блоков layout не делает.
            unreachable!("блок без операторов")
        };
        match &first.kind {
            StmtKind::Expr(expr) if rest.is_empty() => {
                // Хвост блока: все связывания на месте, индексы копившихся
                // закрываемых считаются отсюда.
                let depth = self.scope.len();
                let mut drops: Vec<(u32, Symbol)> = closing
                    .iter()
                    .map(|(born, drop)| {
                        let index = u32::try_from(depth - 1 - *born as usize).unwrap_or(u32::MAX);
                        (index, drop.clone())
                    })
                    .collect();
                lifo(&mut drops);
                // Хвост блока стоит там же, где блок: возвращаемое значение
                // остаётся возвращаемым (§3.3), и отказ придёт на нём, а не
                // на блоке целиком.
                self.closing_all(&drops, |it| {
                    it.placed(position, |it| it.expr(expr, Mult::Many))
                })
            }
            StmtKind::Expr(_) => Err(ElabError::Missing {
                what: Missing::Sequencing,
                span: first.span,
            }),
            // Блок кончается связыванием: значения у него нет, и дело не в
            // недостающем механизме - написана неполная форма.
            StmtKind::Let(_) if rest.is_empty() => {
                Err(ElabError::BlockWithoutValue { span: first.span })
            }
            StmtKind::Let(bindings) => self.bindings(bindings, rest, closing, position),
        }
    }

    /// `let` со своими связываниями: каждое даёт узел `Let`, вложенный в
    /// следующее.
    fn bindings(
        &mut self,
        bindings: &[Binding],
        rest: &[Stmt],
        closing: &mut Vec<(u32, Symbol)>,
        position: Position,
    ) -> Result<Term, ElabError> {
        let Some((binding, tail)) = bindings.split_first() else {
            return self.statements(rest, closing, position);
        };
        if !binding.params.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: binding.span,
            });
        }
        let Some(ty) = &binding.ty else {
            return Err(ElabError::Missing {
                what: Missing::UntypedLet,
                span: binding.span,
            });
        };
        Self::binds(&binding.name)?;
        let mult = self.binder_mult(binding.mult, ty, Mult::Many, binding.span)?;
        // Ресурс, имя которого дальше не встречается, закрывается сам (§3.3);
        // стёртое связывание - нет, расходовать там нечего.
        let closes = mult != Mult::Zero
            && !self.mentioned_later(&binding.name.text, tail, rest)
            && self.owned.destructor(ty).is_some();
        let drop = closes.then(|| self.owned.destructor(ty).cloned()).flatten();
        let owns = self.owned.of(ty).is_some();
        let ty = self.typing(|inner| inner.expr(ty, Mult::Many))?;
        // Аннотация `let` - тот же написанный тип, и лямбда значения берёт
        // кратности у него.
        self.expected = pi_arguments(&ty, self.owned);
        let value = self.expr(&binding.body, Mult::Many)?;
        // §3.3: связывание, инициализированное привязанным к scope значением,
        // само привязано. Без этого правило обходится в одну строку - и обход
        // выписан в §3.3 дословно.
        let scoped = self.produced.take().is_some();
        let born = u32::try_from(self.scope.len()).unwrap_or(u32::MAX);
        let annotation = self.typed(&ty);
        let bound = Bound {
            value: Some(Rc::new(value.clone())),
            ..Bound::owning_scoping(&binding.name.text, mult, annotation, owns, scoped)
        };
        let body = self.binding(bound, |inner| {
            if let Some(drop) = drop {
                closing.push((born, drop));
            }
            inner.bindings(tail, rest, closing, position)
        })?;
        Ok(Term::Let(
            mult,
            CoreName::from(&*binding.name.text),
            Rc::new(ty),
            Rc::new(value),
            Rc::new(body),
        ))
    }

    /// Собирает тело под вставленным `drop` и оборачивает его вызовом.
    ///
    /// `index` - индекс закрываемого связывания в области видимости **без**
    /// вставки; связывание самого вызова добавляется здесь и учитывается уже
    /// при сборке тела.
    ///
    /// Кратность вставки - `1`, а не `ω`: при `ω` вектор использований
    /// значения масштабируется до `ω`, и ресурс, связанный при `1`, тут же
    /// оказался бы израсходован сверх меры - отказ на программе, которую
    /// вставка и должна была починить.
    fn closing(
        &mut self,
        drop: Option<&Symbol>,
        index: u32,
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        let Some(drop) = drop else {
            return body(self);
        };
        let (call, result) = self.destructor(drop, index);
        let anonymous: Symbol = Rc::from("_");
        let ty = self.typed(&result);
        let bound = Bound {
            value: Some(Rc::new(call.clone())),
            ..Bound::visible(&anonymous, Mult::One, ty)
        };
        let inner = self.binding(bound, body)?;
        Ok(Term::Let(
            Mult::One,
            CoreName::from("_"),
            Rc::new(result),
            Rc::new(call),
            Rc::new(inner),
        ))
    }

    /// Вызов деструктора и тип его результата.
    ///
    /// Аргументы уровня свежие на каждую вставку: два `drop` в одном
    /// определении - два независимых вхождения, и общие дырки связали бы их
    /// уровни между собой без причины.
    fn destructor(&mut self, drop: &Symbol, index: u32) -> (Term, Term) {
        let Some(definition) = self.signature.lookup(drop) else {
            unreachable!("деструктор `{drop}` объявлен вместе с типом")
        };
        let levels: Rc<[Level]> = (0..definition.level_arity)
            .map(|_| self.metas.fresh_level())
            .collect();
        let Term::Pi(_, _, _, _, result) = definition.ty.substitute_levels(&levels) else {
            unreachable!("`{drop}` проверен на форму при объявлении")
        };
        let call = Term::Const(CoreName::from(&**drop), levels).apply([Term::var(index)]);
        (call, (*result).clone())
    }

    /// Цепочка операторов. Скобки расставляются по фикситетам, а их ещё нет,
    /// поэтому цепочка длиннее одного оператора - отказ.
    fn chain(&mut self, chain: &ast::Chain, span: Span) -> Result<Term, ElabError> {
        let [(operator, operand)] = &chain.tail[..] else {
            // Спан - цепочка целиком: отказ про то, как расставить в ней
            // скобки, а не про первый операнд, к операторам отношения не
            // имеющий.
            return Err(ElabError::Missing {
                what: Missing::Fixities,
                span,
            });
        };
        let callee = self.name(operator)?;
        // Операнды - те же аргументы применения, и позиция у них та же:
        // оператор-конструктор уносит их внутрь собранного, обычный не уносит.
        let inside = if self.builds(operator) {
            Position::Field
        } else {
            Position::Inner
        };
        let left = self.placed(inside, |it| it.expr(&chain.head, Mult::Many))?;
        let right = self.placed(inside, |it| it.expr(operand, Mult::Many))?;
        self.produced = None;
        Ok(callee.apply([left, right]))
    }

    // --- паттерны ---------------------------------------------------------

    /// Паттерн клаузы или ветки.
    pub(crate) fn pattern(&self, pattern: &Pattern) -> Result<CorePattern, ElabError> {
        match &pattern.kind {
            PatternKind::Wildcard => Ok(CorePattern::Var(CoreName::from("_"))),
            PatternKind::Name(name) => {
                if is_reference(&name.text) {
                    self.constructor(name, Vec::new())
                } else {
                    Ok(CorePattern::Var(CoreName::from(&*name.text)))
                }
            }
            PatternKind::App { head, fields } => {
                let fields = fields
                    .iter()
                    .map(|field| self.pattern(field))
                    .collect::<Result<Vec<_>, _>>()?;
                self.constructor(head, fields)
            }
            PatternKind::Lit(_) => Err(ElabError::Missing {
                what: Missing::Literal,
                span: pattern.span,
            }),
            PatternKind::Tuple(items) => Err(ElabError::Missing {
                what: if items.is_empty() {
                    Missing::Unit
                } else {
                    Missing::Tuple
                },
                span: pattern.span,
            }),
        }
    }

    /// Имя конструктора: обязано быть объявленным конструктором.
    fn constructor(
        &self,
        name: &ast::Name,
        fields: Vec<CorePattern>,
    ) -> Result<CorePattern, ElabError> {
        let Some(declared) = self.signature.lookup(&name.text) else {
            return Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        };
        let DefinitionKind::Constructor { data, .. } = &declared.kind else {
            return Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            });
        };
        // Параметры семейства полями не являются: разбор их не связывает, а
        // подставляет из типа разбираемого. В паттерне их поэтому нет вовсе -
        // ни написанных, ни вставленных.
        let params = self
            .signature
            .lookup(data)
            .and_then(Definition::data_shape)
            .map_or(0, |(params, _)| params);
        Ok(CorePattern::Constructor(
            CoreName::from(&*name.text),
            hidden_fields(&declared.ty, params, fields),
        ))
    }

    /// Клауза: паттерны, затем тело в контексте их переменных.
    ///
    /// Порядок переменных - слева направо в глубину: этого ждёт
    /// [`adamas_core::pattern::compile`], и другого тело видеть не может.
    pub(crate) fn clause(&mut self, clause: &ast::Clause) -> Result<Clause, ElabError> {
        if !clause.wheres.is_empty() {
            return Err(ElabError::Missing {
                what: Missing::LocalDefinitions,
                span: clause.span,
            });
        }
        let mut seen: Vec<&ast::Name> = Vec::new();
        for pattern in &clause.patterns {
            repeated(pattern, &mut seen)?;
        }
        let written = self.spread(&clause.patterns)?;
        let patterns: Vec<CorePattern> = written.iter().map(|(_, it)| it.clone()).collect();

        // Тип связывания виден и у аргумента верхнего уровня (по спайну
        // написанного), и у поля (по объявлению конструктора), поэтому
        // владение и закрытие считаются одним проходом по паттернам.
        let bound = self.clause_variables(&written, &clause.body);
        let closing = closing_of(&bound);
        let depth = self.scope.len();
        let outer = self.ctx.clone();
        // По одному: домен связывания живёт под предыдущими, и вычислить его
        // можно только тогда, когда те уже стоят в контексте.
        for variable in &bound {
            let ty = match &variable.domain {
                Some(domain) => self.typed(domain),
                None => self.hole(),
            };
            self.ctx = self.ctx.bind(
                CoreName::from(&*variable.name),
                variable.mult,
                Rc::clone(&ty),
            );
            self.scope.push(Bound::owning_scoping(
                &variable.name,
                variable.mult,
                ty,
                variable.owned,
                variable.scoped,
            ));
        }
        // Паттерны сняли первые связывания написанного типа; остаток спайна -
        // тем лямбдам, которыми клауза продолжается.
        self.expected = self
            .declared
            .split_at(patterns.len().min(self.declared.len()))
            .1
            .to_vec();
        // Тело клаузы - возвращаемое значение определения (§3.3).
        let body = self.closing_all(&closing, |it| {
            it.placed(Position::Returned, |it| it.expr(&clause.body, Mult::Many))
        });
        self.scope.truncate(depth);
        self.ctx = outer;

        Ok(Clause {
            patterns,
            body: body?,
        })
    }

    /// Паттерны клаузы, разложенные по связываниям объявленного типа.
    ///
    /// Имплисит аргумента не получает, но связывание вводит, и подняли его
    /// (`lifting`) в тот же телескоп, по которому идут паттерны. Значит паттерн
    /// у него обязан быть: [`adamas_core::pattern::compile`] считает арность по
    /// их числу, и без вставки первый написанный паттерн встал бы на место
    /// имплисита. Имя берётся из связывания - оно и есть то, под которым тип
    /// назвал переменную.
    ///
    /// Написанное, не покрытое телескопом, идёт следом как есть: спайн виден
    /// синтаксически, и дальше него записей нет (см. `declared`).
    fn spread<'p>(
        &self,
        written: &'p [Pattern],
    ) -> Result<Vec<(Option<&'p Pattern>, CorePattern)>, ElabError> {
        let mut found = Vec::new();
        let mut rest = written.iter();
        for argument in &self.declared {
            if argument.implicit {
                found.push((None, CorePattern::Var(Rc::clone(&argument.name))));
                continue;
            }
            let Some(pattern) = rest.next() else {
                break;
            };
            found.push((Some(pattern), self.pattern(pattern)?));
        }
        for pattern in rest {
            found.push((Some(pattern), self.pattern(pattern)?));
        }
        Ok(found)
    }

    /// Переменные паттернов клаузы в порядке связывания.
    ///
    /// Проход один на оба вопроса - владеет ли связывание и закрывается ли, -
    /// потому что оба решает **тип связывания**, а он известен на каждой
    /// глубине: у аргумента верхнего уровня по спайну написанного, у поля по
    /// объявлению конструктора. Отсюда рекурсия `drop` по полям (§3.3):
    /// `f (Wrap h) = …` закрывает `h` так же, как закрыл бы аргумент.
    fn clause_variables(
        &mut self,
        written: &[(Option<&Pattern>, CorePattern)],
        body: &Expr,
    ) -> Vec<BoundVar> {
        // Имена собираются первым проходом: они связывают тело, а значит и
        // затеняют в нём головы применений, - но в области видимости их ещё
        // нет, решение о вставке принимается раньше.
        let mut names = Vec::new();
        for (_, pattern) in written {
            variables_of(pattern, &mut names);
        }
        let mut found = Vec::new();
        for (position, (source, pattern)) in written.iter().enumerate() {
            let argument = self.declared.get(position).cloned();
            self.pattern_variables(
                *source,
                pattern,
                argument.as_ref(),
                body,
                &names,
                &mut found,
            );
        }
        found
    }

    /// То же для одного паттерна, вглубь.
    ///
    /// `written` теряется у имплисита, которого автор не писал, и там, где у
    /// ядра формы нет вовсе; тогда упоминание считается состоявшимся -
    /// направление ошибки то же, что и везде: пропущенный `drop` вместо
    /// лишнего.
    fn pattern_variables(
        &mut self,
        written: Option<&Pattern>,
        compiled: &CorePattern,
        argument: Option<&Argument>,
        body: &Expr,
        beside: &[Symbol],
        found: &mut Vec<BoundVar>,
    ) {
        match compiled {
            CorePattern::Var(name) => {
                // `_` закрывается всегда: имени у него нет, упоминанию взяться
                // неоткуда.
                let mentioned = match written.map(|it| &it.kind) {
                    Some(PatternKind::Wildcard) => false,
                    Some(PatternKind::Name(written)) if !is_reference(&written.text) => {
                        self.mentions_beside(&written.text, body, beside)
                    }
                    _ => true,
                };
                found.push(BoundVar {
                    name: Rc::from(&**name),
                    mult: argument.map_or(Mult::Many, |it| it.mult),
                    domain: argument.map(|it| Rc::clone(&it.domain)),
                    owned: argument.is_some_and(|it| it.owned),
                    scoped: argument.is_some_and(Argument::scoped),
                    drop: argument
                        .and_then(Argument::closes)
                        .filter(|_| !mentioned)
                        .cloned(),
                });
            }
            CorePattern::Constructor(constructor, fields) => {
                // Спайн типа конструктора начинается с телескопа параметров
                // семейства - ветвь их не получает, и паттерн не пишет.
                // Сегодня параметров не бывает (их отвергает `declare_data`),
                // но сдвиг молча испортил бы соответствие, как только они
                // появятся: поле взяло бы владение у параметра.
                // Тип конструктора несёт **свои** параметры уровня, и брать
                // его как есть значило бы впустить `LevelVar` семейства в
                // определение, которое его не объявляло. Инстанциация свежими
                // дырками - то же, что делает всякая ссылка на объявленное.
                let declared = self.signature.lookup(constructor).map(|definition| {
                    let params = match &definition.kind {
                        DefinitionKind::Constructor { data } => self
                            .signature
                            .lookup(data)
                            .and_then(|it| it.data_shape().map(|(params, _)| params as usize))
                            .unwrap_or(0),
                        _ => 0,
                    };
                    (definition.ty.clone(), definition.level_arity, params)
                });
                let (types, params) = match declared {
                    Some((ty, arity, params)) => {
                        let levels: Vec<Level> =
                            (0..arity).map(|_| self.metas.fresh_level()).collect();
                        let ty = ty.substitute_levels(&levels);
                        (pi_arguments(&ty, self.owned), params)
                    }
                    None => (Vec::new(), 0),
                };
                let inner = match written.map(|it| &it.kind) {
                    Some(PatternKind::App { fields, .. }) => fields.as_slice(),
                    _ => &[],
                };
                for (position, field) in fields.iter().enumerate() {
                    let argument = types.get(position + params).cloned();
                    self.pattern_variables(
                        inner.get(position),
                        field,
                        argument.as_ref(),
                        body,
                        beside,
                        found,
                    );
                }
            }
        }
    }

    /// Оборачивает тело цепочкой вставленных `drop`.
    fn closing_all(
        &mut self,
        drops: &[(u32, Symbol)],
        body: impl FnOnce(&mut Self) -> Result<Term, ElabError>,
    ) -> Result<Term, ElabError> {
        let Some(((index, drop), rest)) = drops.split_first() else {
            return body(self);
        };
        let drop = drop.clone();
        self.closing(Some(&drop), *index, |it| it.closing_all(rest, body))
    }
}

/// Переменная паттерна: имя, владение и деструктор, если её надо закрыть.
struct BoundVar {
    name: Symbol,
    /// Кратность и тип связывания - из телескопа, по которому шёл разбор.
    mult: Mult,
    /// Домен, ещё не вычисленный: считать его надо на той глубине, на которой
    /// связывание встанет, а связываются переменные по одной.
    domain: Option<Rc<Term>>,
    owned: bool,
    scoped: bool,
    drop: Option<Symbol>,
}

/// Закрываемые связывания в порядке вставки.
///
/// Индекс - расстояние от конца списка связанных: последняя переменная стоит
/// ближе всех. Порядок - LIFO, как обещает §3.3 для вложенных scope.
fn closing_of(bound: &[BoundVar]) -> Vec<(u32, Symbol)> {
    let mut found: Vec<(u32, Symbol)> = bound
        .iter()
        .enumerate()
        .filter_map(|(position, variable)| {
            let index = u32::try_from(bound.len() - 1 - position).unwrap_or(u32::MAX);
            variable.drop.clone().map(|drop| (index, drop))
        })
        .collect();
    lifo(&mut found);
    found
}

/// Имена переменных паттерна слева направо в глубину.
fn variables_of(pattern: &CorePattern, names: &mut Vec<Symbol>) {
    match pattern {
        CorePattern::Var(name) => names.push(Rc::from(&**name)),
        CorePattern::Constructor(_, fields) => {
            for field in fields {
                variables_of(field, names);
            }
        }
    }
}

/// Переставляет закрываемые в порядок вставки: LIFO плюс поправка на глубину.
///
/// Последнее связывание закрывается первым, а каждая следующая вставка видит
/// область видимости на одно связывание глубже - на своё же предыдущее.
fn lifo(found: &mut [(u32, Symbol)]) {
    found.reverse();
    for (depth, entry) in found.iter_mut().enumerate() {
        entry.0 += u32::try_from(depth).unwrap_or(0);
    }
}

/// Ветки `if` как альтернативы разбора по `Bool`.
///
/// Спаны берутся у самих веток: ошибка внутри ветки указывает на неё, а не на
/// `if` целиком. Имена конструкторов - `True` и `False`; не найдись они, откажет
/// компилятор клауз, и скажет он это про имя, а не про `if`.
fn conditional(then_branch: &Expr, else_branch: &Expr) -> Vec<ast::Alt> {
    let alt = |text: &str, body: &Expr| ast::Alt {
        pattern: Pattern {
            kind: PatternKind::Name(ast::Name {
                text: Rc::from(text),
                span: body.span,
            }),
            span: body.span,
        },
        body: body.clone(),
        span: body.span,
    };
    vec![alt("True", then_branch), alt("False", else_branch)]
}

/// Убирает из примера непокрытого набора поднятые колонки контекста.
///
/// Автор их не писал, и показывать их значило бы отвечать про терм, которого
/// в исходнике нет. Колонки эти - всегда переменные, то есть в примере занимают
/// ровно по одному слову без скобок, поэтому отделяются по пробелам.
fn uncovered(error: PatternError, outer: u32) -> PatternError {
    let PatternError::NonExhaustive { example } = error else {
        return error;
    };
    let outer = usize::try_from(outer).unwrap_or(usize::MAX);
    let example = example
        .splitn(outer + 1, char::is_whitespace)
        .last()
        .unwrap_or(&example)
        .to_owned();
    PatternError::NonExhaustive { example }
}

/// Номер клаузы, на которой споткнулась сборка; `0` - когда его нет.
fn clause_of(error: &PatternError) -> usize {
    match error {
        PatternError::ClauseArity { clause, .. }
        | PatternError::UnboundInBody { clause }
        | PatternError::UnreachableClause { clause } => *clause,
        _ => 0,
    }
}

/// Начинается ли телескоп с выводимого связывания.
fn opens_implicit(ty: &Term) -> bool {
    matches!(ty, Term::Pi(binder, ..) if binder.visibility.is_implicit())
}

/// Поля конструктора с `_` на местах имплиситов.
///
/// То же, что `spread` делает с паттернами клаузы, и по той же причине:
/// имплисит поднялся в телескоп конструктора, а `Cons x xs` про него не знает.
/// Разбирать его нечем - имя типа в паттерне не пишется, - поэтому `_`.
///
/// Первые `params` связываний пропускаются вовсе: параметры семейства полем не
/// становятся, разбор берёт их из типа разбираемого, и ветвь их не связывает.
fn hidden_fields(ty: &Term, params: u32, written: Vec<CorePattern>) -> Vec<CorePattern> {
    let mut found = Vec::new();
    let mut rest = written.into_iter();
    let mut current = ty;
    let mut skipped = 0;
    while let Term::Pi(binder, _, _, _, codomain) = current {
        if skipped < params {
            skipped += 1;
            current = codomain;
            continue;
        }
        if binder.visibility.is_implicit() {
            found.push(CorePattern::Var(CoreName::from("_")));
        } else {
            let Some(pattern) = rest.next() else {
                break;
            };
            found.push(pattern);
        }
        current = codomain;
    }
    found.extend(rest);
    found
}

/// Связывания по спайну `Pi` - столько, сколько видно синтаксически.
fn pi_arguments(ty: &Term, owned: &Owned) -> Vec<Argument> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(binder, bound, domain, _, codomain) = current {
        let mult = &binder.mult;
        let mut head = &**domain;
        while let Term::App(callee, _) = head {
            head = callee;
        }
        let name = match head {
            Term::Const(name, _) => Some(name),
            _ => None,
        };
        found.push(Argument {
            mult: *mult,
            domain: Rc::clone(domain),
            name: Rc::clone(bound),
            implicit: binder.visibility.is_implicit(),
            owned: name.is_some_and(|name| owned.owns(name)),
            functional: matches!(&**domain, Term::Pi(..)),
            drop: name.and_then(|name| owned.destructor_of(name)).cloned(),
        });
        current = codomain;
    }
    found
}

/// Имена, которые связывает паттерн.
fn binds_names(pattern: &Pattern, bound: &mut Vec<Symbol>) {
    match &pattern.kind {
        PatternKind::Name(name) => bound.push(Rc::clone(&name.text)),
        PatternKind::App { fields, .. } => {
            for field in fields {
                binds_names(field, bound);
            }
        }
        PatternKind::Tuple(items) => {
            for item in items {
                binds_names(item, bound);
            }
        }
        PatternKind::Wildcard | PatternKind::Lit(_) => {}
    }
}

/// Повторное имя переменной в клаузе.
///
/// Клауза `f x x = x` терму отвечает корректному - побеждает правое вхождение,
/// потому что индекс ищется от ближайшего связывания, - и ядро её принимает.
/// Значит поймать опечатку может только элаборация: написанное равенство
/// аргументов языком не выражается, и разбор по нему сравнением не становится.
fn repeated<'a>(pattern: &'a Pattern, seen: &mut Vec<&'a ast::Name>) -> Result<(), ElabError> {
    match &pattern.kind {
        PatternKind::Name(name) if !is_reference(&name.text) => {
            if let Some(first) = seen.iter().find(|earlier| earlier.text == name.text) {
                return Err(ElabError::RepeatedBinding {
                    name: Rc::clone(&name.text),
                    span: name.span,
                    first: first.span,
                });
            }
            seen.push(name);
        }
        PatternKind::App { fields, .. } => {
            for field in fields {
                repeated(field, seen)?;
            }
        }
        _ => {}
    }
    Ok(())
}

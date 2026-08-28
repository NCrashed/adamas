//! Выражения и паттерны поверхностного языка в термы ядра.
//!
//! Границы фрагмента и причина каждой - в [`crate`] и в [`Missing`]; правило
//! регистра - у [`is_reference`]. Здесь - сами правила элаборации, по одному
//! на форму, и то, что из них следует: тому же порядку следует обратный проход
//! маршрута ([`crate::route`]).

use std::collections::HashMap;
use std::rc::Rc;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::mult::Mult;
use adamas_core::pattern::{Clause, Pattern as CorePattern};
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::source::Span;
use adamas_core::term::{Name as CoreName, Term};
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

/// Связывание написанного типа: что о нём известно до элаборации тела.
#[derive(Clone, Debug)]
struct Argument {
    /// Кратность из `Pi`.
    mult: Mult,
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
    visible: bool,
    owned: bool,
    /// Значение, которое не вправе покинуть scope: замыкание над владеющим
    /// связыванием, связывание, инициализированное таким замыканием, и
    /// `1`-параметр функционального типа (§3.3).
    scoped: bool,
}

impl Bound {
    fn visible(name: &Symbol) -> Self {
        Self {
            name: Rc::clone(name),
            visible: true,
            owned: false,
            scoped: false,
        }
    }

    fn owning(name: &Symbol, owned: bool) -> Self {
        Self {
            owned,
            ..Self::visible(name)
        }
    }

    fn owning_scoping(name: &Symbol, owned: bool, scoped: bool) -> Self {
        Self {
            owned,
            scoped,
            ..Self::visible(name)
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
    /// Члены объявляемой группы вместе с арностью параметров уровня.
    ///
    /// В сигнатуре их ещё нет - она увидит группу целиком (§10 вопрос 50), - а
    /// ссылаться на них надо: конструктор называет своё семейство, тело
    /// называет само определение. Спросить арность у сигнатуры поэтому нечего,
    /// и её считает вызывающий обобщением по типу члена; это и есть §10
    /// вопрос 63.
    group: Vec<(Symbol, Rc<[Level]>)>,
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
        group: Vec<(Symbol, Rc<[Level]>)>,
    ) -> Self {
        Self {
            signature,
            metas,
            owned,
            scope: Vec::new(),
            group,
            declared: Vec::new(),
            expected: Vec::new(),
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

    /// Выполняет `body` под связыванием `name`.
    fn under<T>(&mut self, name: &Symbol, body: impl FnOnce(&mut Self) -> T) -> T {
        self.binding(Bound::visible(name), body)
    }

    /// То же, но связывание несёт свойства владения и привязки к scope (§3.3).
    fn binding<T>(&mut self, bound: Bound, body: impl FnOnce(&mut Self) -> T) -> T {
        self.scope.push(bound);
        let outcome = body(self);
        self.scope.pop();
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
                bound.visible && (bound.owned || bound.scoped) && live::mentions(&bound.name, body)
            })
            .map(|bound| &bound.name)
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
                let codomain = self.under(&anonymous, |inner| inner.expr(codomain, default))?;
                Ok(Term::Pi(
                    mult,
                    CoreName::from("_"),
                    Rc::new(domain),
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

            ExprKind::Hole => missing(Missing::TermHole),
            ExprKind::Lit(_) => missing(Missing::Literal),
            ExprKind::TypeApp(..) => missing(Missing::TypeApplication),
            ExprKind::If { .. } => missing(Missing::Conditional),
            ExprKind::Case { .. } => missing(Missing::CaseExpression),
            ExprKind::Tuple(items) if items.is_empty() => missing(Missing::Unit),
            ExprKind::Tuple(_) => missing(Missing::Tuple),
            ExprKind::List(_) => missing(Missing::List),
        }
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
        // посчитанную вызывающим.
        if let Some((_, levels)) = self.group.iter().find(|(member, _)| **member == *name.text) {
            return Ok(Term::Const(CoreName::from(&*name.text), Rc::clone(levels)));
        }
        // Аргументы уровня подставляются дырками - это implicit UP со стороны
        // места использования (§3.2), - и одному имени они выдаются один раз
        // на объявление (см. `instantiated`).
        if let Some(term) = self.instantiated.get(&name.text) {
            return Ok(term.clone());
        }
        let term = self
            .signature
            .instantiate(&name.text, self.metas)
            .ok_or_else(|| {
                if self.types && !is_reference(&name.text) {
                    return ElabError::Missing {
                        what: Missing::Implicits,
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
        Ok(term)
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
            // Связывание без типа бывает только параметром семейства, и туда
            // этот путь не ведёт.
            let Some(ty) = &binder.ty else {
                return Err(ElabError::Missing {
                    what: Missing::Implicits,
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
        let body = self.binding(Bound::owning(name, owns), |inner| {
            inner.pi_flat(rest, codomain, default)
        })?;
        Ok(Term::Pi(
            *mult,
            CoreName::from(&**name),
            Rc::new(domain),
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
        let drops = Self::closing_params(params, body, expected);
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
                        what: Missing::CaseExpression,
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
        let bound = expected.first().map_or_else(
            || Bound::visible(&name),
            |argument| Bound::owning_scoping(&name, argument.owned, argument.scoped()),
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
        params: &[ast::LamParam],
        body: &Expr,
        expected: &[Argument],
    ) -> Vec<(u32, Symbol)> {
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
                    live::mentions(&name.text, body)
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
            && !live::in_bindings_body(&binding.name.text, tail, rest)
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
        let bound = Bound::owning_scoping(&binding.name.text, owns, scoped);
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
        let inner = self.under(&anonymous, body)?;
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
        let Term::Pi(_, _, _, result) = definition.ty.substitute_levels(&levels) else {
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
        let known = self.signature.lookup(&name.text).is_some_and(|definition| {
            matches!(definition.kind, DefinitionKind::Constructor { .. })
        });
        if known {
            Ok(CorePattern::Constructor(
                CoreName::from(&*name.text),
                fields,
            ))
        } else {
            Err(ElabError::NotAConstructor {
                name: Rc::clone(&name.text),
                span: name.span,
            })
        }
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
        let patterns = clause
            .patterns
            .iter()
            .map(|pattern| self.pattern(pattern))
            .collect::<Result<Vec<_>, _>>()?;

        // Тип связывания виден и у аргумента верхнего уровня (по спайну
        // написанного), и у поля (по объявлению конструктора), поэтому
        // владение и закрытие считаются одним проходом по паттернам.
        let bound = self.clause_variables(clause, &patterns);
        let closing = closing_of(&bound);
        let depth = self.scope.len();
        self.scope.extend(
            bound
                .iter()
                .map(|it| Bound::owning_scoping(&it.name, it.owned, it.scoped)),
        );
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

        Ok(Clause {
            patterns,
            body: body?,
        })
    }

    /// Переменные паттернов клаузы в порядке связывания.
    ///
    /// Проход один на оба вопроса - владеет ли связывание и закрывается ли, -
    /// потому что оба решает **тип связывания**, а он известен на каждой
    /// глубине: у аргумента верхнего уровня по спайну написанного, у поля по
    /// объявлению конструктора. Отсюда рекурсия `drop` по полям (§3.3):
    /// `f (Wrap h) = …` закрывает `h` так же, как закрыл бы аргумент.
    fn clause_variables(&self, clause: &ast::Clause, patterns: &[CorePattern]) -> Vec<BoundVar> {
        let mut found = Vec::new();
        for (position, (written, pattern)) in clause.patterns.iter().zip(patterns).enumerate() {
            self.pattern_variables(
                Some(written),
                pattern,
                self.declared.get(position),
                &clause.body,
                &mut found,
            );
        }
        found
    }

    /// То же для одного паттерна, вглубь.
    ///
    /// `written` теряется там, где у ядра формы нет вовсе; тогда упоминание
    /// считается состоявшимся - направление ошибки то же, что и везде:
    /// пропущенный `drop` вместо лишнего.
    fn pattern_variables(
        &self,
        written: Option<&Pattern>,
        compiled: &CorePattern,
        argument: Option<&Argument>,
        body: &Expr,
        found: &mut Vec<BoundVar>,
    ) {
        match compiled {
            CorePattern::Var(name) => {
                // `_` закрывается всегда: имени у него нет, упоминанию взяться
                // неоткуда.
                let mentioned = match written.map(|it| &it.kind) {
                    Some(PatternKind::Wildcard) => false,
                    Some(PatternKind::Name(written)) if !is_reference(&written.text) => {
                        live::mentions(&written.text, body)
                    }
                    _ => true,
                };
                found.push(BoundVar {
                    name: Rc::from(&**name),
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
                let (types, params) = self.signature.lookup(constructor).map_or_else(
                    || (Vec::new(), 0),
                    |definition| {
                        let params = match &definition.kind {
                            DefinitionKind::Constructor { data } => self
                                .signature
                                .lookup(data)
                                .and_then(|it| it.data_shape().map(|(params, _)| params as usize))
                                .unwrap_or(0),
                            _ => 0,
                        };
                        (pi_arguments(&definition.ty, self.owned), params)
                    },
                );
                let inner = match written.map(|it| &it.kind) {
                    Some(PatternKind::App { fields, .. }) => fields.as_slice(),
                    _ => &[],
                };
                for (position, field) in fields.iter().enumerate() {
                    self.pattern_variables(
                        inner.get(position),
                        field,
                        types.get(position + params),
                        body,
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

/// Связывания по спайну `Pi` - столько, сколько видно синтаксически.
fn pi_arguments(ty: &Term, owned: &Owned) -> Vec<Argument> {
    let mut found = Vec::new();
    let mut current = ty;
    while let Term::Pi(mult, _, domain, codomain) = current {
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
            owned: name.is_some_and(|name| owned.owns(name)),
            functional: matches!(&**domain, Term::Pi(..)),
            drop: name.and_then(|name| owned.destructor_of(name)).cloned(),
        });
        current = codomain;
    }
    found
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

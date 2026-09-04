//! Проверка конвертируемости - definitional equality ядра.
//!
//! Сравниваются значения, а не термы: вычисление уже сделало β-редукцию и
//! развернуло `let`, так что здесь остаётся сопоставление форм плюс η.
//!
//! Кумулятивности нет: `Type 0` и `Type 1` неконвертируемы (§10 вопрос 1).
//!
//! # δ-редукция откладывается до последнего
//!
//! Определения приходят сюда неразвёрнутыми ([`crate::eval`] их не трогает).
//! Сначала сравнение как есть: совпали голова и аргументы уровня - достаточно
//! сверить спайны. Только если не сошлось, определение разворачивается и
//! сравнение повторяется.
//!
//! Неудача быстрого пути **не** означает неравенство: `f a` и `f b` равны,
//! если `f` игнорирует аргумент. Поэтому откат к развороту обязателен, а не
//! факультативен.
//!
//! # Разворот ограничен по глубине
//!
//! Нетотальное определение не разворачивается вовсе - иначе разворот заведомо
//! мог бы не закончиться. Но одной тотальности мало: она гарантирует
//! завершаемость вычисления на **замкнутых** аргументах, а сравниваются
//! значения с открытыми, где ι не срабатывает никогда. Две разные тотальные
//! рекурсивные функции над свободной переменной разворачиваются бесконечно -
//! `F x` против `G x` даёт два застрявших `case`, спуск в ветви даёт `F k`
//! против `G k`, и так без дна.
//!
//! Поэтому число разворотов ограничено пределом. Исчерпание даёт
//! `false`, то есть отказ, а не зависание: направление безопасное - неполнота
//! отвергает корректную программу, тогда как обратная ошибка приняла бы
//! некорректную. Так же устроены пределы в Coq, Agda и Lean; на тотальность
//! здесь положиться нельзя ни в одной из них.
//!
//! Предел считается **вдоль пути**, а не на всё сравнение: топливо передаётся
//! вниз копией, поэтому соседние элементы спайна друг у друга его не отнимают.
//! Общий счётчик делал бы конвертируемость зависящей от ширины типа, а не от
//! глубины разворота: два типа, различающихся одним редексом в каждой из `k`
//! стрелок, признавались бы равными при `k = 128` и разными при `k = 129`, то
//! есть отношение переставало быть композициональным - из `A ≡ A'` и `B ≡ B'`
//! не следовало `(A -> B) ≡ (A' -> B')`. Завершаемость от этого не страдает:
//! вдоль любого пути от корня к листу разворотов по-прежнему не больше предела.

use std::rc::Rc;

use crate::eval::{apply, quote, try_apply, try_eliminate_case};
use crate::meta::Metas;
use crate::mult::Mult;
use crate::row::{Label, Row, Tail};
use crate::sig::Signature;
use crate::solve::{force, solve};
use crate::term::{Field, Fields, Name, Term};
use crate::value::{Elim, Head, Lvl, StuckCase, Telescope, Value};

/// Конвертируемы ли два значения в контексте размера `size`.
///
/// Осмысленный вопрос - только про значения одного типа, и проверяющий других
/// не задаёт. Но функция тотальна и на разнотипных: возвращает `false`, а не
/// паникует. Паника здесь была бы не защитой инварианта, а падением на входе,
/// который ничего не нарушает.
///
/// Функция **не чистая**: сравнивая `Type ?l` с `Type 3`, она обязана решить
/// `?l := 3`. Это архитектура, а не недосмотр - вывод уровней происходит
/// именно там, где встречаются два типа.
///
/// Решения не откатываются, и это источник неполноты. Для внешнего вызова
/// безвредно - неудача означает отказ, - но внутри неудача быстрого пути
/// (`rigid`) штатна: она ведёт к δ-развороту и повторному сравнению. Решения,
/// принятые до того, как быстрый путь провалился, повтор переживают. `F{?l} a`
/// против `F{2} b`, где `F` игнорирует и уровень, и аргумент, фиксирует
/// `?l := 2` без основания: сравнение всё равно пройдёт через разворот, а
/// следующее ограничение `?l ~ 5` отвергнет корректную программу. Лечится тем,
/// чтобы `rigid` сравнивал уровни, а решал их только путь, определяющий
/// исход, - работа не этого среза.
pub fn convertible(
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    convertible_within(UNFOLD_LIMIT, sig, metas, size, left, right)
}

/// Приводит значение к слабой головной нормальной форме: разворачивает
/// определение в голове, пока голова разворачивается.
///
/// Нужна везде, где проверка смотрит на **форму** типа, а не сравнивает его с
/// другим: применение спрашивает "это `Pi`?", позиция типа - "это `Universe`?",
/// разбор - "это то семейство?". [`crate::eval`] определений не разворачивает,
/// поэтому без приведения `def Fn = Nat -> Nat` не был бы типом функции, а
/// `def Sort2 = Type 2` - типом вовсе.
///
/// Предел тот же и по той же причине, что у [`convertible`]; исчерпание
/// возвращает то, что успело развернуться, и вызывающий увидит неразвёрнутую
/// голову - то есть отказ, а не зависание.
///
/// **Решённые дырки эта форма не разворачивает** - для них есть
/// [`whnf_solved`], и проверка типов зовёт именно её. Здесь остались
/// [`crate::pattern`] и [`crate::unify`]: хранилища дырок у них в руках нет, а
/// протаскивание его туда - отдельная работа. Названная цена: тип, оказавшийся
/// решённой дыркой, разбор по нему не узнает.
#[must_use]
pub fn whnf(sig: &Signature, value: &Rc<Value>) -> Rc<Value> {
    let mut current = Rc::clone(value);
    let mut fuel = UNFOLD_LIMIT;
    while let Some(next) = unfold(sig, &current) {
        current = next;
        let Some(remaining) = fuel.checked_sub(1) else {
            break;
        };
        fuel = remaining;
    }
    current
}

/// Вычисляет замкнутый терм до **значения** (§9 Фаза 5).
///
/// Не до нормальной формы, и разница существенная: под связывание вычисление
/// не заходит. Глубокая нормализация рекурсивного определения не завершается
/// даже у тотального - `plus` под своим же связыванием разворачивается в себя
/// бесконечно, - и ровно поэтому у сравнения стоит предел разворота. Значение
/// же считается столько, сколько считает программа, и топлива ему не нужно.
///
/// Значение читается насквозь у конструктора и записи: `Succ (plus 1 1)` есть
/// значение только снаружи, а внутрь надо посчитать. Всё прочее - функция,
/// застрявший разбор - читается таким, каким построено.
#[must_use]
pub fn evaluated(sig: &Signature, term: &Term) -> Term {
    let value = crate::eval::eval(&crate::value::Env::default(), term);
    read_value(sig, &value)
}

/// Терм головной формы: глобальное имя развёрнуто, разбор сведён.
fn forced(sig: &Signature, value: &Rc<Value>) -> Rc<Value> {
    let mut current = Rc::clone(value);
    while let Some(next) = unfolded(sig, &current) {
        current = next;
    }
    current
}

fn read_value(sig: &Signature, value: &Rc<Value>) -> Term {
    let value = forced(sig, value);
    match &*value {
        Value::Neutral(head @ Head::Global(name, ..), spine)
            if matches!(
                sig.lookup(name).map(|it| &it.kind),
                Some(crate::sig::DefinitionKind::Constructor { .. })
            ) =>
        {
            let base = crate::eval::quote(0, &Rc::new(Value::Neutral(head.clone(), Vec::new())));
            spine.iter().fold(base, |callee, elim| match elim {
                Elim::App(argument) => {
                    Term::App(Rc::new(callee), Rc::new(read_value(sig, argument)))
                }
                _ => crate::eval::quote(0, &value),
            })
        }
        Value::Object(fields) => Term::Object(
            fields
                .iter()
                .map(|(name, field)| (Rc::clone(name), Rc::new(read_value(sig, field))))
                .collect(),
        ),
        _ => crate::eval::quote(0, &value),
    }
}

/// То же, но сквозь решённые дырки.
///
/// Решённая дырка **и есть** своё решение, и всякий, кто смотрит на форму
/// типа, обязан видеть его, а не `?m`. [`whnf`] разворачивает только глобальное
/// имя, поэтому тип, оказавшийся решённой дыркой, до `Pi` или `Record` не
/// доходил: `(identity plus1) Zero` отвечало «ожидалась функция, получено
/// значение типа `(ω _ : Nat) -> Nat`», печатая ровно ту форму, отсутствие
/// которой объявляло, - сообщение строится зонкающим обратным чтением, а
/// проверка форму читает без него.
///
/// Разворот и подстановка чередуются: решением дырки бывает глобальное имя, а
/// телом определения - другая дырка.
#[must_use]
pub fn whnf_solved(sig: &Signature, metas: &Metas, value: &Rc<Value>) -> Rc<Value> {
    let mut current = Rc::clone(value);
    let mut fuel = UNFOLD_LIMIT;
    loop {
        let Some(next) = force(metas, &current).or_else(|| unfold(sig, &current)) else {
            return current;
        };
        current = next;
        let Some(remaining) = fuel.checked_sub(1) else {
            return current;
        };
        fuel = remaining;
    }
}

/// Сколько δ-разворотов разрешено на одно сравнение.
///
/// Снизу граница задана тем, что должно проходить: разворот `F n` на числе `n`
/// стоит `n` шагов, поэтому предел определяет, до каких чисел арифметика
/// сводится в типах.
///
/// Сверху - стеком: разворот рекурсивен, и предел обязан срабатывать раньше
/// переполнения, иначе он ничего не спасает. Замер на потоке с 2 МБ (столько у
/// тестовых) даёт срыв между 320 и 384 разворотами в debug и между 2400 и 2600
/// в release - кадры debug-сборки на порядок толще, и связывает именно она,
/// потому что тесты и CI гоняются в ней. Предел взят с запасом от меньшего.
const UNFOLD_LIMIT: u32 = 128;

fn convertible_within(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    // Решённая дырка разворачивается до сравнения: иначе `?m` и её решение
    // оказались бы разными значениями, а это одно и то же значение. Форма
    // та же, что у разворота определений ниже: `None` - разворачивать нечего,
    // и клонировать `Rc` на каждом шаге сравнения незачем.
    let (forced_left, forced_right) = (force(metas, left), force(metas, right));
    let left = forced_left.as_ref().unwrap_or(left);
    let right = forced_right.as_ref().unwrap_or(right);

    if rigid(fuel, sig, metas, size, left, right) {
        return true;
    }

    // Нерешённая дырка в голове - не «не сошлось», а задача унификации.
    // Пробуется она **после** синтаксического сравнения и **до** разворота
    // определений. После - потому что `?m ū ≡ ?m ū` решать нечего, а проверка
    // вхождения приняла бы это за цикл. До - потому что развернув, мы получили
    // бы то же ограничение, только на большем терме.
    match (&**left, &**right) {
        // Дырка головой с обеих сторон - **отложить**, а не отвергнуть.
        //
        // Решения у `?f ū ≡ ?g v̄` сейчас нет: обе стороны гибкие, и всякий
        // выбор был бы догадкой. Позже оно бывает - `ap (pure toNat) (Some
        // True)` определяет `?f` вторым аргументом, когда первый уже проверен
        // (§10 вопрос 91).
        //
        // Отложенное **обязано** быть перебрано: `true` здесь говорит «пока не
        // возражаю», а не «сошлось», и без пересмотра это была бы дыра в
        // проверке. Перебирает `check::settle_terms` на границе объявления.
        (Value::Neutral(Head::Meta(a), spine), Value::Neutral(Head::Meta(b), _)) if a != b => {
            if solve(sig, metas, size, *a, spine, right) {
                return true;
            }
            metas.postpone(size, Rc::clone(left), Rc::clone(right));
            return true;
        }
        (Value::Neutral(Head::Meta(meta), spine), _) => {
            return solve(sig, metas, size, *meta, spine, right);
        }
        (_, Value::Neutral(Head::Meta(meta), spine)) => {
            return solve(sig, metas, size, *meta, spine, left);
        }
        _ => {}
    }
    // Быстрый путь не сошёлся - разворачиваем то, что разворачивается.
    let (unfolded_left, unfolded_right) = (unfold(sig, left), unfold(sig, right));
    if unfolded_left.is_none() && unfolded_right.is_none() {
        return false;
    }
    let Some(remaining) = fuel.checked_sub(1) else {
        return false;
    };
    convertible_within(
        remaining,
        sig,
        metas,
        size,
        unfolded_left.as_ref().unwrap_or(left),
        unfolded_right.as_ref().unwrap_or(right),
    )
}

/// Разворачивает определение в голове значения вместе со спайном.
///
/// `None`, если голова - локальная переменная или постулат: разворачивать
/// нечего.
///
/// Спайн переигрывается целиком, включая разбор: развернув `two` в
/// `succ (succ zero)`, застрявший над ним `case` немедленно сводится по ι.
/// Единственное место, где это происходит, - здесь, потому что [`crate::eval`]
/// определений не трогает.
///
/// Переигрывание **может не получиться**, и тогда результат тоже `None`.
/// Спайн накапливается над значением одного типа, а разворачивается голова
/// другого: η-правило ниже дописывает `Elim::App` к любой нейтрали, поэтому
/// сравнение `\x -> x` с `def c : Type 1 = Type 0` доходит сюда с попыткой
/// применить `Type 0` к аргументу. Для сравнения разнотипных значений это
/// штатный исход - `convertible` обязана отвечать `false`, - а не поломка
/// инварианта, поэтому здесь стоят `try_`-варианты, а не паникующие.
pub(crate) fn unfold(sig: &Signature, value: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(Head::Global(name, levels, rows), spine) = &**value else {
        return None;
    };
    let definition = sig.lookup(name)?;
    // Нетотальное определение не разворачивается никогда: у него разворот мог
    // бы не закончиться уже на замкнутых аргументах. По §4.7 в типах его и не
    // встретишь - там стёртый фрагмент, - так что запрет ничего не стоит.
    //
    // Завершаемость сравнения он при этом **не** даёт: на открытых аргументах
    // расходятся и тотальные определения. За это отвечает `UNFOLD_LIMIT`.
    if !definition.total {
        return None;
    }
    // Запечатанное не разворачивается вовсе (§3.5): снаружи его тело - не
    // представление, а обещание, и сравнение обязано считать `M.T` атомом.
    // Цена названа дизайном: доказать про запечатанную структуру что-либо
    // вычислением нельзя, и законы она обязана экспортировать леммами.
    if definition.opaque {
        return None;
    }
    replayed(definition, levels, rows, spine)
}

/// δ-шаг **без** ворот тотальности и запечатывания - для исполнения.
///
/// Ворота стоят у сравнения, и обе их причины к исполнению не относятся.
/// Нетотальное определение запрещено разворачивать сравнению, потому что оно
/// обязано завершаться; исполнение нетотального обязано расходиться ровно там,
/// где расходится сама программа. Запечатанное сравнение считает атомом, потому
/// что снаружи его тело - обещание, а не представление (§3.5); исполнять
/// обещание нечем, и тело у него то же самое.
pub(crate) fn unfolded(sig: &Signature, value: &Rc<Value>) -> Option<Rc<Value>> {
    let Value::Neutral(Head::Global(name, levels, rows), spine) = &**value else {
        return None;
    };
    let definition = sig.lookup(name)?;
    replayed(definition, levels, rows, spine)
}

/// Тело определения с переигранным спайном - общее у обоих δ.
fn replayed(
    definition: &crate::sig::Definition,
    levels: &[crate::level::Level],
    rows: &Rc<[Row<Rc<Value>>]>,
    spine: &[Elim],
) -> Option<Rc<Value>> {
    // Аргументы-row подставляются **окружением**: метка несёт открытые термы,
    // и вложить их в замкнутое тело нечем (§3.2).
    let body = definition.unfolded(levels, Rc::clone(rows))?;
    spine.iter().try_fold(body, |callee, elim| match elim {
        Elim::App(argument) => try_apply(&callee, Rc::clone(argument)),
        Elim::Case(case) => try_eliminate_case(case, &callee),
        // Проекция из развёрнутого определения. Записью тело быть не обязано:
        // у модуля, объявленного выражением (`module M = F A`), тело - это
        // нейтраль, и проекция на ней **копится в спайне**, а не застревает.
        // Требуй здесь записи - и `None` отбросил бы уже сделанный δ-шаг
        // вместе с ним: `M.T` не разворачивалась бы вовсе, два применения
        // функтора к одному аргументу давали бы неконвертируемые типы, а
        // разница между `:` и `:>` у модуля-значения исчезала.
        Elim::Project(name) => matches!(&*callee, Value::Object(_) | Value::Neutral(..))
            .then(|| crate::eval::project(&callee, name)),
        // То же с переопределением: на записи пересобирает, на нейтрали копит.
        Elim::With(fields) => matches!(&*callee, Value::Object(_) | Value::Neutral(..))
            .then(|| crate::eval::with(&callee, fields.to_vec())),
    })
}

/// Сравнивает два телескопа полей - по одному полю, под предыдущими.
fn same_telescope(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Telescope,
    right: &Telescope,
) -> bool {
    // Закрытая запись - **телескоп**: порядок значим, потому что поле вправе
    // ссылаться на предыдущее (§4.2). Открытая зависимостей не имеет, и там
    // сравнение идёт по именам - иначе `{ x : A | r }` не сошлось бы с
    // `{ y : B, x : A }`, а ровно это row-полиморфизм и обещает.
    if left.is_open() || right.is_open() {
        return same_open(fuel, sig, metas, size, left, right);
    }
    if left.fields().len() != right.fields().len() {
        return false;
    }
    let mut earlier = Vec::with_capacity(left.fields().len());
    for (index, (a, b)) in left.fields().iter().zip(right.fields()).enumerate() {
        if a.name != b.name || a.mult != b.mult {
            return false;
        }
        let depth = size + u32::try_from(index).unwrap_or(0);
        let (x, y) = (left.at(index, &earlier), right.at(index, &earlier));
        if !convertible_within(fuel, sig, metas, depth, &x, &y) {
            return false;
        }
        earlier.push(Value::var(Lvl(depth)));
    }
    true
}

/// Сравнивает ряды, из которых хотя бы один открыт.
///
/// Общие метки сравниваются попарно, а расхождение уходит в хвост: то, чего
/// нет слева, обязан дать хвост левого, и наоборот.
///
/// # Остаток выражается, а не заводится
///
/// Равенство `{ общие, только-наши | l } ~ { общие, только-их | r }`
/// равносильно `l ~ { только-их | ρ }` и `r ~ { только-наши | ρ }` при общем
/// остатке `ρ`. Когда одна из разностей пуста, `ρ` **и есть** хвост той
/// стороны: свежая дырка не нужна, уравнение остаётся одно и решается прямо.
/// Отсюда же и самый частый случай - разностей нет вовсе, - где правило
/// сводится к `l ~ r` единичным законом (`{| r }` есть `r`, см.
/// [`crate::eval`]).
///
/// **Названная граница: обе разности непусты.** Тогда `ρ` не выражается ни
/// через что и его пришлось бы завести дыркой, а тип у неё - телескоп
/// контекста, которого сравнение не знает: оно бестиповое и типов связываний,
/// под которые спускается, не носит (§10 вопрос 80). Такое равенство
/// отвергается; чтобы в него попасть, нужны два ряда, каждый со своей меткой,
/// которой нет у другого.
fn same_open(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Telescope,
    right: &Telescope,
) -> bool {
    let (mine, yours) = (labelled(metas, size, left), labelled(metas, size, right));
    let (ours, theirs) = (&mine.labels, &yours.labels);
    for (name, ours) in ours {
        if let Some(theirs) = theirs.iter().find(|(it, _)| it == name) {
            if !convertible_within(fuel, sig, metas, size, ours, &theirs.1) {
                return false;
            }
        }
    }
    // Развёртка считает тип `i`-го поля под `size + i` переменными - её
    // собственными, - а собираемый ряд стоит при `size`. Пока поле на них не
    // ссылается, глубины расходятся безвредно: свободных переменных у типа
    // меньше `size`, и обратное чтение при `size` их адресует. Сошлись бы они
    // и на зависимом поле - но такого поля у открытой записи не бывает (§4.2),
    // а до этой проверки оно роняло процесс: обратное чтение при `size`
    // упиралось в уровень, которого при `size` нет.
    let missing = |from: &[(Name, Rc<Value>)], other: &[(Name, Rc<Value>)]| -> Option<Vec<Field>> {
        let mut fields = Vec::new();
        for (index, (name, ty)) in from.iter().enumerate() {
            if other.iter().any(|(it, _)| it == name) {
                continue;
            }
            let spread = u32::try_from(index).unwrap_or(u32::MAX);
            if quote(size + spread, ty).mentions_recent(0, spread) {
                return None;
            }
            fields.push(Field {
                name: Rc::clone(name),
                mult: Mult::One,
                ty: Rc::new(quote(size, ty)),
            });
        }
        Some(fields)
    };
    let (Some(only_ours), Some(only_theirs)) = (missing(ours, theirs), missing(theirs, ours))
    else {
        // Сравнить их этот алгоритм не берётся, и «не равны» здесь честнее
        // молчаливого принятия: цена - отвергнутая программа, которую §4.2 и
        // так не разрешает написать.
        return false;
    };
    match (mine.tail, yours.tail) {
        // Один открыт: недостающее обязан дать его хвост, а лишнего у
        // закрытой стороны быть не может.
        (Some(tail), None) => {
            only_ours.is_empty() && solved(fuel, sig, metas, size, &tail, only_theirs, None)
        }
        (None, Some(tail)) => {
            only_theirs.is_empty() && solved(fuel, sig, metas, size, &tail, only_ours, None)
        }
        // Оба открыты: остаток - хвост той стороны, которой нечего добавить.
        (Some(ours_tail), Some(theirs_tail)) => {
            let rest = |tail: &Rc<Value>| Some(quote(size, tail));
            if only_ours.is_empty() {
                solved(
                    fuel,
                    sig,
                    metas,
                    size,
                    &ours_tail,
                    only_theirs,
                    rest(&theirs_tail),
                )
            } else if only_theirs.is_empty() {
                solved(
                    fuel,
                    sig,
                    metas,
                    size,
                    &theirs_tail,
                    only_ours,
                    rest(&ours_tail),
                )
            } else {
                false
            }
        }
        // Развёртка хвостов сошла на нет: метки известны обе стороны, и
        // сравнение идёт по именам - зависимостей у открытого ряда нет.
        (None, None) => only_ours.is_empty() && only_theirs.is_empty(),
    }
}

/// Имена и типы полей ряда - под свежими переменными вместо предыдущих полей -
/// вместе с остатком, который метками не выражается.
///
/// Открытый ряд зависимостей не имеет, поэтому подставлять туда что-либо
/// осмысленное незачем: переменные нужны только чтобы телескоп дошёл до конца.
///
/// **Хвост, оказавшийся рядом, разворачивается.** `{ x | {y, z} }` и
/// `{ x, y, z }` описывают один набор меток, и пока хвост свёрнут, `y` не
/// видно: сравнение отказывало бы на ровном месте. Так выглядит запись,
/// прошедшая через функцию с написанным хвостом (`keep : {x : Nat | r} -> …`),
/// где `r` уже решён.
fn labelled(metas: &Metas, size: u32, telescope: &Telescope) -> Spread {
    let mut labels = Vec::with_capacity(telescope.fields().len());
    let mut current = telescope.clone();
    loop {
        let mut earlier = Vec::with_capacity(current.fields().len());
        for (index, field) in current.fields().iter().enumerate() {
            labels.push((Rc::clone(&field.name), current.at(index, &earlier)));
            // Переменные нумеруются сквозь развёртку: у полей из хвоста они
            // обязаны отличаться от полей головы.
            let depth = size + u32::try_from(labels.len() - 1).unwrap_or(0);
            earlier.push(Value::var(Lvl(depth)));
        }
        let Some(tail) = current.tail() else {
            return Spread { labels, tail: None };
        };
        // Решённая дырка разворачивается: `?r`, ставшая рядом, - это ряд.
        let tail = crate::solve::force(metas, &tail).unwrap_or(tail);
        match &*tail {
            Value::Row(inner) => current = inner.clone(),
            _ => {
                return Spread {
                    labels,
                    tail: Some(tail),
                };
            }
        }
    }
}

/// Ряд, развёрнутый по хвостам.
struct Spread {
    /// Метки и их типы - в порядке появления, головные первыми.
    labels: Vec<(Name, Rc<Value>)>,
    /// Остаток, метками не выразимый: нерешённая дырка или переменная.
    tail: Option<Rc<Value>>,
}

/// Сводит хвост с рядом из недостающих полей и, возможно, своего хвоста.
fn solved(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    tail: &Rc<Value>,
    fields: Vec<Field>,
    rest: Option<Term>,
) -> bool {
    let row = Term::Row(Fields {
        fields: fields.into(),
        tail: rest.map(Rc::new),
    });
    let expected = crate::eval::eval(&fresh_env(size), &row);
    convertible_within(fuel, sig, metas, size, tail, &expected)
}

/// Row значения с подставленным решением хвоста.
///
/// Нужна с тех пор, как решением хвоста стала row **с метками** (§3.4,
/// унификация scoped labels). `Metas::zonk_tail` такое решение не
/// разворачивает и не может: его тип - один хвост, а решение с метками хвостом
/// не выражается. Пока метки в решения не попадали, разницы не было; теперь
/// сравнение, взявшее row неразвёрнутой, сравнивало бы устаревшую.
///
/// Аргументы решения - термы, прочитанные при том же `size`, поэтому и
/// вычисляются они под тем же окружением.
pub(crate) fn expanded(metas: &Metas, size: u32, row: &Row<Rc<Value>>) -> Row<Rc<Value>> {
    let Some(Tail::Meta(meta)) = row.tail() else {
        return row.clone();
    };
    let Some(solution) = metas.row_solution(meta) else {
        return row.clone();
    };
    let solution = solution.map(|term| crate::eval::eval(&fresh_env(size), term));
    row.substituted(&expanded(metas, size, &solution))
}

/// Окружение из `size` свободных переменных - под ним читаются ряды.
fn fresh_env(size: u32) -> crate::value::Env {
    (0..size).fold(crate::value::Env::default(), |env, level| {
        env.extend(Value::var(Lvl(level)))
    })
}

/// Совпадают ли головы застрявших вычислений.
///
/// У определения аргументы уровня не сравниваются структурно, а
/// **унифицируются**: в них стоят метапеременные, и `Id{?l}` против `Id{2}` -
/// это не расхождение, а ограничение `?l ~ 2`. Структурное сравнение здесь
/// отвергло бы корректную программу, а у постулата - окончательно, потому что
/// разворачивать нечего.
fn same_head(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Head,
    right: &Head,
) -> bool {
    match (left, right) {
        (Head::Local(a), Head::Local(b)) => a == b,
        // Одна и та же нерешённая дырка - это одно и то же значение, и решать
        // тут нечего. Без этой строки `?m ū ≡ ?m ū` уходило бы в решение, где
        // проверка вхождения приняла бы его за цикл.
        (Head::Meta(a), Head::Meta(b)) => a == b,
        (Head::Global(name_a, levels_a, rows_a), Head::Global(name_b, levels_b, rows_b)) => {
            name_a == name_b
                && levels_a.len() == levels_b.len()
                && levels_a
                    .iter()
                    .zip(levels_b.iter())
                    .all(|(a, b)| metas.unify_levels(a, b))
                // Аргументы-row сравниваются формой, а их метки - аргументами:
                // атом row есть метка, несущая термы, поэтому равенство row
                // полно лишь с точностью до конвертируемости (§3.2).
                && rows_a.len() == rows_b.len()
                && rows_a
                    .iter()
                    .zip(rows_b.iter())
                    .all(|(a, b)| same_row(fuel, sig, metas, size, a, b))
        }
        _ => false,
    }
}

/// Равны ли две row - унификацией scoped labels (§3.4).
///
/// §3.4 разводит два действия, и здесь делается второе. Равенство - совпадение
/// хвостов и групп. **Унификация** - метки сопоставляются по имени, аргументы
/// унифицируются как обычные термы, а **остаток уходит в хвостовую
/// метапеременную**; отсутствие хвоста при непустом остатке даёт отказ.
///
/// Пока остаток никуда не уходил, сравнение требовало совпадения числа меток,
/// и `withLog pure1` при `withLog : (Bool -> {Log} Bool) -> …` отвергалось:
/// у чистого колбэка row после auto-lift есть дырка, решение `?m := {Log | e}`
/// единственно, а найти его было нечем. Обходилась дыра η-развёрткой
/// `\b -> pure1 b`, то есть higher-order-передача - та самая, которую §3.4
/// приводит мотивом правила погашения, - не писалась.
///
/// **Порядок: сначала форма, потом хвост.** Решение хвоста не откатывается, и
/// записанное до сравнения меток пережило бы неудачу этого сравнения.
///
/// Одноимённые метки сопоставляются попарно в порядке появления: порядок
/// внутри группы значим (§3.4), и лишние в конце группы и есть остаток.
fn same_row(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Row<Rc<Value>>,
    right: &Row<Rc<Value>>,
) -> bool {
    let (left, right) = (&expanded(metas, size, left), &expanded(metas, size, right));
    let mut ours: Vec<&Label<Rc<Value>>> = Vec::new();
    let mut theirs: Vec<&Label<Rc<Value>>> = Vec::new();
    let mut names: Vec<&Name> = Vec::new();
    for label in left.labels().iter().chain(right.labels()) {
        if !names.contains(&&label.name) {
            names.push(&label.name);
        }
    }
    for name in names {
        let mine: Vec<&Label<Rc<Value>>> =
            left.labels().iter().filter(|it| it.name == *name).collect();
        let yours: Vec<&Label<Rc<Value>>> = right
            .labels()
            .iter()
            .filter(|it| it.name == *name)
            .collect();
        let common = mine.len().min(yours.len());
        for (a, b) in mine.iter().zip(&yours).take(common) {
            if a.arguments.len() != b.arguments.len() {
                return false;
            }
            for (x, y) in a.arguments.iter().zip(&b.arguments) {
                if !convertible_within(fuel, sig, metas, size, x, y) {
                    return false;
                }
            }
        }
        ours.extend(mine.into_iter().skip(common));
        theirs.extend(yours.into_iter().skip(common));
    }

    let quoted = |labels: &[&Label<Rc<Value>>]| -> Vec<Label<Term>> {
        labels
            .iter()
            .map(|label| Label {
                name: Rc::clone(&label.name),
                arguments: label
                    .arguments
                    .iter()
                    .map(|argument| quote(size, argument))
                    .collect(),
            })
            .collect()
    };
    if ours.is_empty() && theirs.is_empty() {
        return metas.unify_tails(left.tail(), right.tail());
    }
    // Обе разности непусты - и это решается заведением **общего остатка**
    // (§10 вопрос 80): `{ū | ?l} ~ {v̄ | ?r}` равносильно `?l := {v̄ | ρ}` и
    // `?r := {ū | ρ}`, где ρ - то, чем оба ряда продолжаются одинаково.
    //
    // Записанное препятствие - «тип такой дырки есть телескоп контекста, а
    // сравнение бестиповое» - при измерении не подтвердилось: у row-дырки типа
    // нет вовсе, `fresh_row` его не спрашивает. Догадкой решение не является:
    // другого способа уравнять два открытых ряда нет, и ρ определяется
    // единственным образом.
    if !ours.is_empty() && !theirs.is_empty() {
        let (Some(Tail::Meta(mine)), Some(Tail::Meta(yours))) =
            (metas.zonk_tail(left.tail()), metas.zonk_tail(right.tail()))
        else {
            // Жёсткая переменная лишних меток не примет, а отсутствие хвоста -
            // тем более: там равенства действительно нет.
            return false;
        };
        // Один и тот же хвост с обеих сторон: решение содержало бы саму дырку.
        if mine == yours {
            return false;
        }
        let rho = metas.fresh_row();
        let (ours, theirs) = (quoted(&ours), quoted(&theirs));
        metas.solve_row(mine, Row::closing(theirs, rho.tail()));
        metas.solve_row(yours, Row::closing(ours, rho.tail()));
        return true;
    }
    // Остаток одной стороны обязан уйти в хвост другой. Хвост этот обязан быть
    // дыркой: жёсткая переменная лишних меток не примет, а отсутствие хвоста -
    // тем более.
    let (rest, absorbing, keeping) = if theirs.is_empty() {
        (quoted(&ours), right.tail(), left.tail())
    } else {
        (quoted(&theirs), left.tail(), right.tail())
    };
    let Some(Tail::Meta(meta)) = metas.zonk_tail(absorbing) else {
        return false;
    };
    // `?m := {остаток | ?m}` не строится: решение содержало бы саму дырку.
    if metas.zonk_tail(keeping) == Some(Tail::Meta(meta)) {
        return false;
    }
    metas.solve_row(meta, Row::closing(rest, keeping));
    true
}

/// Совпадают ли элиминаторы в одной позиции спайна.
fn same_elim(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Elim,
    right: &Elim,
) -> bool {
    match (left, right) {
        (Elim::App(a), Elim::App(b)) => convertible_within(fuel, sig, metas, size, a, b),
        (Elim::Case(a), Elim::Case(b)) => same_case(fuel, sig, metas, size, a, b),
        (Elim::Project(a), Elim::Project(b)) => a == b,
        // Порядок написанного значим: `{ p | x = v, x = w }` поверхность не
        // пишет, но затенение делает две последовательности разными, если они
        // разошлись местами. Сравнение поэтому попарное.
        (Elim::With(a), Elim::With(b)) => {
            a.len() == b.len()
                && a.iter().zip(b.iter()).all(|((one, ours), (two, theirs))| {
                    one == two && convertible_within(fuel, sig, metas, size, ours, theirs)
                })
        }
        _ => false,
    }
}

/// Совпадают ли два застрявших разбора.
///
/// Мотивы сравниваются, хотя на результат они не влияют: разбор застрял, а
/// значит ни одна ветвь не выбрана, и при любом значении скрутинируемого два
/// разбора с одинаковыми ветвями дадут одно и то же. Сравнение здесь
/// **консервативно** - оно может отвергнуть конвертируемые термы. Отбросить
/// мотив нельзя: он часть терма и виден в типе результата, и признав такие
/// термы равными, конвертируемость перестала бы сохранять типизацию.
fn same_case(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<StuckCase>,
    right: &Rc<StuckCase>,
) -> bool {
    // `consumed` не сравнивается сознательно. Кратность потребления - учётная
    // аннотация, а не часть вычисления: ι-редукция её не смотрит, и два
    // разбора, различающиеся только ею, дают одно значение. Сравнивай мы её,
    // мотив, собранный элаборацией с `r = 1`, перестал бы совпадать с
    // написанным при `r = ω`, то есть отвергались бы корректные программы.
    // Учёт кратностей при этом не страдает: вектор использований считает
    // `infer_case` по самому терму, а не через конвертируемость.
    left.data == right.data
        && left.params == right.params
        && left.levels.len() == right.levels.len()
        && left
            .levels
            .iter()
            .zip(right.levels.iter())
            .all(|(a, b)| metas.unify_levels(a, b))
        && convertible_within(fuel, sig, metas, size, &left.motive, &right.motive)
        && left.branches.len() == right.branches.len()
        && left.branches.iter().zip(&right.branches).all(|(a, b)| {
            a.constructor == b.constructor
                && convertible_within(fuel, sig, metas, size, &a.body, &b.body)
        })
}

/// Сравнение без разворота определений.
fn rigid(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: &Rc<Value>,
    right: &Rc<Value>,
) -> bool {
    match (&**left, &**right) {
        // Универсум и сорт рядов сравниваются уровнем. Смешать их нельзя -
        // варианты разные, - а правило у них одно.
        // Сорт `Effect` один на всех: сравнивать в нём нечего - ни уровня,
        // ни аргументов у него нет.
        (Value::EffectKind, Value::EffectKind) => true,
        (Value::Universe(a), Value::Universe(b)) | (Value::RowKind(a), Value::RowKind(b)) => {
            metas.unify_levels(a, b)
        }

        // Запись - телескоп, и сравнивается она как телескоп: имена и порядок
        // синтаксически, типы полей - конвертируемостью под предыдущими
        // полями. Порядок значим потому же, почему значим у `Pi`: поле вправе
        // ссылаться на предыдущее, и перестановка меняет, на что именно
        // (решение 2026-08-29, §4.2). Кратность - часть типа, как у `Pi`.
        (Value::Record(a), Value::Record(b)) => same_telescope(fuel, sig, metas, size, a, b),

        // Ряд - **набор меток**, а не телескоп: порядок в нём не значит ничего
        // (§4.2), и закрытый сравнивается по именам так же, как открытый.
        // Позиционное сравнение отвергало `{y, z}` против `{z, y}` - два
        // написания одного ряда, - и попасть в него было легко: закрытые ряды
        // рождаются штатно, их строит проверка лишних полей открытой записи.
        (Value::Row(a), Value::Row(b)) => same_open(fuel, sig, metas, size, a, b),

        // Значения записи - по именам. Порядок полей значения семантически
        // инертен: вычисление считает их в одном окружении, а проекция и
        // переопределение ищут по имени. Сравнение же требовало совпадения
        // позиций, опираясь на инвариант «поля хранятся в порядке типа» - а
        // приводит к нему только пересборка под `{ p | … }`, тогда как литерал
        // остаётся написанным. Отсюда отказ на двух значениях одного типа,
        // различающихся только порядком написания.
        (Value::Object(a), Value::Object(b)) => {
            a.len() == b.len()
                && a.iter().all(|(name, x)| {
                    b.iter()
                        .find(|(it, _)| it == name)
                        .is_some_and(|(_, y)| convertible_within(fuel, sig, metas, size, x, y))
                })
        }

        // η для записи: `p` и `{x = p.x, y = p.y}` - одно значение. Сравнение
        // здесь бестиповое, поэтому раскрывается **застрявшая** сторона: типа,
        // из которого взять список полей, у неё нет, а у собранной он есть, и
        // хорошо типизированными их делает то, что сравнивают их при одном
        // типе. Без правила запись, разобранная и собранная заново, отличалась
        // бы от исходной - а это ровно то, что делает всякий проход по полям.
        (Value::Object(fields), Value::Neutral(..)) => fields.iter().all(|(name, value)| {
            let projected = crate::eval::project(right, name);
            convertible_within(fuel, sig, metas, size, value, &projected)
        }),
        (Value::Neutral(..), Value::Object(fields)) => fields.iter().all(|(name, value)| {
            let projected = crate::eval::project(left, name);
            convertible_within(fuel, sig, metas, size, &projected, value)
        }),

        (Value::Neutral(head_a, spine_a), Value::Neutral(head_b, spine_b)) => {
            same_head(fuel, sig, metas, size, head_a, head_b)
                && spine_a.len() == spine_b.len()
                && spine_a
                    .iter()
                    .zip(spine_b)
                    .all(|(a, b)| same_elim(fuel, sig, metas, size, a, b))
        }

        // Связывание - часть типа функции целиком: `(1 x : A) -> B` и
        // `(ω x : A) -> B` разные типы, и `{a : A} -> B` с `(a : A) -> B`
        // тоже. Видимость сравнивается по тому же доводу, что кратность:
        // считай их одним типом - и значение одного встало бы на место
        // другого, а вставка имплиситов перестала бы быть определённой.
        //
        // Row - на тех же правах (§3.4): `A -> {IO} B` и `A -> B` различаются,
        // потому что различается контракт применения. Формы сравниваются
        // синтаксически - метки в каноническом порядке, - а аргументы меток
        // конвертируемостью, как всякие термы.
        (
            Value::Pi(binder_a, _, domain_a, row_a, codomain_a),
            Value::Pi(binder_b, _, domain_b, row_b, codomain_b),
        ) => {
            binder_a == binder_b
                && same_row(fuel, sig, metas, size, row_a, row_b)
                && convertible_within(fuel, sig, metas, size, domain_a, domain_b)
                && convertible_under(
                    fuel,
                    sig,
                    metas,
                    size,
                    |v| codomain_a.apply(v),
                    |v| codomain_b.apply(v),
                )
        }

        // Кратность лямбды не сравнивается - иначе ломается транзитивность,
        // см. `comparing_lambda_multiplicities_would_break_transitivity`.
        (Value::Lam(_, _, body_a), Value::Lam(_, _, body_b)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| body_a.apply(v),
            |v| body_b.apply(v),
        ),

        // η: функция равна своему развёрнутому виду `\x -> f x`. Без этого
        // правила `f` и `\x -> f x` были бы разными термами.
        //
        // Разворачивается только против застрявшего значения. Против `Pi` или
        // `Universe` лямбда неконвертируема в любом случае, а применить их
        // нельзя - попытка была бы обращением к `apply` с не-функцией.
        (Value::Lam(_, _, body), Value::Neutral(..)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| body.apply(v),
            |v| apply(right, v),
        ),
        (Value::Neutral(..), Value::Lam(_, _, body)) => convertible_under(
            fuel,
            sig,
            metas,
            size,
            |v| apply(left, v),
            |v| body.apply(v),
        ),

        _ => false,
    }
}

/// Сравнивает под свежим связыванием.
fn convertible_under(
    fuel: u32,
    sig: &Signature,
    metas: &mut Metas,
    size: u32,
    left: impl FnOnce(Rc<Value>) -> Rc<Value>,
    right: impl FnOnce(Rc<Value>) -> Rc<Value>,
) -> bool {
    let fresh = Value::var(Lvl(size));
    convertible_within(
        fuel,
        sig,
        metas,
        size + 1,
        &left(Rc::clone(&fresh)),
        &right(fresh),
    )
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::row::{Label, Row, RowVar, Tail};
    use crate::term::Binder;
    use crate::visibility::Visibility;

    use super::{UNFOLD_LIMIT, convertible};
    use crate::eval::eval;
    use crate::mult::Mult;
    use crate::term::Term;
    use crate::value::{Env, Lvl, Value};

    fn lam(body: Term) -> Term {
        Term::Lam(Mult::Many, "x".into(), Rc::new(body))
    }

    fn pi(mult: Mult, domain: Term, codomain: Term) -> Term {
        rowed(mult, Row::empty(), domain, codomain)
    }

    fn rowed(mult: Mult, row: Row<Term>, domain: Term, codomain: Term) -> Term {
        Term::Pi(
            Binder::explicit(mult),
            "x".into(),
            Rc::new(domain),
            row,
            Rc::new(codomain),
        )
    }

    fn effect(name: &str, arguments: Vec<Term>) -> Row<Term> {
        Row::new([Label {
            name: name.into(),
            arguments,
        }])
    }

    /// Вычисляет оба терма в контексте с `free` свободными переменными.
    fn conv_in(free: u32, left: &Term, right: &Term) -> bool {
        let env = (0..free).fold(Env::default(), |env, level| {
            env.extend(Value::var(Lvl(level)))
        });
        let signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        convertible(
            &signature,
            &mut metas,
            free,
            &eval(&env, left),
            &eval(&env, right),
        )
    }

    fn conv(left: &Term, right: &Term) -> bool {
        conv_in(0, left, right)
    }

    #[test]
    fn beta_equal_terms_are_convertible() {
        let reduced = Term::universe(0);
        let redex = lam(Term::var(0)).apply([Term::universe(0)]);
        assert!(conv(&redex, &reduced));
    }

    #[test]
    fn names_do_not_matter() {
        let x = Term::Lam(Mult::Many, "x".into(), Rc::new(Term::var(0)));
        let y = Term::Lam(Mult::Many, "y".into(), Rc::new(Term::var(0)));
        assert!(conv(&x, &y));
    }

    #[test]
    fn eta_expansion_is_invisible() {
        // f  ==  \x -> f x, где f свободна.
        let f = Term::var(0);
        let expanded = lam(Term::var(1).apply([Term::var(0)]));
        assert!(conv_in(1, &f, &expanded));
        assert!(conv_in(1, &expanded, &f), "и в обратную сторону");
    }

    #[test]
    fn distinct_universes_are_not_convertible() {
        // Без кумулятивности Type 0 не является Type 1.
        assert!(!conv(&Term::universe(0), &Term::universe(1)));
    }

    #[test]
    fn equivalent_level_expressions_are_convertible() {
        use crate::level::{Level, LevelVar};

        let u = Level::Var(LevelVar(0));
        let left = Term::Universe(u.clone().max(Level::Zero));
        let right = Term::Universe(u);
        assert!(conv(&left, &right));
    }

    #[test]
    fn multiplicity_distinguishes_function_types() {
        let linear = pi(Mult::One, Term::universe(0), Term::universe(0));
        let unrestricted = pi(Mult::Many, Term::universe(0), Term::universe(0));
        assert!(
            !conv(&linear, &unrestricted),
            "(1 x : A) -> B ≠ (ω x : A) -> B"
        );
        assert!(conv(&linear, &linear.clone()));
    }

    #[test]
    fn erased_and_linear_pi_differ_too() {
        let erased = pi(Mult::Zero, Term::universe(0), Term::universe(0));
        let linear = pi(Mult::One, Term::universe(0), Term::universe(0));
        assert!(!conv(&erased, &linear));
    }

    #[test]
    fn neutral_spines_are_compared_pointwise() {
        let applied_once = Term::var(0).apply([Term::universe(0)]);
        let applied_twice = Term::var(0).apply([Term::universe(0), Term::universe(0)]);
        assert!(conv_in(1, &applied_once, &applied_once.clone()));
        assert!(
            !conv_in(1, &applied_once, &applied_twice),
            "разная длина спайна"
        );

        let other_argument = Term::var(0).apply([Term::universe(1)]);
        assert!(!conv_in(1, &applied_once, &other_argument));
    }

    #[test]
    fn different_heads_are_not_convertible() {
        assert!(!conv_in(2, &Term::var(0), &Term::var(1)));
    }

    /// Почему кратность лямбды не сравнивается - регрессионный тест на решение.
    ///
    /// Если бы сравнивалась, конвертируемость перестала бы быть транзитивной:
    /// обе лямбды η-равны одной и той же `f`, а между собой различались бы.
    /// Свободу выбора это не даёт - у корректно типизированных термов под одним
    /// `Pi` кратность совпадает по построению.
    #[test]
    fn comparing_lambda_multiplicities_would_break_transitivity() {
        let f = Term::var(0);
        let expand = |mult| {
            Term::Lam(
                mult,
                "x".into(),
                Rc::new(Term::var(1).apply([Term::var(0)])),
            )
        };

        assert!(conv_in(1, &expand(Mult::One), &f));
        assert!(conv_in(1, &f, &expand(Mult::Zero)));
        assert!(
            conv_in(1, &expand(Mult::One), &expand(Mult::Zero)),
            "иначе транзитивность через f нарушена"
        );
    }

    /// Нормальные формы **не** канонические представители классов
    /// конвертируемости: обратное чтение не выполняет η-развёртку, потому что
    /// не знает типов.
    ///
    /// Это упирается в §7.3: content addressing требует, чтобы семантически
    /// одинаковые определения давали одинаковый хеш. Здесь два конвертируемых
    /// терма одного типа дают разные нормальные формы, значит и разные хеши.
    /// Лечится типизированным обратным чтением (η-длинные нормальные формы) -
    /// работа не этого среза.
    #[test]
    fn eta_equal_terms_have_different_normal_forms() {
        use crate::eval::quote;

        let f = Term::var(0);
        let expanded = Term::Lam(
            Mult::Many,
            "x".into(),
            Rc::new(Term::var(1).apply([Term::var(0)])),
        );

        let env = Env::default().extend(Value::var(Lvl(0)));
        assert!(conv_in(1, &f, &expanded), "конвертируемы");
        assert_ne!(
            quote(1, &eval(&env, &f)),
            quote(1, &eval(&env, &expanded)),
            "но нормальные формы различаются"
        );
    }

    /// Разворот определения не обязан принимать накопленный спайн.
    ///
    /// η-правило дописывает `Elim::App` к любой нейтрали, поэтому сравнение
    /// лямбды с `c : Type 1 = Type 0` доходит до попытки применить `Type 0` к
    /// аргументу. Значения здесь разных типов, и контракт функции - ответить
    /// `false`, а не упасть: раньше здесь была паника в `eval`.
    #[test]
    fn unfolding_a_non_function_is_a_refusal_not_a_panic() {
        let mut signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        signature
            .define(
                &mut metas,
                "c",
                Mult::Many,
                0,
                Term::universe(1),
                Some(Term::universe(0)),
            )
            .expect("определение корректно");
        let mut metas = crate::meta::Metas::default();

        let lambda = eval(&Env::default(), &lam(Term::var(0)));
        let constant = eval(&Env::default(), &Term::constant("c"));
        assert!(!convertible(&signature, &mut metas, 0, &lambda, &constant));
        assert!(
            !convertible(&signature, &mut metas, 0, &constant, &lambda),
            "и в обратную сторону"
        );
    }

    #[test]
    fn a_row_parameter_is_substituted_when_the_definition_unfolds() {
        // Подстановка row идёт **окружением**, а не по терму: метка несёт
        // открытые термы, и вложить их в замкнутое тело нечем (§3.2). Здесь
        // `f{IO}` разворачивается в стрелку с row `{IO}`, а не с параметром.
        let mut signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        let open = Row::closing([], Some(Tail::Var(RowVar(0))));
        let body = rowed(Mult::Many, open, Term::universe(0), Term::universe(0));
        let member = crate::sig::Member::definition("f", Mult::Many, Term::universe(1))
            .with_arity(0, 1)
            .with_body(body);
        signature
            .declare(&mut metas, &crate::sig::Group::of(member))
            .expect("`f` корректно");

        let label = Label {
            name: "IO".into(),
            arguments: Vec::new(),
        };
        let applied = Term::Const(
            "f".into(),
            Rc::from([]),
            crate::term::Rows::new([Row::new([label])]),
        );
        let unfolded = super::whnf(&signature, &eval(&Env::default(), &applied));
        let Value::Pi(_, _, _, row, _) = &*unfolded else {
            panic!("разворот даёт стрелку, получено {unfolded}");
        };
        assert_eq!(row.labels().len(), 1, "аргумент подставился");
        assert_eq!(row.tail(), None, "параметра не осталось");
    }

    /// Топливо разворота тратится вдоль пути, а не на всё сравнение.
    ///
    /// Иначе конвертируемость зависела бы от ширины типа: `k` стрелок, каждая
    /// с одним редексом, признавались бы равными при `k <= 128` и разными
    /// дальше, то есть из `A ≡ A'` и `B ≡ B'` не следовало бы
    /// `(A -> B) ≡ (A' -> B')`.
    #[test]
    fn fuel_is_spent_along_a_path_not_across_the_width() {
        let mut signature = crate::sig::Signature::default();
        let mut metas = crate::meta::Metas::default();
        signature
            .postulate(&mut metas, "Nat", Mult::Many, 0, Term::universe(0))
            .expect("Nat корректен");
        signature
            .postulate(&mut metas, "zero", Mult::Many, 0, Term::constant("Nat"))
            .expect("zero корректен");
        signature
            .define(
                &mut metas,
                "id",
                Mult::Many,
                0,
                pi(Mult::Many, Term::constant("Nat"), Term::constant("Nat")),
                Some(lam(Term::var(0))),
            )
            .expect("id корректна");
        signature
            .postulate(
                &mut metas,
                "F",
                Mult::Many,
                0,
                pi(Mult::Zero, Term::constant("Nat"), Term::universe(0)),
            )
            .expect("F корректна");

        // `(0 _ : F n) -> … k раз … -> Type 0`, где слева `n` под редексом либо
        // уже сведённое. Каждая стрелка стоит ровно один разворот.
        let chain = |redex: bool| {
            let index = if redex {
                Term::constant("id").apply([Term::constant("zero")])
            } else {
                Term::constant("zero")
            };
            (0..UNFOLD_LIMIT + 8).fold(Term::universe(0), |tail, _| {
                Term::Pi(
                    Binder::explicit(Mult::Zero),
                    "_".into(),
                    Rc::new(Term::constant("F").apply([index.clone()])),
                    Row::empty(),
                    Rc::new(tail),
                )
            })
        };

        let mut metas = crate::meta::Metas::default();
        let left = eval(&Env::default(), &chain(true));
        let right = eval(&Env::default(), &chain(false));
        assert!(
            convertible(&signature, &mut metas, 0, &left, &right),
            "ширина типа не должна расходовать общий запас разворотов"
        );
    }

    #[test]
    fn convertibility_is_an_equivalence_relation() {
        let terms = [
            Term::universe(0),
            lam(Term::var(0)),
            lam(lam(Term::var(1))),
            pi(Mult::One, Term::universe(0), Term::universe(0)),
        ];

        for left in &terms {
            assert!(conv(left, left), "рефлексивность");
            for right in &terms {
                assert_eq!(conv(left, right), conv(right, left), "симметричность");
                for middle in &terms {
                    if conv(left, middle) && conv(middle, right) {
                        assert!(conv(left, right), "транзитивность");
                    }
                }
            }
        }
    }

    #[test]
    fn a_row_is_part_of_the_function_type() {
        // §3.4: row описывает, что происходит при применении, и стоит на тех
        // же правах, что кратность. `A -> {IO} B` и `A -> B` - разные типы,
        // ровно как `(1 x : A) -> B` и `(ω x : A) -> B`.
        let pure = pi(Mult::Many, Term::universe(0), Term::universe(0));
        let effectful = rowed(
            Mult::Many,
            effect("IO", Vec::new()),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(!conv_in(0, &pure, &effectful), "чистая против эффектной");
        assert!(conv_in(0, &effectful, &effectful.clone()));
    }

    #[test]
    fn row_arguments_of_a_constant_are_compared() {
        // Ссылка на определение несёт два списка аргументов, и различаются они
        // оба: `f{IO}` и `f{State}` - разные значения, ровно как `f{0}` и
        // `f{1}`. Метки при этом сравниваются формой, а их аргументы -
        // конвертируемостью (§3.2).
        let label = |name: &str| Label {
            name: name.into(),
            arguments: Vec::new(),
        };
        let applied = |name: &str| {
            Term::Const(
                "f".into(),
                Rc::from([]),
                crate::term::Rows::new([Row::new([label(name)])]),
            )
        };
        assert!(conv_in(0, &applied("IO"), &applied("IO")));
        assert!(
            !conv_in(0, &applied("IO"), &applied("State")),
            "разные аргументы-row - разные значения"
        );
    }

    #[test]
    fn two_row_holes_are_unified_not_compared() {
        // После auto-lift у каждой сигнатуры своя дырка в хвосте, и два
        // употребления одного имени приходят с разными. Сравнение их не
        // различает, а **сводит** - это scoped labels §3.4 в той части, что
        // касается хвоста.
        let mut metas = crate::meta::Metas::default();
        let signature = crate::sig::Signature::default();
        let hole = |metas: &mut crate::meta::Metas| {
            let Some(tail) = metas.fresh_row().tail() else {
                unreachable!("свежая row открыта дыркой")
            };
            rowed(
                Mult::Many,
                Row::closing(
                    [Label {
                        name: "IO".into(),
                        arguments: Vec::new(),
                    }],
                    Some(tail),
                ),
                Term::universe(0),
                Term::universe(0),
            )
        };
        let left = hole(&mut metas);
        let right = hole(&mut metas);
        let (left, right) = (eval(&Env::default(), &left), eval(&Env::default(), &right));
        assert!(
            convertible(&signature, &mut metas, 0, &left, &right),
            "две дырки сводятся, а не расходятся"
        );
    }

    #[test]
    fn a_tail_is_part_of_the_row() {
        // Хвост - такая же часть row, как метки: `{IO}` означает «ровно `IO`»,
        // `{IO | e}` - «`IO` и что угодно ещё», и это разные обещания.
        // Сравниваются хвосты синтаксически: решать дырку - работа унификации.
        let closed = rowed(
            Mult::Many,
            effect("IO", Vec::new()),
            Term::universe(0),
            Term::universe(0),
        );
        let open = |index| {
            rowed(
                Mult::Many,
                Row::closing(
                    [Label {
                        name: "IO".into(),
                        arguments: Vec::new(),
                    }],
                    Some(Tail::Var(RowVar(index))),
                ),
                Term::universe(0),
                Term::universe(0),
            )
        };
        assert!(!conv_in(0, &closed, &open(0)), "закрытая против открытой");
        assert!(!conv_in(0, &open(0), &open(1)), "разные параметры");
        assert!(conv_in(0, &open(0), &open(0)));
    }

    #[test]
    fn row_arguments_are_compared_up_to_conversion() {
        // Аргументы метки - обычные термы, поэтому сравниваются так же, как
        // всё прочее: с точностью до вычисления, а не по написанию.
        let redex = Term::App(Rc::new(lam(Term::var(0))), Rc::new(Term::universe(0)));
        let written = rowed(
            Mult::Many,
            effect("State", vec![Term::universe(0)]),
            Term::universe(0),
            Term::universe(0),
        );
        let computed = rowed(
            Mult::Many,
            effect("State", vec![redex]),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(
            conv_in(0, &written, &computed),
            "`(\\x -> x) Type 0` есть `Type 0`"
        );

        let other = rowed(
            Mult::Many,
            effect("State", vec![Term::universe(1)]),
            Term::universe(0),
            Term::universe(0),
        );
        assert!(
            !conv_in(0, &written, &other),
            "разные аргументы - разные типы"
        );
    }

    #[test]
    fn labels_are_ordered_canonically_but_not_within_a_group() {
        // Группы упорядочены по имени, поэтому написание не влияет; порядок
        // внутри группы значим - внутренний хендлер перехватывает раньше
        // внешнего (§4.1), и переставить их значит изменить тип.
        let row = |labels: Vec<(&str, u32)>| {
            Row::new(labels.into_iter().map(|(name, level)| Label {
                name: name.into(),
                arguments: vec![Term::universe(level)],
            }))
        };
        let ty = |labels| {
            rowed(
                Mult::Many,
                row(labels),
                Term::universe(0),
                Term::universe(0),
            )
        };
        assert!(
            conv_in(
                0,
                &ty(vec![("A", 0), ("B", 1)]),
                &ty(vec![("B", 1), ("A", 0)])
            ),
            "порядок групп канонический"
        );
        assert!(
            !conv_in(
                0,
                &ty(vec![("A", 0), ("A", 1)]),
                &ty(vec![("A", 1), ("A", 0)])
            ),
            "порядок внутри группы значим"
        );
    }

    #[test]
    fn visibility_is_part_of_the_function_type() {
        // §4.1: `{a : A} -> B` и `(a : A) -> B` - разные типы. Считай их одним,
        // и значение одного встало бы на место другого, а вставка имплиситов
        // перестала бы быть определённой.
        let visible = |visibility| {
            Term::Pi(
                Binder {
                    mult: Mult::Many,
                    visibility,
                },
                "x".into(),
                Rc::new(Term::universe(0)),
                Row::empty(),
                Rc::new(Term::universe(0)),
            )
        };
        let explicit = visible(Visibility::Explicit);
        let implicit = visible(Visibility::Implicit);
        assert!(!conv_in(0, &explicit, &implicit));
        assert!(conv_in(0, &implicit, &implicit.clone()));
        assert_eq!(
            implicit.to_string(),
            "{ω x : Type 0} -> Type 0",
            "вид скобок несёт связывание"
        );
    }
}

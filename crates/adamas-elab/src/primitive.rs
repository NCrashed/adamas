//! `Primitive` - класс дорожки вектора и вывод его инстансов (§4.9).
//!
//! Устроен по образцу [`crate::flat`] и по тому же доводу: класс объявляется
//! программой, как объявляются `Bool` для `if` и `Flat` для укладки, а инстансы
//! **руками не пишутся** - их вычисляет компилятор. Объявление такого инстанса
//! отвергается.
//!
//! # Чем он не `Flat`
//!
//! Перечни инстансов расходятся, и §4.9 говорит это дословно: «SIMD-lane тип
//! обязан быть плоским, но плоский тип lane'ом быть не обязан. Списки инстансов
//! не совпадают намеренно». Здесь инстанс имеют ровно десять примитивов §4.11 и
//! ничего сверх: запись `Vec3` плоская, но дорожкой быть не может - §4.9
//! отводит ей отдельный абзац («ширина `Simd` есть число обрабатываемых
//! сущностей, а не число компонент величины»), - и `Ref r Packet` тем более.
//! Это и есть та работа, ради которой класс в §4.9 заведён.
//!
//! # Два расхождения с §4.9, оба названные
//!
//! *Метод типизирован `Layout`, а не `SIMDLayout`.* §4.9 пишет
//! `simdLayout : SIMDLayout` - «size + alignment для SIMD-операций». Отдельного
//! descriptor'а здесь нет, потому что сказать ему нечего: тот же §4.9 ниже
//! отказывается от пере-выравнивания («выравнивание натуральное, не SIMD-ное»),
//! а без него размер и граница дорожки - ровно те, что отдаёт `Flat`, и второй
//! счёт разошёлся бы с первым молча.
//!
//! *Суперкласса `{Flat a}` нет.* §4.9 объявляет `class {Flat a} => Primitive a`.
//! Здесь класс объявляется без суперкласса, и обещание его держится не
//! объявлением, а выводом: инстанс есть только у примитива, а примитив плоский
//! по построению. Суперкласс добавил бы в словарь второе поле, которое никто не
//! читает, и завёл бы порядок объявления между двумя выводимыми классами.

use std::rc::Rc;

use adamas_core::check::check_within;
use adamas_core::conv::whnf_solved;
use adamas_core::ctx::Ctx;
use adamas_core::eval::eval;
use adamas_core::meta::Metas;
use adamas_core::prim::{Prim, PrimTy};
use adamas_core::sig::Signature;
use adamas_core::source::Span;
use adamas_core::term::{Name, Term};
use adamas_core::value::{Env, Value};
use adamas_parser::ast::Symbol;

use crate::class::{abstracted, abstracted_pi, binders_of, goal_of, written};
use crate::error::ElabError;

/// Имя класса. Написано в ядре: тип операции над вектором называет тот же
/// класс, и второе написание разошлось бы молча.
pub(crate) const PRIMITIVE: &str = adamas_core::prim::PRIMITIVE;

/// Единственный метод класса - см. шапку модуля про его тип.
pub(crate) const SIMD_LAYOUT: &str = "simdLayout";

/// Поля дескриптора - те же, что у `Flat` (§4.11).
const SIZE: &str = "size";
const ALIGN: &str = "align";

/// Словарь `Primitive τ`, выведенный по типу, - решение дырки разрешения.
///
/// `ty` - тип дырки: телескоп, оканчивающийся целью; `goal` - сама цель,
/// приведённая к нормальной форме под этим телескопом.
///
/// # Errors
///
/// Тип дорожкой быть не может - отказ называет его; либо класс объявлен не так,
/// как написано в §4.9.
pub(crate) fn derive(
    signature: &Signature,
    metas: &mut Metas,
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
    // Цель - применение класса к единственному аргументу: форму `class
    // Primitive a` проверяет объявление, поэтому здесь она уже такая.
    let Term::App(_, argument) = goal else {
        return Err(ElabError::PrimitiveShape {
            why: "класс `Primitive` объявляется одним параметром (§4.9)",
            span,
        });
    };
    let subject = ctx.eval(argument);
    let lane = lane_of(signature, metas, &subject).ok_or_else(|| ElabError::NoInstance {
        written: written(&Rc::from(PRIMITIVE), &[shown(signature, metas, &subject)]),
        span,
    })?;
    let solution = abstracted(&binders, descriptor(lane));
    // Сверка словаря с приведённой целью - тот же порядок и та же причина, что
    // у `Flat`: цель может быть полиморфна по уровню, а словарь нет.
    let checked = abstracted_pi(&binders, goal_of(goal).clone());
    check_within(&Ctx::new(signature), metas, &solution, &checked).map_err(|_| {
        ElabError::PrimitiveShape {
            why: "словарь `Primitive` не сошёлся с объявленным классом: метод у него \
                  один - `simdLayout : Layout`, а `Layout` есть \
                  `{ size : UInt32, align : UInt32 }` (§4.9, §4.11)",
            span,
        }
    })?;
    Ok(eval(&Env::default(), &solution))
}

/// Примитивный тип, стоящий за значением, - если он там стоит.
///
/// Синоним разворачивается: `Float` есть `Float64` (§4.3), и представление есть
/// свойство типа, а не его написания. Всё прочее - запись, семейство,
/// переменная, функция - дорожкой не является, и `None` здесь и есть отказ.
fn lane_of(signature: &Signature, metas: &Metas, subject: &Rc<Value>) -> Option<PrimTy> {
    match &*whnf_solved(signature, metas, subject) {
        Value::Prim(Prim::Ty(prim)) => Some(*prim),
        _ => None,
    }
}

/// Имя типа для сообщения об отказе.
fn shown(signature: &Signature, metas: &Metas, subject: &Rc<Value>) -> Symbol {
    let reduced = whnf_solved(signature, metas, subject);
    match &*reduced {
        Value::Neutral(adamas_core::value::Head::Global(name, ..), _) => Rc::from(&**name),
        Value::Prim(prim) => Rc::from(prim.to_string().as_str()),
        other => Rc::from(other.to_string().as_str()),
    }
}

/// Словарь `{ simdLayout = { size = …, align = … } }` термом.
///
/// Числа - биты `UInt32`, как у `Flat` (§4.11, вопрос 152). Выравнивание равно
/// размеру: §4.9 отказался от пере-выравнивания, и дорожка стоит по своей
/// собственной границе, а не по границе регистра.
fn descriptor(lane: PrimTy) -> Term {
    let numeral = |value: u32| Term::Prim(Prim::literal(PrimTy::UInt32, u64::from(value)));
    let written = Term::Object(Rc::from([
        (Name::from(SIZE), Rc::new(numeral(lane.size()))),
        (Name::from(ALIGN), Rc::new(numeral(lane.size()))),
    ]));
    Term::Object(Rc::from([(
        Name::from(SIMD_LAYOUT),
        Rc::new(written),
    )]))
}

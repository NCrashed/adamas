//! Понижение термов ядра в [`ir`](crate::ir).
//!
//! Берётся **чистый фрагмент**: семейства и конструкторы, функции и применение,
//! разбор, рекурсия, `let`. Эффектов, хендлеров и резумпций здесь нет - им
//! отвечает вторая форма понижения (§13, 2026-09-08), а она приходит отдельно.
//! Всё, что во фрагмент не входит, отвергается названной причиной: молча
//! посчитать не то хуже, чем не посчитать.
//!
//! # Что здесь повторено за машиной, а не придумано заново
//!
//! **Стирание аргумента.** Машина стирает аргумент, когда вызываемое -
//! глобальное имя, а связывание его **типа** на этой позиции нулевое
//! (`adamas-interp/src/machine.rs`, `erases`). Кратность самой лямбды признаком
//! не служит: решение дырки терма есть цепочка лямбд при `0`, и значения в них
//! настоящие. Здесь ровно то же правило и ровно по тому же источнику - тип из
//! сигнатуры.
//!
//! **Поля ветви.** Ветвь получает связывания конструктора после параметров
//! семейства - столько же и в том же порядке, включая стёртые.
//!
//! # Откуда берётся представление (§4.11)
//!
//! Плоское значение заголовка не имеет вовсе (§13, 2026-09-08), поэтому
//! [`Repr`] обязан быть известен **до** эмиссии: от него зависят C-тип
//! связывания, наличие RC-трафика и то, чем считает слот дроп с печатью.
//!
//! Читается он там, где тип **написан**: домен `Pi` даёт представление
//! параметра и поля конструктора, аннотация `let` - своего связывания, а
//! литерал и операция несут тип в себе. Дальше представление **синтезируется**
//! снизу вверх - каждое выражение отдаёт своё вместе с собой, - и в объявленных
//! позициях сверяется. Расхождение отвергается
//! ([`LowerError::Representation`]), а не приводится молча: биты числа,
//! принятые за указатель, суть чтение по адресу этого числа.
//!
//! Написан тип не везде: у связывания лямбды его нет в ядре вовсе. Поэтому
//! связывание лямбды объявляется указательным, а плоское значение,
//! пришедшее в такую позицию, отвергается.
//!
//! **Дескриптор эту границу не снял, и это измерено.** План фазы ждал
//! обратного: дескриптор даёт **шаг**, а замыканию нужен единообразный
//! **слот**, и второе есть боксирование (§5.1, «боксирование при передаче
//! значения в позицию, скомпилированную по указательному представлению»), а
//! не индексация. Свидетель прежний и по-прежнему красный на попытке -
//! `tests/flat.rs`, `a_flat_value_does_not_cross_a_closure`.
//!
//! # Массив: представление одно на два случая (§4.11)
//!
//! `Array n a` есть один объект кучи независимо от элемента; раздваивается
//! **укладка ячеек**. При плоском элементе они лежат подряд по `stride` байт,
//! иначе - слотами указателей ([`Elems`]). Шаг читается не у массива, а у
//! **написанного типа элемента**, и приходит он двумя путями, которые §4.11
//! называет обоими:
//!
//! - элемент - примитив, и шаг известен типом ([`Stride::Static`]);
//! - элемент - переменная, о которой в телескопе функции есть словарь `Flat`,
//!   и шаг приходит его полем ([`Stride::Dynamic`]).
//!
//! Второе и есть «функция с `{Flat a}` в контексте получает дескриптор обычным
//! имплиситом». Мономорфизация (`adamas_elab::mono`) переводит второй путь в
//! первый, и оба обязаны давать один ответ - свидетель `tests/array.rs`.
//!
//! Функция **без** `{Flat a}` компилируется по указательному представлению, как
//! §4.11 и говорит, поэтому плоский массив в неё не проходит: это была бы
//! передача в позицию другого представления, то есть снова боксирование.
//!
//! # Арность берётся у типа, а не у тела (§10 вопрос 153)
//!
//! Определение приходит **свёрнутым по эте** от трёх источников сразу, и это
//! измерено, а не предположено. Мономорфизация: `add@_,Add#Int64` имеет тип
//! `Int64 -> Int64 -> Int64` и тело `Const("Add#Int64.add")`. Написанное от
//! руки целиком: `again = plus`. Написанное от руки частично: у `half x = plus
//! x` лямбда одна, а стрелок две. Бери арность у тела - и в первых двух случаях
//! её ноль, в третьем единица, а недоданные аргументы уходят применением к
//! значению, то есть через границу замыкания, где плоскому места нет.
//!
//! Поэтому параметров у функции столько, сколько **стрелок у типа**;
//! недостающие связывания достраиваются здесь и дописываются к спайну тела.
//! Терм при этом не переписывается: снятые лямбды остаются в среде де Брёйна
//! на своих местах, а достроенные в неё не попадают вовсе - тело на них
//! сослаться не может по построению. Отсюда и нет сдвигов.
//!
//! Тело, спайном не являющееся (`case`, `let`, лямбда под `0`-связыванием),
//! дописать некуда: достроенные параметры применяются к его значению обычным
//! путём, и плоское там по-прежнему отвергается.
//!
//! # Чего понижение не делает
//!
//! Не бета-редуцирует, не инлайнит, не кеширует значение определения без
//! параметров: оптимизаций на этом срезе нет вовсе, и предсказуемость выхода
//! дороже его длины.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use adamas_core::eval::{eval, quote};
use adamas_core::mult::Mult;
use adamas_core::prim::{ArrayOp, Prim, PrimTy};
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::term::{Case, Index, Name, Term};
use adamas_core::value::{Env, Lvl, Value};

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Elems, Expr, Fact, Form, FuncId, Function, LocalId, PackId,
    Packing, Program, Repr, Slot as PackSlot, Stride,
};

/// Почему понижение отказало.
#[derive(Debug, thiserror::Error)]
pub enum LowerError {
    /// Имя, которого нет в сигнатуре.
    #[error("имя `{name}` не объявлено")]
    Unknown {
        /// Оно самое.
        name: String,
    },

    /// Постулат: тип есть, тела нет, понижать нечего.
    #[error("`{name}` - постулат: тела нет, и понижать нечего")]
    Postulate {
        /// Имя постулата.
        name: String,
    },

    /// Метка, операция либо элиминатор хендлера.
    #[error("`{name}` - эффект: вторая форма понижения этим срезом не берётся")]
    Effectful {
        /// Имя метки или операции.
        name: String,
    },

    /// Семейство в позиции значения.
    #[error("`{name}` - семейство типов: значения у него в рантайме нет")]
    TypeValue {
        /// Имя семейства.
        name: String,
    },

    /// Форма терма, которой чистый фрагмент не знает.
    #[error("{form} этим срезом не берётся")]
    Unsupported {
        /// Что именно встретилось.
        form: &'static str,
    },

    /// Ответ программы - функция.
    #[error("ответ программы - функция: печатать её нечем")]
    FunctionAnswer,

    /// Конструкторов больше, чем тегов: верх диапазона занят рантаймом.
    #[error("конструкторов больше {limit}: верх диапазона тегов занят рантаймом")]
    TooManyConstructors {
        /// Сколько их помещается.
        limit: u16,
    },

    /// Переменная за пределами захваченной среды - дефект анализа свободных.
    #[error("переменная #{index} вне захваченной среды")]
    Unbound {
        /// Индекс де Брёйна.
        index: u32,
    },

    /// Живому связыванию не досталось аргумента.
    #[error("`{name}`: живому связыванию #{binder} не досталось аргумента")]
    Missing {
        /// Кому.
        name: String,
        /// Какому связыванию.
        binder: usize,
    },

    /// Представление значения разошлось с представлением позиции (§4.11).
    ///
    /// Отказ, а не приведение: заголовка у плоского значения нет вовсе, и
    /// положить его туда, где ждут указатель, значит отдать биты числа
    /// счётчику ссылок.
    #[error("{at}: ожидалось {want}, а пришло {got} (§4.11)")]
    Representation {
        /// В какой позиции.
        at: &'static str,
        /// Что там объявлено.
        want: String,
        /// Что туда пришло.
        got: String,
    },

    /// Примитивная операция без обоих аргументов.
    ///
    /// Значением она была бы замыканием, а замыкание принимает аргументы
    /// указательными: плоскому нужен дескриптор layout (§4.11), и это
    /// следующая половина трека.
    #[error("`{name}` без обоих аргументов: примитив значением требует дескриптора layout (§4.11)")]
    Partial {
        /// Имя операции.
        name: String,
    },

    /// Операция над массивом без всех аргументов.
    ///
    /// Недобранной она была бы замыканием, а через замыкание не проходит ни
    /// плоский элемент, ни дескриптор (§4.11).
    #[error("`{name}` без всех аргументов: операция над массивом значением этим срезом не берётся")]
    PartialArray {
        /// Имя операции.
        name: String,
    },

    /// Ответ программы - массив.
    ///
    /// Печатать его нечем, и это названная граница: `adamas eval` печатает
    /// цепочку `arrayNew`/`arraySet` со стёртыми аргументами, понижение -
    /// значение, и сводить эти две печати - работа не этого среза.
    #[error("ответ программы - массив: печатать его нечем (§4.11)")]
    ArrayAnswer,

    /// Ответ программы - плоский агрегат.
    ///
    /// Печать идёт по тегу заголовка, а у плоского агрегата заголовка нет
    /// вовсе (§4.11): в ответе лежат байты. Названная граница того же жанра,
    /// что массив в ответе.
    #[error("ответ программы - плоский агрегат: заголовка у него нет, печатать нечем (§4.11)")]
    PackedAnswer,

    /// Дескриптор укладки написан не той записью.
    #[error("дескриптор укладки ожидался записью `{{ layout = {{ size, align }} }}` (§4.11)")]
    Descriptor,

    /// Проекция из значения, чьей формы понижение не знает.
    ///
    /// Имени поля в рантайме нет - слот раздаёт форма записи (§4.2), - поэтому
    /// проекция без формы неисполнима. Формы нет там, где представление
    /// расширилось до указательного: поле полиморфного конструктора, связывание
    /// лямбды, ответ применения.
    #[error("`.{label}`: форма записи потеряна, слот брать неоткуда (§4.2)")]
    Shapeless {
        /// Какое поле берут.
        label: String,
    },

    /// Проекция поля, которого в форме записи нет.
    #[error("`.{label}`: поля нет в форме `{shape}` (§4.2)")]
    NoField {
        /// Какое поле берут.
        label: String,
        /// Из чего берут.
        shape: String,
    },
}

/// Требует, чтобы все живые связывания жили указателем.
fn pointing(facts: &[Fact], at: &'static str) -> Result<(), LowerError> {
    for fact in facts {
        if fact.present && !fact.repr.pointer() {
            return Err(LowerError::Representation {
                at,
                want: describe(Repr::Boxed),
                got: describe(fact.repr),
            });
        }
    }
    Ok(())
}

/// Годится ли пришедшее представление в объявленную позицию.
///
/// Совпадение - обычный случай. Послаблений два, и оба про **запись**: у неё
/// тот же C-тип, тот же заголовок и тот же счётчик, что у указателя, и
/// различает их одно - помнит ли понижение форму.
///
/// *Расширение* - запись в позицию указателя. Форма теряется, и проекция после
/// потери отвергается по имени ([`LowerError::Shapeless`]). Без него запись не
/// легла бы в поле полиморфного конструктора (`Cons { size = 4, align = 4 }
/// Nil`), а §4.11 пишет ровно такое.
///
/// *Сужение* - указатель в позицию записи. Здесь верят **объявлению**: форму
/// назвал написанный тип позиции, а значение потеряло её по дороге - в
/// связывании лямбды, у которого типа в ядре нет вовсе. Верить объявлению
/// безопасно не по построению, а потому, что промах виден: проекция понижается
/// разбором, и тег объекта сверяется в рантайме - форма не та, и прогон
/// обрывается на `default`, а не читает чужой слот.
fn fits(got: Repr, want: Repr) -> bool {
    got == want
        || (want.boxed() && got.pointer())
        || matches!((got, want), (Repr::Boxed, Repr::Record(_)))
}

/// Как представление называется в отказе.
fn describe(repr: Repr) -> String {
    match repr {
        Repr::Boxed => "указательное значение".to_owned(),
        Repr::Flat(ty) => format!("плоское `{ty}`"),
        Repr::Layout => "дескриптор укладки".to_owned(),
        Repr::Opaque => "плоский элемент неизвестного типа".to_owned(),
        Repr::Array(Elems::Flat) => "плоский массив".to_owned(),
        Repr::Array(Elems::Boxed) => "указательный массив".to_owned(),
        Repr::Record(tag) => format!("запись формы #{}", tag.0),
        Repr::Packed(pack) => format!("плоский агрегат укладки #{}", pack.0),
    }
}

/// Имя класса представления (§4.11).
///
/// Объявляет его программа - соглашение то же, каким `if` берёт `Bool`, - и
/// понижение читает его по имени ровно там же, где элаборация
/// (`adamas-elab/src/flat.rs`). Второго имени тут не заводится: словарь,
/// пришедший имплиситом, и есть дескриптор.
const FLAT: &str = "Flat";

/// Имя единственного метода `Flat` и полей его укладки (§4.11).
///
/// Читаются они по имени там же, где [`descriptor`] собирает дескриптор:
/// форма словаря записана в §4.11 дословно, и второго источника у неё нет.
const METHOD: &str = "layout";
/// Поле размера в укладке.
const SIZE: &str = "size";
/// Поле выравнивания в укладке.
const ALIGN: &str = "align";

/// Где лежат дескрипторы укладки: уровень описанного связывания - словарь.
///
/// Ключ - **уровень** типового связывания, о котором словарь говорит.
/// Значение - номер того связывания, в котором словарь лежит. Так и читается
/// §4.11 «функция с `{Flat a}` в контексте получает дескриптор обычным
/// имплиситом»: контекст - это телескоп, и найти в нём словарь по типу
/// элемента можно только сравнив, о каком связывании он говорит.
type Dicts = HashMap<u32, LocalId>;

/// Верх диапазона тегов занят служебными объектами рантайма (`adamas.h`).
const TAGS: u16 = 0xFFF0;

/// Понижает терм в программу.
///
/// `entry` - тело `main` с подставленными аргументами уровня и row, то есть
/// ровно то, что вычисляет `adamas eval`.
///
/// # Errors
///
/// [`LowerError`] - форма вне чистого фрагмента либо имя, которого не понизить.
pub fn lower(signature: &Signature, entry: &Term) -> Result<Program, LowerError> {
    Lowerer::new(signature).program(entry)
}

/// Аргумент спайна.
///
/// Написанных здесь большинство; достроенные приходят от эта-развёртки (§10
/// вопрос 153) - параметр объявлен типом, а в терме его нет.
enum Arg<'a> {
    /// Написан в терме.
    Written(&'a Term),
    /// Достроен по типу определения: связывания в терме нет.
    Supplied(&'a Binding),
}

/// Где лежит связывание, видимое телу.
#[derive(Clone, Debug)]
enum Slot {
    /// Связано: номер и факты.
    Bound(LocalId, Fact),
    /// Не захвачено этой функцией: ссылаться на него неоткуда.
    Absent,
}

/// Локальное состояние одной понижаемой функции.
#[derive(Debug, Default)]
struct Scope {
    /// Сколько локальных номеров уже выдано.
    locals: u32,
    /// Связывания в порядке связывания: последнее - индекс 0.
    env: Vec<Slot>,
    /// Дескрипторы укладки, пришедшие имплиситами этой функции (§4.11).
    dicts: Dicts,
}

impl Scope {
    /// Свежий номер.
    fn fresh(&mut self) -> LocalId {
        let id = LocalId(self.locals);
        self.locals += 1;
        id
    }

    /// Связывание по индексу де Брёйна.
    fn slot(&self, Index(index): Index) -> Result<&Slot, LowerError> {
        let from_top = usize::try_from(index).unwrap_or(usize::MAX);
        self.env
            .len()
            .checked_sub(from_top + 1)
            .and_then(|position| self.env.get(position))
            .ok_or(LowerError::Unbound { index })
    }
}

/// Понижение: сигнатура на входе, программа на выходе.
struct Lowerer<'a> {
    signature: &'a Signature,
    constructors: Vec<Constructor>,
    packings: Vec<Packing>,
    tags: HashMap<Name, CtorId>,
    functions: Vec<Function>,
    numbers: HashMap<Name, FuncId>,
    /// Определения, чьи тела ещё не понижены.
    pending: VecDeque<(FuncId, Name)>,
}

impl<'a> Lowerer<'a> {
    fn new(signature: &'a Signature) -> Self {
        Self {
            signature,
            constructors: Vec::new(),
            packings: Vec::new(),
            tags: HashMap::new(),
            functions: Vec::new(),
            numbers: HashMap::new(),
            pending: VecDeque::new(),
        }
    }

    /// Понижает точку входа и всё, до чего она дотягивается.
    fn program(mut self, entry: &Term) -> Result<Program, LowerError> {
        if matches!(entry, Term::Lam(..)) {
            return Err(LowerError::FunctionAnswer);
        }
        let entry_id = FuncId(0);
        self.functions.push(Function {
            id: entry_id,
            name: "main".to_owned(),
            form: form(),
            captured: Vec::new(),
            parameters: Vec::new(),
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let mut scope = Scope::default();
        let (mut body, mut repr) = self.expr(&mut scope, entry)?;
        // У точки входа объявленного типа нет - она уже инстанцирована, - и
        // представление ответа берётся у самого ответа.
        if matches!(repr, Repr::Array(_)) {
            return Err(LowerError::ArrayAnswer);
        }
        // Плотный агрегат печатается упакованным: печать идёт по тегу
        // заголовка, а у плотного заголовка нет вовсе (§4.11). Упаковка тут не
        // выбор представления, а цена печати, и она одна на весь ответ.
        if let Repr::Packed(pack) = repr {
            let tag = self.boxed_shape(pack)?;
            body = self.boxing(&mut scope, body, pack, tag);
            repr = Repr::Record(tag);
        }
        self.functions[entry_id.0].body = body;
        self.functions[entry_id.0].result = repr;

        // Очередь, а не рекурсия: имя получает номер до того, как понижено его
        // тело, поэтому рекурсия и взаимная рекурсия проходят сами собой.
        while let Some((id, name)) = self.pending.pop_front() {
            let (parameters, inner, taken, dicts) = self.peeled(&name)?;
            let mut scope = Scope {
                // Номера выданы всем параметрам, включая достроенные, а в среду
                // де Брёйна попадают только снятые: на достроенные тело
                // сослаться не может, их в нём нет.
                locals: u32::try_from(parameters.len()).unwrap_or(u32::MAX),
                env: Vec::with_capacity(taken),
                dicts,
            };
            for parameter in &parameters[..taken] {
                scope.env.push(Slot::Bound(parameter.local, parameter.fact));
            }
            let declared = self.functions[id.0].result;
            let (body, repr) =
                self.saturated(&mut scope, &inner, &parameters[taken..], declared)?;
            if !fits(repr, declared) {
                return Err(LowerError::Representation {
                    at: "ответ функции",
                    want: describe(declared),
                    got: describe(repr),
                });
            }
            self.functions[id.0].body = body;
        }

        Ok(Program {
            constructors: self.constructors,
            packings: self.packings,
            functions: self.functions,
            entry: entry_id,
        })
    }

    /// Определение по имени.
    fn definition(&self, name: &Name) -> Result<&'a adamas_core::sig::Definition, LowerError> {
        self.signature
            .lookup(name)
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Параметры определения, тело под снятыми лямбдами и сколько их снято.
    ///
    /// Параметров столько, сколько **стрелок у типа** (§10 вопрос 153): тело
    /// приходит свёрнутым по эте от трёх источников, и арность по нему выходит
    /// меньше объявленной. Снять из них удаётся столько, сколько у тела ведущих
    /// лямбд, - это и есть `taken`; остальные достраиваются здесь, и в среду
    /// де Брёйна они не идут.
    ///
    /// Кратность и представление каждого берутся из **типа**, а не из лямбды -
    /// тем же правилом, каким машина решает, стирать ли аргумент. Лямбд бывает
    /// и больше, чем стрелок (тип за синонимом): лишние остаются
    /// указательными при `ω`, как и прежде.
    fn peeled(
        &mut self,
        name: &Name,
    ) -> Result<(Vec<Binding>, Rc<Term>, usize, Dicts), LowerError> {
        let definition = self.definition(name)?;
        let body = definition.body.as_ref().ok_or_else(|| {
            // Невыразимое имя без тела заводит элаборация эффектов: `#handle.L`,
            // `#handleMulti.L`, `#mask`, `#closing`. Звать их постулатами
            // формально верно и по существу неверно - автор постулата не писал,
            // а написал `handle`.
            if name.starts_with('#') {
                LowerError::Effectful {
                    name: name.to_string(),
                }
            } else {
                LowerError::Postulate {
                    name: name.to_string(),
                }
            }
        })?;
        // Словари телескопа считаются **до** параметров: представление массива
        // зависит от того, есть ли в контексте `Flat` на его элемент (§4.11).
        let dicts = dicts_of(self.signature, &definition.ty);
        let mut parameters = Vec::new();
        let mut current = Rc::new(body.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(_, bound, inner) = &*step else {
                break;
            };
            let (mult, repr) = self
                .binder_at(&definition.ty, parameters.len(), &dicts)?
                .unwrap_or((Mult::Many, Repr::Boxed));
            parameters.push(Binding {
                name: bound.to_string(),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult).shaped(repr),
            });
            current = Rc::clone(inner);
        }
        let taken = parameters.len();
        while let Some((mult, repr)) = self.binder_at(&definition.ty, parameters.len(), &dicts)? {
            parameters.push(Binding {
                name: format!("эта{}", parameters.len() - taken),
                local: LocalId(u32::try_from(parameters.len()).unwrap_or(u32::MAX)),
                fact: Fact::declared(mult).shaped(repr),
            });
        }
        Ok((parameters, current, taken, dicts))
    }

    /// Номер функции определения; тело откладывается в очередь.
    fn function(&mut self, name: &Name) -> Result<FuncId, LowerError> {
        if let Some(id) = self.numbers.get(name) {
            return Ok(*id);
        }
        let (parameters, _, _, dicts) = self.peeled(name)?;
        let ty = &self.definition(name)?.ty;
        let result = self.result_repr(ty, parameters.len(), &dicts)?;
        let id = FuncId(self.functions.len());
        self.functions.push(Function {
            id,
            name: name.to_string(),
            form: form(),
            captured: Vec::new(),
            parameters,
            result,
            body: Expr::Erased,
        });
        self.numbers.insert(Rc::clone(name), id);
        self.pending.push_back((id, Rc::clone(name)));
        Ok(id)
    }

    /// Заводит теги всем конструкторам семейства разом.
    ///
    /// Разом потому, что разбор требует тега у каждой ветви, а не только у
    /// встреченных конструкторов.
    fn family(&mut self, data: &Name) -> Result<(), LowerError> {
        let definition = self.definition(data)?;
        let DefinitionKind::Data {
            constructors,
            params,
            ..
        } = &definition.kind
        else {
            return Err(LowerError::TypeValue {
                name: data.to_string(),
            });
        };
        for name in constructors {
            if self.tags.contains_key(name) {
                continue;
            }
            // Тег берётся **после** телескопа: поле-запись заводит свою форму,
            // и форма эта живёт в той же таблице. Возьми номер раньше - два
            // конструктора получили бы один тег.
            let ty = &self.definition(name)?.ty;
            let binders = self.binders_of(ty)?;
            let tag = u16::try_from(self.constructors.len())
                .ok()
                .filter(|tag| *tag < TAGS)
                .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
            self.constructors.push(Constructor {
                tag: CtorId(tag),
                name: name.to_string(),
                data: data.to_string(),
                binders,
                params: *params,
                labels: None,
            });
            self.tags.insert(Rc::clone(name), CtorId(tag));
        }
        Ok(())
    }

    /// Тег конструктора: семейство заводится целиком по дороге.
    fn tag(&mut self, name: &Name) -> Result<CtorId, LowerError> {
        if let Some(tag) = self.tags.get(name) {
            return Ok(*tag);
        }
        let DefinitionKind::Constructor { data } = &self.definition(name)?.kind else {
            return Err(LowerError::Unknown {
                name: name.to_string(),
            });
        };
        self.family(data)?;
        self.tags
            .get(name)
            .copied()
            .ok_or_else(|| LowerError::Unknown {
                name: name.to_string(),
            })
    }

    /// Понижает выражение и отдаёт его представление (§4.11).
    ///
    /// Представление синтезируется, а не проверяется: у каждого узла оно своё,
    /// и в объявленных позициях сверяется [`Lowerer::shaped`].
    fn expr(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        match term {
            Term::Var(index) => match scope.slot(*index)? {
                Slot::Bound(local, fact) if fact.present => Ok((Expr::Local(*local), fact.repr)),
                Slot::Bound(..) => Ok((Expr::Erased, Repr::Boxed)),
                Slot::Absent => Err(LowerError::Unbound { index: index.0 }),
            },
            Term::Lam(..) => self.closure(scope, term),
            Term::App(..) | Term::Const(..) | Term::Prim(_) => {
                let (head, written) = spine(term);
                let arguments: Vec<Arg<'_>> = written.into_iter().map(Arg::Written).collect();
                self.application(scope, head, &arguments)
            }
            Term::Let(mult, name, ty, value, body) => {
                let depth = u32::try_from(scope.env.len()).unwrap_or(u32::MAX);
                let dicts = scope.dicts.clone();
                let declared = self.repr_of(ty, depth, &dicts)?;
                let value = self.shaped(scope, value, declared, "связанное значение")?;
                let binding = Binding {
                    name: name.to_string(),
                    local: scope.fresh(),
                    // Машина считает связанное значение, не спрашивая кратности:
                    // `let 0 x = …` вычисляется наравне с прочими.
                    fact: Fact::present(*mult).shaped(declared),
                };
                scope.env.push(Slot::Bound(binding.local, binding.fact));
                let body = self.expr(scope, body);
                scope.env.pop();
                let (body, repr) = body?;
                Ok((
                    Expr::Bind {
                        binding,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    repr,
                ))
            }
            Term::Case(case) => self.analysis(scope, case),
            // Словарь `Flat` - исключение из общего пути записей: форма его
            // записана в §4.11, а живёт он дескриптором, а не объектом кучи.
            Term::Object(fields) => match descriptor(fields) {
                Some((size, align)) => Ok((Expr::Layout { size, align }, Repr::Layout)),
                None => self.object(scope, fields),
            },
            Term::Project(record, label) => self.projection(scope, record, label),
            // Переопределение доживает до ядра только у **открытой** записи:
            // закрытую элаборация пересобирает полями (§4.2). Форма открытой
            // не перечислима - её знает хвост, - и слотов у неё поэтому нет.
            Term::With(..) => Err(LowerError::Unsupported {
                form: "переопределение открытой записи",
            }),
            Term::Record(_)
            | Term::Pi(..)
            | Term::Universe(_)
            | Term::RowKind(_)
            | Term::EffectKind
            | Term::Row(_) => Err(LowerError::Unsupported {
                form: "тип в позиции значения",
            }),
            Term::Meta(_) => Err(LowerError::Unsupported {
                form: "неразрешённая дырка",
            }),
        }
    }

    /// Понижает подвыражение и требует от него объявленного представления.
    fn shaped(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        want: Repr,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        let (value, got) = self.expected(scope, term, want)?;
        if fits(got, want) {
            return Ok(value);
        }
        if let Some(moved) = self.moved(scope, &value, got, want)? {
            return Ok(moved);
        }
        Err(LowerError::Representation {
            at,
            want: describe(want),
            got: describe(got),
        })
    }

    /// Перекладывает значение между плотной укладкой и объектом кучи (§4.11).
    ///
    /// Два перехода, и оба стоят копии полей, а не приведения. **Упаковка** -
    /// плотный агрегат туда, где ждут указатель: объект кучи с заголовком,
    /// слот на поле. **Распаковка** - обратно: слоты читаются, байты ложатся
    /// подряд. `None` - перехода нет, и отвечать будет сверка представлений.
    ///
    /// Нужны они потому, что плоское и указательное встречаются в одной
    /// программе по построению: `Array n Vec3` требует плотного элемента
    /// (§4.11), а `Cons` и печать ответа говорят указателями. Цена названа и
    /// она поэлементная; убрать её - работа специализации, а не понижения.
    fn moved(
        &mut self,
        scope: &mut Scope,
        value: &Expr,
        got: Repr,
        want: Repr,
    ) -> Result<Option<Expr>, LowerError> {
        match (got, want) {
            (Repr::Packed(pack), Repr::Boxed | Repr::Record(_)) => {
                let tag = self.boxed_shape(pack)?;
                if !fits(Repr::Record(tag), want) {
                    return Ok(None);
                }
                Ok(Some(self.boxing(scope, value.clone(), pack, tag)))
            }
            (Repr::Record(tag), Repr::Packed(pack)) => {
                Ok(self.tightening(scope, value.clone(), tag, pack))
            }
            _ => Ok(None),
        }
    }

    /// Форма объекта кучи, отвечающая плотной укладке.
    fn boxed_shape(&mut self, pack: PackId) -> Result<CtorId, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        let facts: Vec<Fact> = packing
            .slots
            .iter()
            .map(|slot| Fact::declared(Mult::One).shaped(Repr::Flat(slot.ty)))
            .collect();
        self.shape(&packing.labels, &facts)
    }

    /// Плотный агрегат объектом кучи: поля читаются смещением, кладутся слотом.
    fn boxing(&mut self, scope: &mut Scope, value: Expr, pack: PackId, tag: CtorId) -> Expr {
        let count = self.packings[pack.0 as usize].slots.len();
        let binding = Binding {
            name: "агрегат".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::Many).shaped(Repr::Packed(pack)),
        };
        let local = binding.local;
        let fields = (0..count)
            .map(|at| Expr::Unpack {
                packing: pack,
                field: u32::try_from(at).unwrap_or(u32::MAX),
                value: Box::new(Expr::Local(local)),
            })
            .collect();
        Expr::Bind {
            binding,
            value: Box::new(value),
            body: Box::new(Expr::Construct {
                constructor: tag,
                reuse: None,
                arguments: fields,
            }),
        }
    }

    /// Объект кучи плотным агрегатом: разбор в одну ветвь, поля - в байты.
    ///
    /// Разбором, а не отдельным узлом, по той же причине, что и проекция:
    /// договор о владении у разбора уже есть, и разобранный объект отдаётся им.
    /// `None` - формы не сходятся полями, и отвечать будет сверка.
    fn tightening(
        &mut self,
        scope: &mut Scope,
        value: Expr,
        tag: CtorId,
        pack: PackId,
    ) -> Option<Expr> {
        let described = self.constructors[usize::from(tag.0)].clone();
        let packing = self.packings[pack.0 as usize].clone();
        if described.labels.as_deref() != Some(&packing.labels) {
            return None;
        }
        let matching = described
            .binders
            .iter()
            .zip(&packing.slots)
            .all(|(fact, slot)| fact.present && fact.repr == Repr::Flat(slot.ty));
        if !matching || described.binders.len() != packing.slots.len() {
            return None;
        }
        let fields: Vec<Binding> = packing
            .labels
            .iter()
            .zip(&described.binders)
            .map(|(label, fact)| Binding {
                name: label.clone(),
                local: scope.fresh(),
                fact: *fact,
            })
            .collect();
        let taken = fields.iter().map(|it| Expr::Local(it.local)).collect();
        Some(Expr::Match {
            scrutinee: Box::new(value),
            consumed: Mult::One,
            arms: vec![Arm {
                constructor: tag,
                fields,
                body: Expr::Pack {
                    packing: pack,
                    fields: taken,
                },
            }],
        })
    }

    /// Понижает выражение, зная, какого представления от него ждут.
    ///
    /// Ожидание читает ровно одна форма - значение записи, - и читает по делу:
    /// синтезом форма собирается из **значений** полей, а значения не всё
    /// знают. Стёртое поле там неотличимо от живого (`type T = Nat` в теле
    /// модуля - тип в позиции значения), а поле, потерявшее форму по дороге,
    /// дало бы форму, не равную объявленной. Объявление знает и то, и другое.
    fn expected(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        want: Repr,
    ) -> Result<(Expr, Repr), LowerError> {
        if let Term::Object(fields) = term {
            if descriptor(fields).is_none() {
                match want {
                    Repr::Record(tag) => return Ok((self.object_as(scope, fields, tag)?, want)),
                    Repr::Packed(pack) => return Ok((self.pack_as(scope, fields, pack)?, want)),
                    _ => {}
                }
            }
        }
        self.expr(scope, term)
    }

    /// Значение записи: объект кучи со слотом на поле (§4.2).
    ///
    /// Форма берётся у **написанного** - метки и представления полей идут в том
    /// порядке, в каком они написаны, - и она же порядок печати. Форма из
    /// **типа** (параметр, аннотация, ответ) читается телескопом, и это тот же
    /// порядок ровно потому, что элаборация пересобирает обновление по
    /// телескопу (§4.2). Разойдись они - сверка представлений отвергает по
    /// имени, а не считает не то.
    fn object(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
    ) -> Result<(Expr, Repr), LowerError> {
        let mut labels = Vec::with_capacity(fields.len());
        let mut facts = Vec::with_capacity(fields.len());
        let mut values = Vec::with_capacity(fields.len());
        for (label, value) in fields {
            let (value, repr) = self.expr(scope, value)?;
            labels.push(label.to_string());
            // Поле записи кладёт значение однажды - `check::infer_object`
            // объявляет его `1`, и другого источника кратности у значения нет.
            facts.push(Fact::declared(Mult::One).shaped(repr));
            values.push(value);
        }
        let tag = self.shape(&labels, &facts)?;
        Ok((
            Expr::Construct {
                constructor: tag,
                reuse: None,
                arguments: values,
            },
            Repr::Record(tag),
        ))
    }

    /// Значение записи, собранное по **объявленной** форме.
    ///
    /// Метки сверяются с формой позиция в позицию, а не по имени: слоты
    /// раздаёт форма, а печать идёт в порядке слотов, и `adamas eval` печатает
    /// поля как написаны (§4.2). Совпади множества, но разойдись порядок - две
    /// печати разошлись бы тоже, поэтому здесь отказ, а не перестановка.
    fn object_as(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
        tag: CtorId,
    ) -> Result<Expr, LowerError> {
        let described = self.constructors[usize::from(tag.0)].clone();
        let labels = described.labels.clone().unwrap_or_default();
        let mismatch = || LowerError::Representation {
            at: "поля записи",
            want: described.name.clone(),
            got: format!(
                "{{{}}}",
                fields
                    .iter()
                    .map(|(label, _)| label.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        if labels.len() != fields.len() {
            return Err(mismatch());
        }
        let mut arguments = Vec::with_capacity(fields.len());
        for (position, (label, value)) in fields.iter().enumerate() {
            if **label != *labels[position] {
                return Err(mismatch());
            }
            let fact = described.binders[position];
            if !fact.present {
                arguments.push(Expr::Erased);
                continue;
            }
            arguments.push(self.shaped(scope, value, fact.repr, "поле записи")?);
        }
        Ok(Expr::Construct {
            constructor: tag,
            reuse: None,
            arguments,
        })
    }

    /// Значение записи, уложенное **плоско** (§4.11).
    ///
    /// Отличается от [`Lowerer::object_as`] тем, куда ложатся поля: там слот
    /// объекта кучи, здесь смещение внутри байтов. Метки сверяются так же -
    /// позиция в позицию.
    fn pack_as(
        &mut self,
        scope: &mut Scope,
        fields: &[(Name, Rc<Term>)],
        pack: PackId,
    ) -> Result<Expr, LowerError> {
        let packing = self.packings[pack.0 as usize].clone();
        let mismatch = || LowerError::Representation {
            at: "поля плоской записи",
            want: format!("{{{}}}", packing.labels.join(", ")),
            got: format!(
                "{{{}}}",
                fields
                    .iter()
                    .map(|(label, _)| label.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        if packing.labels.len() != fields.len() {
            return Err(mismatch());
        }
        let mut given = Vec::with_capacity(fields.len());
        for (position, (label, value)) in fields.iter().enumerate() {
            if **label != *packing.labels[position] {
                return Err(mismatch());
            }
            let want = Repr::Flat(packing.slots[position].ty);
            given.push(self.shaped(scope, value, want, "поле плоской записи")?);
        }
        Ok(Expr::Pack {
            packing: pack,
            fields: given,
        })
    }

    /// Проекция поля: чтение слота, найденного формой записи.
    ///
    /// Понижается **разбором в одну ветвь**, а не отдельным узлом, и это не
    /// экономия узлов: у разбора уже есть договор о владении - разобранное
    /// отдаётся, названное поле приходит `dup`'ом (`perceus::arm`), - и второй
    /// узел потребовал бы второй его копии.
    fn projection(
        &mut self,
        scope: &mut Scope,
        record: &Term,
        label: &Name,
    ) -> Result<(Expr, Repr), LowerError> {
        let (value, repr) = self.expr(scope, record)?;
        if repr == Repr::Layout && &**label == METHOD {
            return Ok(self.materialised(scope, value));
        }
        if let Repr::Packed(pack) = repr {
            // Плоский агрегат: поле адресуется **смещением**, а не слотом, - и
            // это названная цена варианта (а) вопроса 154.
            let packing = &self.packings[pack.0 as usize];
            let at = packing
                .labels
                .iter()
                .position(|it| **it == **label)
                .ok_or_else(|| LowerError::NoField {
                    label: label.to_string(),
                    shape: format!("{{{}}}", packing.labels.join(", ")),
                })?;
            let ty = packing.slots[at].ty;
            return Ok((
                Expr::Unpack {
                    packing: pack,
                    field: u32::try_from(at).unwrap_or(u32::MAX),
                    value: Box::new(value),
                },
                Repr::Flat(ty),
            ));
        }
        let Repr::Record(tag) = repr else {
            return Err(LowerError::Shapeless {
                label: label.to_string(),
            });
        };
        let described = self.constructors[usize::from(tag.0)].clone();
        let at = described
            .labels
            .as_ref()
            .and_then(|labels| labels.iter().position(|it| **it == **label))
            .ok_or_else(|| LowerError::NoField {
                label: label.to_string(),
                shape: described.name.clone(),
            })?;
        let fields: Vec<Binding> = described
            .binders
            .iter()
            .enumerate()
            .map(|(position, fact)| Binding {
                name: described.labels.as_ref().map_or_else(
                    || format!("поле{position}"),
                    |labels| labels[position].clone(),
                ),
                local: scope.fresh(),
                fact: *fact,
            })
            .collect();
        let taken = fields[at].fact;
        let body = if taken.present {
            Expr::Local(fields[at].local)
        } else {
            Expr::Erased
        };
        Ok((
            Expr::Match {
                scrutinee: Box::new(value),
                // Запись потребляется проекцией целиком: прочие поля отдаёт
                // дроп разобранного.
                consumed: Mult::One,
                arms: vec![Arm {
                    constructor: tag,
                    fields,
                    body,
                }],
            },
            taken.repr,
        ))
    }

    /// Единственный метод `Flat` записью: `dict.layout` есть `{ size, align }`.
    ///
    /// Словарь `Flat` живёт дескриптором, а не объектом кучи ([`Repr::Layout`]),
    /// поэтому проекция его метода - не чтение слота, а **сборка** записи из
    /// двух чисел. Порядок полей тот же, что требует [`descriptor`]: сперва
    /// размер, потом выравнивание. Напиши программа `Layout` в другом порядке -
    /// формы разойдутся, и сверка представлений скажет об этом по имени.
    fn materialised(&mut self, scope: &mut Scope, descriptor: Expr) -> (Expr, Repr) {
        let labels = [SIZE.to_owned(), ALIGN.to_owned()];
        let pack = self.packing(&labels, &[PrimTy::UInt32, PrimTy::UInt32]);
        // Дескриптор связывается: полей у него два, а посчитан он однажды.
        let binding = Binding {
            name: "дескриптор".to_owned(),
            local: scope.fresh(),
            fact: Fact::present(Mult::Many).shaped(Repr::Layout),
        };
        let local = binding.local;
        (
            Expr::Bind {
                binding,
                value: Box::new(descriptor),
                body: Box::new(Expr::Pack {
                    packing: pack,
                    fields: vec![
                        Expr::LayoutField {
                            descriptor: local,
                            align: false,
                        },
                        Expr::LayoutField {
                            descriptor: local,
                            align: true,
                        },
                    ],
                }),
            },
            Repr::Packed(pack),
        )
    }

    /// Форма записи по меткам и представлениям полей; заводится однажды.
    ///
    /// Сравниваются метки **и** факты: `{ x : Int64 }` и `{ x : Nat }` - разные
    /// формы, потому что слот у первого несёт биты, а у второго ссылку.
    fn shape(&mut self, labels: &[String], facts: &[Fact]) -> Result<CtorId, LowerError> {
        let found = self
            .constructors
            .iter()
            .find(|it| it.labels.as_deref() == Some(labels) && it.binders == facts);
        if let Some(constructor) = found {
            return Ok(constructor.tag);
        }
        let tag = u16::try_from(self.constructors.len())
            .ok()
            .filter(|tag| *tag < TAGS)
            .ok_or(LowerError::TooManyConstructors { limit: TAGS })?;
        let written: Vec<&str> = labels.iter().map(String::as_str).collect();
        self.constructors.push(Constructor {
            tag: CtorId(tag),
            name: format!("{{{}}}", written.join(", ")),
            data: "запись".to_owned(),
            binders: facts.to_vec(),
            params: 0,
            labels: Some(labels.to_vec()),
        });
        Ok(CtorId(tag))
    }

    /// Понижает тело определения, дописав к его спайну достроенные параметры.
    ///
    /// Дописать удаётся ровно спайну (§10 вопрос 153): у него голова - имя, и
    /// лишние аргументы делают вызов насыщенным вместо того, чтобы уходить
    /// применением к значению. Прочие формы тела применяют достроенные параметры
    /// обычным путём - через границу замыкания, где плоское по-прежнему
    /// отвергается.
    ///
    /// # Из двух стражей свидетеля получил один
    ///
    /// Сверка достроенного аргумента ([`Lowerer::given`]) свидетелем **обзавелась**
    /// вместе с массивами: один и тот же написанный тип `Array 3 a` читается
    /// плоским там, где в контексте есть `Flat a`, и указательным там, где его
    /// нет, - и телескопы вызывающего и вызываемого расходятся по-настоящему
    /// (`tests/array.rs`, `a_supplied_argument_is_checked_by_its_representation`).
    /// Прежде разойтись им было нечем: оба читали один тип.
    ///
    /// Сверка **применяемого значения** здесь свидетеля не получила, и причина
    /// теперь структурная, а не «пока нечем»: позиция эта - вызываемое, то есть
    /// тип-стрелка, а стрелка указательна при любом представлении элементов.
    /// Чтобы страж сработал, потребовалось бы плоское значение функционального
    /// типа, а такого нет ни одного. Страж остаётся; звать его покрытым
    /// по-прежнему нельзя.
    fn saturated(
        &mut self,
        scope: &mut Scope,
        term: &Term,
        extra: &[Binding],
        want: Repr,
    ) -> Result<(Expr, Repr), LowerError> {
        if extra.is_empty() {
            return self.expected(scope, term, want);
        }
        if matches!(term, Term::App(..) | Term::Const(..) | Term::Prim(_)) {
            let (head, written) = spine(term);
            let mut arguments: Vec<Arg<'_>> = written.into_iter().map(Arg::Written).collect();
            arguments.extend(extra.iter().map(Arg::Supplied));
            return self.application(scope, head, &arguments);
        }
        let (mut value, repr) = self.expr(scope, term)?;
        if !repr.boxed() {
            return Err(LowerError::Representation {
                at: "применяемое значение",
                want: describe(Repr::Boxed),
                got: describe(repr),
            });
        }
        for binding in extra {
            let argument = self.given(
                scope,
                &Arg::Supplied(binding),
                Repr::Boxed,
                "аргумент замыкания",
            )?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Понижает аргумент спайна и требует от него объявленного представления.
    ///
    /// Написанный проверяет `shaped`, достроенный - сверка ниже; свидетели
    /// стоят на обоих, см. [`Lowerer::saturated`].
    fn given(
        &mut self,
        scope: &mut Scope,
        argument: &Arg<'_>,
        want: Repr,
        at: &'static str,
    ) -> Result<Expr, LowerError> {
        match argument {
            Arg::Written(term) => self.shaped(scope, term, want, at),
            Arg::Supplied(binding) => {
                if !fits(binding.fact.repr, want) {
                    return Err(LowerError::Representation {
                        at,
                        want: describe(want),
                        got: describe(binding.fact.repr),
                    });
                }
                Ok(if binding.fact.present {
                    Expr::Local(binding.local)
                } else {
                    Expr::Erased
                })
            }
        }
    }

    /// Понижает применение с разложенным спайном.
    fn application(
        &mut self,
        scope: &mut Scope,
        head: &Term,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        if let Term::Prim(prim) = head {
            return self.primitive(scope, *prim, arguments);
        }
        let Term::Const(name, ..) = head else {
            // Голова - не имя: применяется значение, и стирания здесь не бывает.
            let mut value = self.shaped(scope, head, Repr::Boxed, "применяемое значение")?;
            for argument in arguments {
                let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        };
        match &self.definition(name)?.kind {
            DefinitionKind::Constructor { .. } => self.built(scope, name, arguments),
            DefinitionKind::Regular => self.called(scope, name, arguments),
            DefinitionKind::Data { .. } => Err(LowerError::TypeValue {
                name: name.to_string(),
            }),
            DefinitionKind::Effect { .. } | DefinitionKind::Operation { .. } => {
                Err(LowerError::Effectful {
                    name: name.to_string(),
                })
            }
        }
    }

    /// Понижает примитив: тип, литерал либо операцию (§4.3, §4.11).
    ///
    /// Ячейки кучи здесь не возникает ни на одной ветке - плоское значение
    /// живёт в регистре, - и это то самое, что показывает счётчик блоков.
    fn primitive(
        &mut self,
        scope: &mut Scope,
        prim: Prim,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        match prim {
            Prim::Ty(ty) => Err(LowerError::TypeValue {
                name: ty.name().to_owned(),
            }),
            Prim::Array => Err(LowerError::TypeValue {
                name: adamas_core::prim::ARRAY.to_owned(),
            }),
            Prim::Over(op) => self.array(scope, op, arguments),
            Prim::Lit(ty, bits) => {
                if arguments.is_empty() {
                    Ok((Expr::Literal { ty, bits }, Repr::Flat(ty)))
                } else {
                    Err(LowerError::Unsupported {
                        form: "литерал в позиции функции",
                    })
                }
            }
            Prim::Op(op, ty) => {
                let [left, right] = arguments else {
                    return Err(LowerError::Partial {
                        name: format!("{op}{ty}"),
                    });
                };
                let want = Repr::Flat(ty);
                let left = self.given(scope, left, want, "левый аргумент операции")?;
                let right = self.given(scope, right, want, "правый аргумент операции")?;
                Ok((
                    Expr::Primitive {
                        op,
                        ty,
                        left: Box::new(left),
                        right: Box::new(right),
                    },
                    want,
                ))
            }
        }
    }

    /// Операция над массивом (§4.11).
    ///
    /// Шаг индексации читается у **написанного** типа элемента - у того самого
    /// стёртого аргумента, который операция несёт вторым (у `arrayNew` -
    /// первым). Читается он там, а не у представления массива, ровно потому,
    /// что представление отвечает «плоский или указательный», а шаг - число, и
    /// приходит оно либо типом, либо дескриптором из контекста.
    fn array(
        &mut self,
        scope: &mut Scope,
        op: ArrayOp,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let wanted = match op {
            ArrayOp::New => 3,
            ArrayOp::Index => 4,
            ArrayOp::Set => 5,
        };
        if arguments.len() != wanted {
            return Err(LowerError::PartialArray {
                name: op.name().to_owned(),
            });
        }
        // Тип элемента: у `arrayNew` он единственный стёртый аргумент, у
        // прочих - второй, после длины.
        let at = usize::from(op != ArrayOp::New);
        let Arg::Written(element) = arguments[at] else {
            return Err(LowerError::PartialArray {
                name: op.name().to_owned(),
            });
        };
        let depth = u32::try_from(scope.env.len()).unwrap_or(u32::MAX);
        // Решение имплисита приезжает бета-редексом по контексту, поэтому тип
        // сперва нормализуется: `((\m -> #2) …)` переменной не является, а
        // после нормализации является.
        let element = normalized(element, depth);
        let dicts = scope.dicts.clone();
        let stride = self.stride_of(&element, depth, &dicts);
        // Представление ячейки: у плоского массива его даёт шаг, у
        // указательного - сам тип элемента. Второе не «просто указатель»:
        // `Array n Cell` держит записи, и форма их нужна проекции.
        let elements = match stride {
            Some(stride) => stride.element(),
            None => self.repr_of(&element, depth, &dicts)?,
        };
        let cells = stride.map_or(Elems::Boxed, |_| Elems::Flat);
        let word = Repr::Flat(PrimTy::UInt64);
        match op {
            ArrayOp::New => {
                let count = self.given(scope, &arguments[1], word, "длина массива")?;
                let initial = self.given(scope, &arguments[2], elements, "ячейка массива")?;
                Ok((
                    Expr::ArrayNew {
                        stride,
                        count: Box::new(count),
                        initial: Box::new(initial),
                    },
                    Repr::Array(cells),
                ))
            }
            ArrayOp::Index => {
                let array =
                    self.given(scope, &arguments[2], Repr::Array(cells), "читаемый массив")?;
                let at = self.given(scope, &arguments[3], word, "номер ячейки")?;
                Ok((
                    Expr::ArrayIndex {
                        stride,
                        array: Box::new(array),
                        at: Box::new(at),
                    },
                    elements,
                ))
            }
            ArrayOp::Set => {
                let array = self.given(
                    scope,
                    &arguments[2],
                    Repr::Array(cells),
                    "переписываемый массив",
                )?;
                let at = self.given(scope, &arguments[3], word, "номер ячейки")?;
                let value = self.given(scope, &arguments[4], elements, "ячейка массива")?;
                Ok((
                    Expr::ArraySet {
                        stride,
                        array: Box::new(array),
                        at: Box::new(at),
                        value: Box::new(value),
                    },
                    Repr::Array(cells),
                ))
            }
        }
    }

    /// Применение конструктора: насыщенное собирает объект, недобранное -
    /// замыкание.
    fn built(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let constructor = self.tag(name)?;
        let binders = self.constructors[usize::from(constructor.0)]
            .binders
            .clone();
        // Насыщено, если всё недоданное стёрто: у него значений нет вовсе.
        let complete = arguments.len() >= binders.len()
            || binders[arguments.len()..].iter().all(|fact| !fact.present);
        if !complete {
            // Недобранное собирается замыканием, а замыкание копит аргументы
            // слотами указателей: плоскому полю там места нет (§4.11).
            pointing(&binders, "поле недобранного конструктора")?;
            let mut value = Expr::ConstructClosure { constructor };
            for (position, argument) in arguments.iter().enumerate() {
                // Стёртая позиция применяется наравне с живой - замыкание
                // берёт **все** связывания ядра позиционно, - но написанное в
                // ней не понижается: параметром семейства стоит имя типа.
                let argument = if binders.get(position).is_some_and(|it| !it.present) {
                    Expr::Erased
                } else {
                    self.given(
                        scope,
                        argument,
                        Repr::Boxed,
                        "аргумент недобранного конструктора",
                    )?
                };
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        }
        let mut built = Vec::with_capacity(binders.len());
        for (position, fact) in binders.iter().enumerate() {
            if !fact.present {
                built.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            built.push(self.given(scope, argument, fact.repr, "поле конструктора")?);
        }
        // Переиспользование ставит вставка RC ([`crate::perceus`]): понижение
        // разобранного не помнит, а она помнит.
        let mut value = Expr::Construct {
            constructor,
            reuse: None,
            arguments: built,
        };
        for argument in arguments.iter().skip(binders.len()) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Применение определения: насыщенное зовёт напрямую, недобранное -
    /// замыкание.
    fn called(
        &mut self,
        scope: &mut Scope,
        name: &Name,
        arguments: &[Arg<'_>],
    ) -> Result<(Expr, Repr), LowerError> {
        let function = self.function(name)?;
        let parameters: Vec<Fact> = self.functions[function.0]
            .parameters
            .iter()
            .map(|it| it.fact)
            .collect();
        let result = self.functions[function.0].result;
        let complete = arguments.len() >= parameters.len()
            || parameters[arguments.len()..]
                .iter()
                .all(|fact| !fact.present);
        if !complete {
            // Недобранный вызов уходит замыканием, а трамплин отдаёт слоты
            // указателями: плоский параметр или плоский ответ через него не
            // проходят (§4.11).
            pointing(&parameters, "параметр недобранного вызова")?;
            if !result.boxed() {
                return Err(LowerError::Representation {
                    at: "ответ недобранного вызова",
                    want: describe(Repr::Boxed),
                    got: describe(result),
                });
            }
            let mut value = Expr::Closure {
                function,
                captured: Vec::new(),
            };
            for (position, argument) in arguments.iter().enumerate() {
                // Стёртая позиция применяется наравне с живой - замыкание
                // берёт **все** связывания ядра позиционно, - но написанное в
                // ней не понижается: значения у него нет, а стоять там может
                // и имя семейства.
                let argument = if parameters.get(position).is_some_and(|it| !it.present) {
                    Expr::Erased
                } else {
                    self.given(scope, argument, Repr::Boxed, "аргумент недобранного вызова")?
                };
                value = Expr::Apply {
                    callee: Box::new(value),
                    argument: Box::new(argument),
                };
            }
            return Ok((value, Repr::Boxed));
        }
        let mut given = Vec::with_capacity(parameters.len());
        for (position, fact) in parameters.iter().enumerate() {
            if !fact.present {
                given.push(Expr::Erased);
                continue;
            }
            let argument = arguments.get(position).ok_or_else(|| LowerError::Missing {
                name: name.to_string(),
                binder: position,
            })?;
            given.push(self.given(scope, argument, fact.repr, "аргумент вызова")?);
        }
        let mut value = Expr::Call {
            function,
            arguments: given,
        };
        let extra = arguments.len().saturating_sub(parameters.len());
        if extra == 0 {
            return Ok((value, result));
        }
        // Пересып: определение отдало функцию, и остаток спайна применяется к
        // ней. Стирания здесь уже нет - имени нет тоже.
        if !result.boxed() {
            return Err(LowerError::Representation {
                at: "применяемое значение",
                want: describe(Repr::Boxed),
                got: describe(result),
            });
        }
        for argument in arguments.iter().skip(parameters.len()) {
            let argument = self.given(scope, argument, Repr::Boxed, "аргумент замыкания")?;
            value = Expr::Apply {
                callee: Box::new(value),
                argument: Box::new(argument),
            };
        }
        Ok((value, Repr::Boxed))
    }

    /// Понижает разбор.
    fn analysis(&mut self, scope: &mut Scope, case: &Case) -> Result<(Expr, Repr), LowerError> {
        self.family(&case.data)?;
        // Разбирается объект: тег лежит в его заголовке, а у плоского значения
        // заголовка нет вовсе (§4.11).
        let scrutinee = self.shaped(scope, &case.scrutinee, Repr::Boxed, "разбираемое")?;
        // Пустой разбор ответа не даёт: тип пуст, и до печати дело не дойдёт.
        let mut answer = Repr::Boxed;
        let mut arms = Vec::with_capacity(case.branches.len());
        for branch in &case.branches {
            let constructor = self.tag(&branch.constructor)?;
            let described = &self.constructors[usize::from(constructor.0)];
            let params = described.params as usize;
            let facts: Vec<Fact> = described.binders.iter().skip(params).copied().collect();
            let mut fields: Vec<Binding> = facts
                .iter()
                .enumerate()
                .map(|(position, fact)| Binding {
                    name: format!("поле{position}"),
                    local: scope.fresh(),
                    fact: *fact,
                })
                .collect();

            // Тело ветви есть функция от полей: сколько ведущих лямбд, столько
            // связываний снимается на месте, остаток применяется.
            let mut current = Rc::new((*branch.body).clone());
            let mut taken = 0;
            while taken < fields.len() {
                let step = Rc::clone(&current);
                let Term::Lam(_, bound, inner) = &*step else {
                    break;
                };
                fields[taken].name = bound.to_string();
                scope
                    .env
                    .push(Slot::Bound(fields[taken].local, fields[taken].fact));
                current = Rc::clone(inner);
                taken += 1;
            }
            let body = self.expr(scope, &current);
            scope.env.truncate(scope.env.len() - taken);
            let (mut body, mut repr) = body?;
            for field in fields.iter().skip(taken) {
                if !repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "применяемое значение",
                        want: describe(Repr::Boxed),
                        got: describe(repr),
                    });
                }
                if field.fact.present && !field.fact.repr.boxed() {
                    return Err(LowerError::Representation {
                        at: "неснятое поле ветви",
                        want: describe(Repr::Boxed),
                        got: describe(field.fact.repr),
                    });
                }
                body = Expr::Apply {
                    callee: Box::new(body),
                    argument: Box::new(if field.fact.present {
                        Expr::Local(field.local)
                    } else {
                        Expr::Erased
                    }),
                };
                repr = Repr::Boxed;
            }
            // Ветви отвечают одним значением, значит и представление у них
            // одно: разойдись оно, у разбора не было бы C-типа.
            if arms.is_empty() {
                answer = repr;
            } else if fits(repr, answer) {
                // Годится как есть.
            } else if repr.pointer() && answer.pointer() {
                // Две записи разной формы либо запись с указателем: общее у них
                // одно - указатель, и форма теряется.
                answer = Repr::Boxed;
            } else {
                return Err(LowerError::Representation {
                    at: "ветвь разбора",
                    want: describe(answer),
                    got: describe(repr),
                });
            }
            arms.push(Arm {
                constructor,
                fields,
                body,
            });
        }
        Ok((
            Expr::Match {
                scrutinee: Box::new(scrutinee),
                consumed: case.consumed,
                arms,
            },
            answer,
        ))
    }

    /// Понижает лямбду в замыкание: своя функция плюс захваченная среда.
    ///
    /// Связывания лямбды объявляются указательными: типа у них в ядре нет, и
    /// прочитать представление неоткуда. Плоское значение поэтому через
    /// границу замыкания не проходит - ни захватом, ни аргументом, - и это
    /// названная граница, а не упущение: §4.11 отдаёт этот случай дескриптору
    /// layout, которого в рантайме ещё нет.
    fn closure(&mut self, scope: &mut Scope, term: &Term) -> Result<(Expr, Repr), LowerError> {
        let mut parameters: Vec<(Mult, String)> = Vec::new();
        let mut current = Rc::new(term.clone());
        loop {
            let step = Rc::clone(&current);
            let Term::Lam(mult, name, inner) = &*step else {
                break;
            };
            parameters.push((*mult, name.to_string()));
            current = Rc::clone(inner);
        }

        // Захватывается то, на что тело смотрит наружу.
        let mut free = BTreeSet::new();
        escaping(term, 0, &mut free);
        let depth = scope.env.len();
        let mut captured = Vec::new();
        let mut taken = Vec::new();
        let mut inner = Vec::with_capacity(depth + parameters.len());
        for (position, slot) in scope.env.iter().enumerate() {
            let index = u32::try_from(depth - position - 1).unwrap_or(u32::MAX);
            if !free.contains(&index) {
                inner.push(Slot::Absent);
                continue;
            }
            let Slot::Bound(local, fact) = slot else {
                return Err(LowerError::Unbound { index });
            };
            if fact.present && !fact.repr.pointer() {
                return Err(LowerError::Representation {
                    at: "захват замыкания",
                    want: describe(Repr::Boxed),
                    got: describe(fact.repr),
                });
            }
            let id = LocalId(u32::try_from(captured.len()).unwrap_or(u32::MAX));
            captured.push(Binding {
                name: format!("захвачено{}", captured.len()),
                local: id,
                fact: *fact,
            });
            taken.push(if fact.present {
                Expr::Local(*local)
            } else {
                Expr::Erased
            });
            inner.push(Slot::Bound(id, *fact));
        }

        let mut nested = Scope {
            locals: u32::try_from(captured.len()).unwrap_or(u32::MAX),
            env: inner,
            // Дескрипторы наружу не едут: захват объявлен указательным, а
            // словарь им не является. Обобщённый код внутри лямбды поэтому
            // считает элемент указательным - названная граница §4.11.
            dicts: Dicts::new(),
        };
        // Лямбда получает значение всегда: стирает машина по типу глобального
        // имени, а здесь имени нет.
        let bindings: Vec<Binding> = parameters
            .iter()
            .map(|(mult, name)| Binding {
                name: name.clone(),
                local: nested.fresh(),
                fact: Fact::present(*mult),
            })
            .collect();
        for binding in &bindings {
            nested.env.push(Slot::Bound(binding.local, binding.fact));
        }

        let function = FuncId(self.functions.len());
        self.functions.push(Function {
            id: function,
            name: format!("лямбда{}", function.0),
            form: form(),
            captured,
            parameters: bindings,
            // Ответ замыкания приходит через `adamas_apply`, а он говорит
            // указателями: плоский ответ ему не отдать.
            result: Repr::Boxed,
            body: Expr::Erased,
        });
        let body = self.shaped(&mut nested, &current, Repr::Boxed, "тело замыкания")?;
        self.functions[function.0].body = body;
        Ok((
            Expr::Closure {
                function,
                captured: taken,
            },
            Repr::Boxed,
        ))
    }
}

/// Форма понижения функции.
///
/// Спрашивается она у трёхзначного вердикта §3.4 - того же, который различает
/// `@noalloc`. Вердикта пока нет вовсе: [`adamas_core::alloc`] называет его
/// отсутствие своей границей и потому считает всякий элиминатор хендлера
/// аллоцирующим. Ответ здесь известен и без него, и не по умолчанию: чистый
/// фрагмент эффектов не содержит **по построению** - операция, метка и хендлер
/// отвергаются понижением, - а без них оказаться под общим или мультишотным
/// хендлером нечему. Появятся эффекты - здесь встанет вызов вердикта, а не
/// расширение этой функции догадками.
fn form() -> Form {
    Form::Stack
}

/// Дескриптор укладки, записанный по форме §4.11: `{ layout = { size, align } }`.
///
/// `None` - запись другой формы, и понижать её нечем: общего пути записей у
/// этого среза нет.
fn descriptor(fields: &[(Name, Rc<Term>)]) -> Option<(u32, u32)> {
    let [(name, inner)] = fields else {
        return None;
    };
    if &**name != "layout" {
        return None;
    }
    let Term::Object(pair) = &**inner else {
        return None;
    };
    let [(first, size), (second, align)] = &**pair else {
        return None;
    };
    if &**first != "size" || &**second != "align" {
        return None;
    }
    Some((number(size)?, number(align)?))
}

/// Литерал `UInt32` числом.
fn number(term: &Term) -> Option<u32> {
    match term {
        Term::Prim(Prim::Lit(PrimTy::UInt32, bits)) => u32::try_from(*bits).ok(),
        _ => None,
    }
}

/// Нормализует терм под `depth` связываниями контекста.
///
/// Нужно ровно одному месту - типу элемента массива: решение имплисита
/// приезжает бета-редексом `(\m₂ -> \m₁ -> \m₀ -> #2) #2 #1 #0`, и переменной
/// такой терм не является, пока редекс не сведён. Считает то же ядро, которым
/// считают все три вычислителя; своего правила здесь не заводится.
fn normalized(term: &Term, depth: u32) -> Term {
    let mut env = Env::default();
    for level in 0..depth {
        env = env.extend(Value::var(Lvl(level)));
    }
    quote(depth, &eval(&env, term))
}

/// Голова спайна и его аргументы слева направо.
fn spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut arguments = Vec::new();
    let mut head = term;
    while let Term::App(callee, argument) = head {
        arguments.push(&**argument);
        head = callee;
    }
    arguments.reverse();
    (head, arguments)
}

/// Тип после `at` снятых связываний. `None` - связываний столько нет.
fn after(ty: &Term, at: usize) -> Option<&Term> {
    let mut current = ty;
    for _ in 0..at {
        let Term::Pi(_, _, _, _, codomain) = current else {
            return None;
        };
        current = codomain;
    }
    Some(current)
}

/// Сколько алиасов подряд разворачивается по дороге к примитиву.
///
/// Цепочка `type Int = Int64` конечна по построению - ordered scoping (§4.8)
/// не даёт имени сослаться на себя, - но предел стоит: обход по чужой
/// сигнатуре не должен зависать, если она окажется собрана иначе.
const ALIASES: usize = 32;

/// Чтение представлений у **написанных** типов (§4.11, §4.2).
///
/// Методами, а не свободными функциями, потому что форма записи заводится по
/// дороге: у неё есть тег, и тег этот живёт в таблице конструкторов.
impl Lowerer<'_> {
    /// Представление значения написанного типа (§4.11, §4.2).
    ///
    /// Плоским считается ровно примитив: `Flat` над записями и семействами
    /// (§4.11, укладка тегом) существует типовой стороной, а укладывать его в
    /// понижении нечем, пока нет дескриптора layout, - это следующая половина
    /// трека.
    ///
    /// **Закрытая запись даёт форму** ([`Repr::Record`]): метки телескопа в его
    /// порядке, представления полей - тем же правилом рекурсивно. Открытая
    /// формы не даёт - её поля знает хвост, - и остаётся указательной.
    ///
    /// **Алиас разворачивается.** `Int` и `Float` - прелюдные синонимы `Int64` и
    /// `Float64` (§4.3, лог 2026-09-09), то есть каноническое имя написанной
    /// программы, и представление есть свойство типа, а не его написания: типовая
    /// сторона `Flat` (`adamas-elab/src/flat.rs`) читает укладку у **значения**
    /// типа и потому синоним видит насквозь. Разворачивается только имя без
    /// аргументов и только у определения, чей тип - универсум: параметризованный
    /// алиас требует подстановки, которой понижение не делает, и остаётся
    /// указательным.
    fn repr_of(&mut self, ty: &Term, depth: u32, dicts: &Dicts) -> Result<Repr, LowerError> {
        let current = unaliased(self.signature, ty).clone();
        if let Term::Prim(Prim::Ty(prim)) = current {
            return Ok(Repr::Flat(prim));
        }
        // Спайн: массив применён к длине и типу элемента, класс `Flat` - к типу.
        let (head, arguments) = spine(&current);
        match head {
            Term::Prim(Prim::Array) if arguments.len() == 2 => {
                let element = arguments[1].clone();
                return Ok(match self.stride_of(&element, depth, dicts) {
                    Some(_) => Repr::Array(Elems::Flat),
                    None => Repr::Array(Elems::Boxed),
                });
            }
            // `Flat` - единственный класс, чей словарь не объект кучи: у него
            // один метод, и метод этот сам есть укладка (§4.11). Проверяется он
            // **до** разворота, иначе развернулся бы в обычную запись.
            Term::Const(name, ..) if &**name == FLAT && arguments.len() == 1 => {
                return Ok(Repr::Layout);
            }
            _ => {}
        }
        match &unfolded(self.signature, &current, depth) {
            // Запись из одних примитивов плоская - §4.11 говорит это дословно,
            // - и потому уложена плотно, а не слотами объекта. Прочие записи
            // остаются объектом кучи: поле-указатель в плотную укладку не
            // ложится.
            Term::Record(fields) => match self.packed_shape(fields) {
                Some(packed) => Ok(packed),
                None => self.record_shape(fields, depth, dicts),
            },
            _ => Ok(Repr::Boxed),
        }
    }

    /// Плоская укладка записи, если все её поля примитивны (§4.11).
    ///
    /// `None` - хотя бы одно поле не примитив: указатель в плотную укладку не
    /// ложится, вложенный агрегат требовал бы проекции путём, а стёртое поле
    /// значения не имеет вовсе.
    fn packed_shape(&mut self, fields: &adamas_core::term::Fields) -> Option<Repr> {
        if fields.is_open() || fields.is_empty() {
            return None;
        }
        let mut labels = Vec::with_capacity(fields.len());
        let mut primitives = Vec::with_capacity(fields.len());
        for field in fields.iter() {
            let Term::Prim(Prim::Ty(prim)) = unaliased(self.signature, &field.ty) else {
                return None;
            };
            if field.mult == Mult::Zero {
                return None;
            }
            labels.push(field.name.to_string());
            primitives.push(*prim);
        }
        Some(Repr::Packed(self.packing(&labels, &primitives)))
    }

    /// Форма записи, прочитанная у её типа.
    ///
    /// Тип поля стоит **под предыдущими полями** телескопа (§4.2), поэтому
    /// глубина растёт по одному на поле: без этого зависимое поле читалось бы
    /// не в своём контексте.
    fn record_shape(
        &mut self,
        fields: &adamas_core::term::Fields,
        depth: u32,
        dicts: &Dicts,
    ) -> Result<Repr, LowerError> {
        if fields.is_open() {
            return Ok(Repr::Boxed);
        }
        let mut labels = Vec::with_capacity(fields.len());
        let mut facts = Vec::with_capacity(fields.len());
        for (position, field) in fields.iter().enumerate() {
            let under = depth + u32::try_from(position).unwrap_or(0);
            let repr = self.repr_of(&field.ty, under, dicts)?;
            labels.push(field.name.to_string());
            // Типовой член (`type T` в сигнатуре модуля, §4.8) значения в
            // рантайме не имеет: тип стёрт (§3.3), а кратность у него `1` -
            // элаборация даёт её всем членам одинаково. Судить поэтому
            // приходится по **сорту** поля, а не по кратности.
            let mut fact = Fact::declared(field.mult).shaped(repr);
            if universal(&field.ty) {
                fact.present = false;
            }
            facts.push(fact);
        }
        Ok(Repr::Record(self.shape(&labels, &facts)?))
    }

    /// Шаг индексации массива с таким элементом. `None` - элемент указательный.
    ///
    /// Плоским элемент бывает по трём причинам, и §4.11 называет все три.
    /// Примитив - шаг известен типом. **Запись, все поля которой плоские** -
    /// шаг есть её размер, посчитанный [`packing_of`]; это и есть колонка
    /// `Vec3`, ради которой §4.11 писался. И переменная, о которой в
    /// контексте есть словарь `Flat`, - шаг приходит дескриптором, а код один
    /// на все плоские элементы.
    ///
    /// Названная граница: агрегат берётся записью из **примитивов**. Семейство
    /// с тегом (§4.11, `Option Int64` в 16 байт) и вложенный агрегат сюда не
    /// входят - у первого нет конструирования плоским значением, у второго
    /// проекция шла бы путём, а не меткой.
    fn stride_of(&mut self, ty: &Term, depth: u32, dicts: &Dicts) -> Option<Stride> {
        let current = unaliased(self.signature, ty).clone();
        if let Term::Prim(Prim::Ty(prim)) = current {
            return Some(Stride::Static(prim));
        }
        if let Term::Var(Index(index)) = current {
            let level = depth.checked_sub(index + 1)?;
            return dicts.get(&level).copied().map(Stride::Dynamic);
        }
        let Term::Record(fields) = &unfolded(self.signature, &current, depth) else {
            return None;
        };
        match self.packed_shape(fields) {
            Some(Repr::Packed(pack)) => Some(Stride::Packed(pack)),
            _ => None,
        }
    }

    /// Укладка агрегата по меткам и полям; заводится однажды.
    fn packing(&mut self, labels: &[String], fields: &[PrimTy]) -> PackId {
        let made = packing_of(labels, fields);
        if let Some(at) = self.packings.iter().position(|it| *it == made) {
            return PackId(u32::try_from(at).unwrap_or(u32::MAX));
        }
        let id = PackId(u32::try_from(self.packings.len()).unwrap_or(u32::MAX));
        self.packings.push(made);
        id
    }

    /// Кратность и представление `n`-го связывания типа.
    ///
    /// Ровно то же, что считает машина: `None` значит «не стёрто», потому что
    /// связывания на этом месте синтаксически не видно.
    fn binder_at(
        &mut self,
        ty: &Term,
        at: usize,
        dicts: &Dicts,
    ) -> Result<Option<(Mult, Repr)>, LowerError> {
        let depth = u32::try_from(at).unwrap_or(u32::MAX);
        let Some(Term::Pi(binder, _, domain, _, _)) = after(ty, at) else {
            return Ok(None);
        };
        let (mult, domain) = (binder.mult, domain.clone());
        Ok(Some((mult, self.repr_of(&domain, depth, dicts)?)))
    }

    /// Представление ответа после `taken` снятых связываний.
    ///
    /// Снято меньше, чем стрелок в типе, - ответ функция, то есть указатель.
    fn result_repr(&mut self, ty: &Term, taken: usize, dicts: &Dicts) -> Result<Repr, LowerError> {
        let depth = u32::try_from(taken).unwrap_or(u32::MAX);
        let Some(result) = after(ty, taken).cloned() else {
            return Ok(Repr::Boxed);
        };
        self.repr_of(&result, depth, dicts)
    }

    /// Факты о связываниях типа: телескоп до результата.
    ///
    /// Словарей здесь нет: телескоп этот принадлежит конструктору, а дескриптор
    /// приходит имплиситом **функции** (§4.11). Элемент-переменная в поле
    /// конструктора поэтому указательный.
    fn binders_of(&mut self, ty: &Term) -> Result<Vec<Fact>, LowerError> {
        let empty = Dicts::new();
        let mut facts = Vec::new();
        let mut current = ty;
        let mut at = 0u32;
        while let Term::Pi(binder, _, domain, _, codomain) = current {
            let repr = self.repr_of(domain, at, &empty)?;
            facts.push(Fact::declared(binder.mult).shaped(repr));
            at += 1;
            current = codomain;
        }
        Ok(facts)
    }
}

/// Разворачивает **применённое** имя: класс, сигнатуру модуля, алиас с
/// параметрами.
///
/// Отдельно от [`unaliased`], потому что цена разная. Там разворот - чтение
/// тела по имени; здесь он требует подстановки, то есть счёта: `class Functor
/// f where map : …` объявляет `Functor : (Type -> Type) -> Type` с телом
/// `\f -> { map : … }`, и увидеть запись можно только сведя применение.
///
/// Нужно ровно ради формы записи (§4.2): словарь класса и значение модуля -
/// записи в ядре, и без разворота проекция метода не знала бы номера слота.
/// Считает то же ядро, которым считают все три вычислителя.
fn unfolded(signature: &Signature, ty: &Term, depth: u32) -> Term {
    let mut current = ty.clone();
    for _ in 0..ALIASES {
        let (head, arguments) = spine(&current);
        let Term::Const(name, ..) = head else {
            return current;
        };
        let Some(definition) = signature.lookup(name) else {
            return current;
        };
        if !matches!(definition.kind, DefinitionKind::Regular) || !universal(&definition.ty) {
            return current;
        }
        let Some(body) = definition.body.as_ref() else {
            return current;
        };
        let mut applied = body.clone();
        for argument in arguments {
            applied = Term::App(Rc::new(applied), Rc::new(argument.clone()));
        }
        current = normalized(&applied, depth);
    }
    current
}

/// Оканчивается ли тип универсумом - то есть объявляет ли имя тип.
fn universal(ty: &Term) -> bool {
    let mut current = ty;
    while let Term::Pi(_, _, _, _, codomain) = current {
        current = codomain;
    }
    matches!(current, Term::Universe(_))
}

/// Разворачивает цепочку синонимов до имени, у которого тела нет.
fn unaliased<'a>(signature: &'a Signature, ty: &'a Term) -> &'a Term {
    let mut current = ty;
    for _ in 0..ALIASES {
        let Term::Const(name, ..) = current else {
            return current;
        };
        let Some(definition) = signature.lookup(name) else {
            return current;
        };
        if !matches!(definition.kind, DefinitionKind::Regular)
            || !matches!(definition.ty, Term::Universe(_))
        {
            return current;
        }
        let Some(body) = definition.body.as_ref() else {
            return current;
        };
        current = body;
    }
    current
}

/// Ближайшее сверху кратное `align`. То же правило, что в типовой стороне.
fn aligned(offset: u32, align: u32) -> u32 {
    offset.next_multiple_of(align.max(1))
}

/// Плоская укладка записи из примитивных полей (§4.11).
///
/// «Укладка последовательная, выравнивание по максимальному `align` полей» -
/// правило дословно, и числа отсюда обязаны совпасть с теми, что выводит
/// типовая сторона (`adamas-elab/src/flat.rs`). Совпадение стоит теста
/// (`tests/packed.rs`), потому что запись числа здесь вторая: `adamas-codegen`
/// на элаборацию не смотрит.
///
/// Названная граница: поля только примитивные. Вложенный агрегат §4.11
/// укладывает тем же правилом, но проекция сквозь него - путь, а не метка, и
/// путей у этого среза нет.
fn packing_of(labels: &[String], fields: &[PrimTy]) -> Packing {
    let mut slots = Vec::with_capacity(fields.len());
    let mut size = 0u32;
    let mut align = 1u32;
    for ty in fields {
        let width = ty.size();
        let offset = aligned(size, width);
        slots.push(PackSlot { offset, ty: *ty });
        size = offset.saturating_add(width);
        align = align.max(width);
    }
    Packing {
        labels: labels.to_vec(),
        slots,
        size: aligned(size, align),
        align,
    }
}

/// Словари `Flat` телескопа: какое связывание о каком типе говорит.
///
/// Связывание `i` описывает тип, стоящий на уровне `i - 1 - d`, где `d` -
/// индекс переменной внутри домена `Flat #d`. Номера связываний те же, что
/// раздаёт [`Lowerer::peeled`], - позиция в телескопе.
fn dicts_of(signature: &Signature, ty: &Term) -> Dicts {
    let mut found = Dicts::new();
    let mut current = ty;
    let mut at = 0u32;
    while let Term::Pi(binder, _, domain, _, codomain) = current {
        if binder.mult != Mult::Zero {
            let (head, arguments) = spine(unaliased(signature, domain));
            if let (Term::Const(name, ..), [Term::Var(Index(index))]) = (head, arguments.as_slice())
            {
                if &**name == FLAT {
                    if let Some(level) = at.checked_sub(index + 1) {
                        found.insert(level, LocalId(at));
                    }
                }
            }
        }
        at += 1;
        current = codomain;
    }
    found
}

/// Индексы, уходящие за `depth`, приведённые к внешнему счёту.
///
/// Обход идёт по позициям, где значение доживает до исполнения: типы, мотив
/// разбора и телескопы пропускаются - переменную оттуда захватывать незачем,
/// а понижение туда не заходит вовсе.
fn escaping(term: &Term, depth: u32, out: &mut BTreeSet<u32>) {
    match term {
        Term::Var(Index(index)) => {
            if *index >= depth {
                out.insert(index - depth);
            }
        }
        Term::Lam(_, _, body) => escaping(body, depth + 1, out),
        Term::App(callee, argument) => {
            escaping(callee, depth, out);
            escaping(argument, depth, out);
        }
        Term::Let(_, _, _, value, body) => {
            escaping(value, depth, out);
            escaping(body, depth + 1, out);
        }
        Term::Case(case) => {
            escaping(&case.scrutinee, depth, out);
            for branch in &case.branches {
                escaping(&branch.body, depth, out);
            }
        }
        _ => {}
    }
}

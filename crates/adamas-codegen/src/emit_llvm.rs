//! Эмиттер LLVM: [`ir`](crate::ir) в текст `.ll` (§9 Фаза 7, волна 1, треки
//! A и A′).
//!
//! **Ядра этот модуль не читает** - ровно как [`emit_c`](crate::emit_c), и по
//! той же проверяемой причине: шов между ядром и эмиттером существует затем,
//! чтобы Фаза 7 добавила **второй эмиттер**, а не второй компилятор
//! (`docs/phase7-plan.md`, «Что Фаза 7 требует от Фазы 6»). Свидетель -
//! `tests/seam.rs`, читающий исходник этого файла.
//!
//! # Способ привязки - текст
//!
//! Не `inkwell` и не `llvm-sys`: решение 2026-09-15 на основании замеров
//! 2026-09-08 - разбор `.ll` берёт 6% времени бэкенда, и доля падает с
//! размером, а проверок текстовый путь не теряет, потому что делает их verifier
//! на прогоне, а не система типов Rust.
//!
//! Цена решения - **правило консервативного подмножества**: новых
//! необязательных атрибутов IR не использовать без причины. Проверяется правило
//! прогоном на минимальной поддерживаемой версии
//! ([`llvm::MINIMUM_MAJOR`](crate::llvm::MINIMUM_MAJOR)), а не грепом по
//! формам, - той же дисциплиной, что MSRV, и заведена она так потому, что греп
//! по формам врал трижды подряд.
//!
//! Что из правила следует построчно: у целочисленной арифметики **нет** `nsw` и
//! `nuw`; у [`getelementptr`](Builder::slot_pointer) нет ни `inbounds`, ни
//! `nuw`; ни `target datalayout`, ни `target triple` не пишется - цель берёт
//! `llc` у хоста, и вписанная строка сделала бы `.ll` непереносимым между
//! архитектурами.
//!
//! GEP - первая форма, которой правило коснулось, и треугольник версий на ней
//! **перемерен** (2026-09-15, трек A′, обе цепочки dev-shell): 18.1.8 отвергает
//! `getelementptr inbounds nuw` разбором (`error: expected type`) и принимает
//! как голый `getelementptr`, так и `getelementptr inbounds`. То есть ломает
//! чтение ровно `nuw`, как и записано в плане, а не `inbounds`. Голый выбран
//! всё равно: `inbounds` здесь законен - слот лежит внутри блока, - но правило
//! говорит «без причины не использовать», а причины, которую можно предъявить
//! числом, у него нет.
//!
//! # Что берёт этот срез
//!
//! Скалярный фрагмент плюс **объектный слой**. Скалярное: плоское значение (все
//! десять типов §4.11), арифметика, сравнение, прямой вызов первой формы,
//! `let`, разбор, `dup` и `drop`. Объектное: [`Expr::Construct`] через
//! `adamas_alloc`, придержанная ячейка ([`Expr::Reclaim`], `adamas_reuse` и
//! `adamas_drop_reuse`), поля в ветви разбора, схлопнутый дроп разобранного
//! ([`Salvage`], §5.1) и ответ программы объектом кучи либо записью.
//!
//! Не берётся - и отвергается **названным** отказом ([`LlvmError`]): замыкания,
//! массивы, регионы, плотные агрегаты, вторая форма понижения и всё, что за ней
//! стоит, - хендлеры, резумпции, питомник.
//!
//! # Где стояла граница на самом деле
//!
//! Трек A измерил корпус в 2 из 100 и назвал причину у 79 отказов одну: ответ
//! программы - объект кучи, а спутник печати берёт только плоское целое. Отсюда
//! читалось, что граница узкая и стоит у **печати**. Трек A′ это проверил
//! пробной правкой, и **не подтвердилось**: снятая в одиночку, печать даёт
//! те же 2 из 100. Гистограмма за ней другая - 45 конструктор, 17 эффект, 11
//! поля в ветви, - потому что отказ печатью стоял первым и заслонял второй ряд.
//!
//! Мера объектного слоя поэтому считается его собственным потолком, а не
//! разностью: 21 из 100 при отвергнутом плавающем, и следующая стена названа -
//! 43 эффект и 15 замыкание, то есть волна 2 и слой замыканий, а не этот трек.
//!
//! # Что объектный слой знает о раскладке
//!
//! Ровно два числа - [`HEADER_BYTES`] и [`SLOT_BYTES`], - и обязаны они совпасть
//! с `adamas.h`. Совпадение **проверяется сборкой**: спутник несёт
//! `_Static_assert` с этими же числами, подставленными отсюда, и разъедься они
//! с рантаймом - не соберётся спутник, а не разойдётся ответ.
//!
//! Знать их приходится потому, что слот читается и пишется **инструкцией**, а
//! не вызовом `adamas_field`/`adamas_set_field`. Довод - трек C: вызов в чужую
//! единицу трансляции непрозрачен для `opt`, и «RC-трафик на объектах» через
//! него не увидеть ни до, ни после инлайнинга. Куча при этом остаётся за
//! рантаймом целиком: блок выдаёт `adamas_alloc`, придерживает
//! `adamas_drop_reuse`, занимает `adamas_reuse`, освобождает `adamas_free`.
//!
//! # Уникальность производства: что берёт трек B
//!
//! [`Fact::unique`] приезжает на IR проходом [`crate::unique`] и читается в
//! **одном** месте - [`Builder::salvaged_unique`]. Где производство уникально,
//! вопроса `adamas_is_unique` не задаётся вовсе: печатается одна ветвь из двух,
//! и вместе со второй уходят `dup` взятых полей, `adamas_drop` родителя, два
//! блока, ветвление и `phi` придержанной ячейки.
//!
//! Мера - вызовы рантайма и инструкции, **не** счётчик блоков: на
//! `resource-cleanup` вопросов 6 против 4, вызовов после `-O2` 61 против 55,
//! инструкций 321 против 301 (штатный конвейер); выдано 17 в обоих случаях.
//! Так и должно быть - рантайм принимал то же решение и без факта, а счётчик
//! считает решения, а не цену их принятия.
//!
//! Метаданные алиасинга при этом не ставятся ни одни: замер в `tests/alias.rs`.
//!
//! # Плавающее: строгий режим (§4.3, трек F)
//!
//! Два обещания §4.3, и оба здесь исполняются формой инструкции, а не ключом.
//!
//! *Контракции нет.* `a * b + c` остаётся `fmul` плюс `fadd`, и слиться в `fma`
//! им нечем: в LLVM контракцию разрешает **флаг на инструкции** (`contract`), а
//! не запрещает - см. [`Builder::arithmetic`], где сказано, что именно
//! измерено и где у обещания граница.
//!
//! *Сравнение идёт по `totalOrder`, а не по IEEE.* `fcmp` здесь был бы прямой
//! ошибкой: у него `nan == nan` ложно и `-0.0 == 0.0` истинно, то есть ровно
//! две точки, в которых §4.3 расходится с IEEE. Ключ порядка считается
//! [`Builder::key`] - тем же преобразованием битов, каким его считают
//! `adamas_order_*` в `flat.c` и [`PrimTy`] в ядре.
//!
//! # Где встанут треки B-F
//!
//! Каждый режет в **одном** месте, и место названо здесь, чтобы его не искали
//! по тексту.
//!
//! - **B, алиасинг из QTT. Закрыт** 2026-09-15, и закрыт отрицательно по
//!   метаданным: ни одно из них не ставится, потому что ни одно не меняет
//!   инструкции (см. [`parameter_attributes`] и раздел про уникальность ниже).
//!   Читается [`Fact::unique`] - ветвлением, а не атрибутом.
//! - **C, схлопывание RC. Закрыт** 2026-09-15: [`collapse`](crate::collapse) -
//!   стадия конвейера ([`llvm::Pipeline::collapsing`](crate::llvm::Pipeline)),
//!   снимающая пару `dup`/`drop`, которую инлайнинг свёл в одну функцию.
//!   Эмиттера трек не тронул вовсе, и это его главная находка: пара рождается
//!   **после** эмиссии, из подстановки тела вызываемого, и на выходе этого
//!   файла её ещё нет.
//! - **D, `musttail`. Закрыт**: [`Tail`] получил второе значение, и как оно
//!   выбирается, сказано ниже отдельным разделом.
//! - **E, DWARF. Закрыт**: [`Notes`] подписывает инструкцию, узлы модуля
//!   заводит [`Metadata`]; подробности - разделом ниже.
//! - **F, строгий режим плавающей арифметики. Закрыт** 2026-09-15; см. раздел
//!   про плавающее выше. Тип DWARF плавающему ([`Dwarf::ty`]) выдан тем же
//!   треком.
//!
//! # Отладочная информация: что взял трек E
//!
//! DWARF пишется **текстом**, как и всё остальное: `!DICompileUnit`,
//! `!DISubprogram`, `!DILocalVariable`, `!DILocation`, вызовы
//! `llvm.dbg.declare`. `DIBuilder` из плана - API, а волна 0 выбрала текст, и
//! суть требования от способа не изменилась: текстом выразилось всё, что нужно
//! отладчику.
//!
//! Появляется она **от исходника** ([`Program::source`](crate::ir::Program)), а
//! не от ключа сборки: нет текста - выход байт в байт прежний.
//!
//! Потолок мелкости - **функция**. Позиция в IR лежит на ней, потому что спанов
//! в ядре нет вовсе, и шаг отладчика идёт между определениями `.adamas`, а не
//! между выражениями внутри одного. Свидетель - `tests/debug.rs`.
//!
//! # Хвостовой вызов - свойство инструкции (трек D)
//!
//! Обещание §3.4 и §5.3 - «хвостовой вызов не растит стек» - держится здесь, а
//! не на ключах сборки. Три решения, и каждое взято замером.
//!
//! *Соглашение о вызове - [`CONVENTION`], а не C.* `musttail` при C-соглашении
//! требует **совпадения прототипов** вызывающего и вызываемого, а первая же
//! программа корпуса его ломает: `main` без параметров хвостом зовёт `mix`
//! двух. Отсюда `tailcc` на всех порождённых определениях и на всех вызовах к
//! ним. Точка входа [`ENTRY_SYMBOL`] остаётся с C-соглашением - её зовёт
//! спутник, - и вызов из неё хвостовым не помечается.
//!
//! *Хвостовая позиция считается **анализом**, а не полем узла.* Признака
//! хвоста у [`Expr::Call`] нет и заводить его не следует: хвост есть свойство
//! **контекста**, а не вызова, и всякая правка представления его меняет. Ближе
//! всего пример Perceus: дроп, вставленный **после** вызова, хвост отнимает, а
//! вставленный до - оставляет; поле пришлось бы пересчитывать в проходе,
//! который про хвосты ничего не знает. Обход [`Builder::tail`] это различает по
//! построению - `Expr::Drop { body }` спускает хвост в тело, `Expr::Bind {
//! value }` не спускает.
//!
//! *`phi` в хвостовой позиции не строится вовсе.* LLVM требует, чтобы за
//! `musttail` немедленно шёл `ret`; ветвь разбора, кончающаяся `br label
//! %join`, требование ломает. Поэтому разбор в хвостовой позиции печатается
//! **без** блока стыковки: каждая ветвь возвращает сама
//! ([`Builder::analysis_tail`]). Цена - вторая печать разбора рядом с
//! [`Builder::analysis`]; выигрыш - на витке нет ни `phi`, ни лишнего блока.
//!
//! # Чем срез платил рантайму, и это снято
//!
//! Сравнение (§4.3) отвечает конструктором `Bool`, а строит и разбирает его
//! **рантайм** - `adamas_con0` и `adamas_tag`. Для `opt` они непрозрачны, и
//! трек A измерил цену: на `workload-scalar` после `-O2` оставался цикл с двумя
//! вызовами на виток, тогда как у C-бэкенда та же пара исчезала на сборке
//! (`-std=c11 -O2 -flto`, ноль вызовов в бинаре по `objdump -d`). Разница была
//! не в качестве кодогенерации, а в том, что рантайм приезжает к C битовым
//! кодом LTO, а к `.ll` - готовым объектником.
//!
//! Снято это **не правкой эмиттера**, а стадией конвейера
//! ([`Pipeline::whole_program`](crate::llvm::Pipeline::whole_program), трек A′):
//! рантайм собирается в `.bc` и прикладывается `llvm-link` перед `opt`. Замер
//! 2026-09-15: на `workload-fbip` вызовов рантайма после `-O2` было 22, стало
//! 0; на `workload-symbolic` 29 и 0; на `workload-scalar` 4 и 0, то есть та
//! самая пара ушла. Ответ и счётчик блоков те же, переиспользование ячейки
//! инлайнинг переживает. Свидетель - `tests/llvm.rs`.
//!
//! Штатный конвейер стадии не несёт, и это решение, а не недоделка: `.bc`
//! рантайма собран под хост, а `.ll` переносим - подробности там же, в
//! [`Pipeline::whole_program`](crate::llvm::Pipeline::whole_program).
//!
//! # Что рядом с `.ll` и почему
//!
//! Спутник на C ([`Artefacts::support`]): печать ответа, дроп его детей и точка
//! входа. Он не уступка - это **те же** `flat.c`, `print.c`, `release.c` и
//! `main.c`, что собирает C-бэкенд, взятые дословно теми же `include_str!`, над
//! той же таблицей конструкторов ([`emit_c::table`](crate::emit_c::table)).
//! Разъедься две печати - разошёлся бы и договор «печатает то же», а причина
//! была бы не в вычислении. Программу считает `.ll` целиком; спутник её только
//! печатает и дропает.
//!
//! Одну строку спутник добавляет от себя - [`RELEASE_SYMBOL`]: `release.c`
//! объявляет дроп детей `static`, а зовёт его порождённый IR из **другой**
//! единицы трансляции.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use adamas_core::prim::{PrimCmp, PrimOp, PrimTy};

use adamas_core::source::Location;

use crate::ir::{
    Arm, Binding, Constructor, CtorId, Expr, Fact, Form, FuncId, Function, LocalId, Program, Repr,
    Salvage, Source, Unique,
};

/// Почему эмиссия в LLVM отказала.
///
/// Отказ **названный**, как у понижения: молча посчитать не то хуже, чем не
/// посчитать. Мера среза читается прогоном по корпусу (`tests/llvm.rs`), а не
/// оценкой, и каждая причина здесь - строка этой меры.
#[derive(Debug, thiserror::Error)]
pub enum LlvmError {
    /// Узел представления, которого скалярный фрагмент не знает.
    #[error("`{function}`: {node} - узел вне скалярного фрагмента")]
    Node {
        /// Чья функция.
        function: String,
        /// Какой узел.
        node: &'static str,
    },

    /// Представление, которое в регистр не ложится.
    #[error("`{function}`: {place} - {shape}, а срез берёт только плоское значение")]
    Shape {
        /// Чья функция.
        function: String,
        /// Что именно: параметр, ответ, промежуточное значение.
        place: String,
        /// Как оно представлено.
        shape: String,
    },

    /// Вторая форма понижения: кадр отчуждается в кучу (§3.4).
    #[error("`{function}`: вторая форма понижения - кадров этот срез не кладёт")]
    Detached {
        /// Чья функция.
        function: String,
    },
}

/// Что даёт эмиссия: текст `.ll` и спутник на C.
#[derive(Clone, Debug)]
pub struct Artefacts {
    /// Текст `.ll`: программа целиком.
    pub ll: String,
    /// Спутник на C: печать ответа и точка входа.
    pub support: String,
}

/// Имя точки входа, которую спутник зовёт из `.ll`.
const ENTRY_SYMBOL: &str = "adamas_entry";

/// Имя дропа детей, видимого из `.ll`.
///
/// Своё, а не `adamas_release_value`: `release.c` объявляет тот `static`, и
/// линковать его из другой единицы трансляции нечем. Обёртка стоит в спутнике,
/// то есть **одна** на программу, и дроп за ней тот же самый, что у C-бэкенда.
pub const RELEASE_SYMBOL: &str = "adamas_release_extern";

/// Имя константы с текстом обрыва по неизвестному тегу.
const TAG_MESSAGE: &str = "@.str.tag";

/// Смещение первого слота от начала объекта, в байтах (`adamas.h`).
///
/// Не догадка и не соглашение этого файла: `adamas.h` держит на нём
/// `_Static_assert(offsetof(adamas_object, fields) == 8)`, и спутник повторяет
/// проверку **этим** числом ([`support`]). Разъехавшись, они уронят сборку, а
/// не ответ.
pub const HEADER_BYTES: u32 = 8;

/// Ширина слота объекта, в байтах.
///
/// Слово на слот, а не упакованные байты: плотная укладка §4.11 принадлежит
/// плоским массивам и агрегатам, а слот объекта Perceus носит либо указатель,
/// либо биты числа в целом слове (`flat.c`).
pub const SLOT_BYTES: u32 = 8;

/// Атрибуты определения функции.
///
/// `nounwind` - утверждение о **нашем** коде: раскрутки в порождённом нет
/// вовсе, обрыв идёт через `adamas_fail`. На объявления рантайма он не
/// ставится: про чужой код это было бы обещанием, а не фактом.
const DEFINITION_ATTRIBUTES: &str = "nounwind";

/// Соглашение о вызове порождённых функций (трек D).
///
/// `tailcc`, а не C-соглашение, и причина одна: при C-соглашении `musttail`
/// требует совпадения прототипов вызывающего с вызываемым, а хвостовой вызов
/// между разными сигнатурами в языке обычен - `main : UInt64` хвостом зовёт
/// `mix : UInt64 -> UInt64 -> UInt64` в первой же программе корпуса. `tailcc`
/// это требование снимает и разрешает вызываемому **больше** аргументов, чем у
/// вызывающего; ровно этого не умеет и обычная оптимизация хвостового вызова в
/// `llc` (измерено, `tests/tail.rs`).
///
/// Соглашение обязано совпадать у определения и у каждого вызова, поэтому
/// печатается оно и там и там. Исключение одно - [`ENTRY_SYMBOL`]: его зовёт
/// спутник на C, и C-соглашение у него не выбор, а договор.
const CONVENTION: &str = "tailcc";

/// Собирает `.ll` и спутник на C.
///
/// # Errors
///
/// [`LlvmError`] - форма понижения вне скалярного фрагмента.
pub fn emit(program: &Program) -> Result<Artefacts, LlvmError> {
    let entry = &program.functions[program.entry.0];
    let answer = Answer::of(entry)?;
    // Точка входа зовётся без аргументов, и подать их было бы неоткуда: `main`
    // с параметром есть функция значением, а её ответ печатать нечем и у
    // C-бэкенда (`agreement.rs`, `LANGUAGE`).
    if entry.live_parameters().next().is_some() {
        return Err(LlvmError::Shape {
            function: entry.name.clone(),
            place: "точка входа".to_owned(),
            shape: "функция с параметрами".to_owned(),
        });
    }

    let mut module = Module::default();
    // Отладочная информация появляется **от исходника**, а не от ключа сборки:
    // нет текста - нечего и называть отладчику, и выход тогда байт в байт тот
    // же, что был до трека E.
    if let Some(source) = &program.source {
        module.dwarf = Some(Dwarf::new(&mut module.metadata, source));
    }
    for function in &program.functions {
        module.function(program, function)?;
    }
    Ok(Artefacts {
        ll: module.finish(program, answer),
        support: support(program, answer),
    })
}

/// Чем отвечает программа: тем и различаются две печати спутника.
///
/// Форм две, потому что их две у `main.c`, взятого дословно: плоское лежит в
/// регистре и печатается по сорту, объект приходит владением и после печати
/// дропается. Третьей формы нет и у C-бэкенда.
#[derive(Clone, Copy, Debug)]
enum Answer {
    /// Плоское: печатается сортом, дропать нечего.
    Flat(PrimTy),
    /// Объект кучи либо запись: печатается таблицей, дропается спутником.
    Boxed,
}

impl Answer {
    /// Чем отвечает точка входа. Прочее - названный отказ.
    fn of(entry: &Function) -> Result<Self, LlvmError> {
        if let Some(ty) = entry.result.primitive() {
            return Ok(Self::Flat(ty));
        }
        // Запись сюда входит, резумпция - нет: печатать её нечем и у
        // C-бэкенда (`print.c` ответил бы `?tag`), а дроп у неё свой.
        if matches!(entry.result, Repr::Boxed | Repr::Record(_)) {
            return Ok(Self::Boxed);
        }
        Err(LlvmError::Shape {
            function: entry.name.clone(),
            place: "ответ программы".to_owned(),
            shape: describe(entry.result),
        })
    }

    /// Тип регистра, которым ответ уходит из `.ll`.
    const fn machine(self) -> &'static str {
        match self {
            Self::Flat(ty) => machine(ty),
            Self::Boxed => "ptr",
        }
    }
}

/// Как назвать представление в тексте отказа.
fn describe(repr: Repr) -> String {
    match repr {
        Repr::Flat(ty) => format!("плоское {}", ty.name()),
        Repr::Boxed => "объект кучи".to_owned(),
        Repr::Packed(_) => "плотный агрегат".to_owned(),
        Repr::Layout => "дескриптор укладки".to_owned(),
        Repr::Opaque => "плоское неизвестной ширины".to_owned(),
        Repr::Array(_) => "массив".to_owned(),
        Repr::Region => "блок региона".to_owned(),
        Repr::Record(_) => "запись".to_owned(),
        Repr::Resumption => "резумпция".to_owned(),
    }
}

/// Тип LLVM у плоского значения.
///
/// Знаковость типом не выражается вовсе - её несёт инструкция (`sdiv` против
/// `udiv`, `slt` против `ult`), и это не потеря: §4.11 различает `Int64` и
/// `UInt64` шириной и правилом сравнения, а ширина здесь та же.
const fn machine(ty: PrimTy) -> &'static str {
    match ty {
        PrimTy::Int8 | PrimTy::UInt8 => "i8",
        PrimTy::Int16 | PrimTy::UInt16 => "i16",
        PrimTy::Int32 | PrimTy::UInt32 => "i32",
        PrimTy::Int64 | PrimTy::UInt64 => "i64",
        PrimTy::Float32 => "float",
        PrimTy::Float64 => "double",
    }
}

/// Целое той же ширины: в нём живёт ключ порядка (§4.3).
///
/// У целых типов оно совпадает с [`machine`] - ключ у них и есть само значение
/// с перевёрнутым знаковым разрядом, а переворачивает его предикат `icmp`.
const fn word(ty: PrimTy) -> &'static str {
    match ty {
        PrimTy::Float32 => "i32",
        PrimTy::Float64 => "i64",
        other => machine(other),
    }
}

/// Плоская константа в тексте `.ll`.
///
/// Целое - беззнаковым десятичным: LLVM принимает всё, что укладывается в
/// ширину, а биты в представлении уже обрезаны понижением.
///
/// Плавающее - **шестнадцатеричной** формой, той самой, которую LLVM завёл для
/// точной записи. Десятичная запись поехала бы через разбор строки, а §4.3
/// обещает биты, а не близкое к ним число.
fn constant(ty: PrimTy, bits: u64) -> String {
    match ty {
        PrimTy::Float32 => format!("0x{:016X}", widened(bits)),
        PrimTy::Float64 => format!("0x{bits:016X}"),
        _ => bits.to_string(),
    }
}

/// Биты `Float32`, расширенные до `double`.
///
/// Так устроен разбор `.ll`: константа одинарной точности пишется в нём
/// шестнадцатеричным `double`, и сужение обратно обязано быть точным. Оно
/// точно - младшие 29 бит расширения нулевые по построению, - и `llvm-as`
/// отвергает запись, у которой это не так.
///
/// NaN расширяется **руками**, а не приведением: приведение железом квитирует
/// сигнальный NaN, то есть меняет биты, которые §4.3 обещает сохранить.
#[expect(
    clippy::cast_possible_truncation,
    reason = "биты `Float32` лежат в младшей половине слова по построению"
)]
fn widened(bits: u64) -> u64 {
    let bits = bits as u32;
    let single = f32::from_bits(bits);
    if single.is_nan() {
        let sign = u64::from(bits >> 31) << 63;
        let payload = u64::from(bits & 0x007f_ffff) << 29;
        return sign | (0x7ffu64 << 52) | payload;
    }
    f64::from(single).to_bits()
}

/// Сорт вызова (трек D).
///
/// `musttail` есть свойство **инструкции**, а не ключей пользователя (§3.4,
/// §5.3): оптимизация хвостового вызова, которую `llc` делает сам, идёт только
/// с `-O2` и только там, где кадру вызываемого хватает места вызывающего.
/// Приставка снимает оба условия.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Tail {
    /// Обычный вызов: кадр вызывающего живёт дальше.
    Plain,
    /// Хвостовой: кадр вызывающего замещается кадром вызываемого.
    ///
    /// Требование LLVM к такому вызову одно, и его обязан выполнить эмиттер: за
    /// инструкцией немедленно следует `ret` того же значения. Отсюда разбор без
    /// `phi` в хвостовой позиции ([`Builder::analysis_tail`]).
    Must,
}

impl Tail {
    /// Приставка инструкции вызова.
    const fn prefix(self) -> &'static str {
        match self {
            Self::Plain => "",
            Self::Must => "musttail ",
        }
    }
}

/// Метаданные **одной** инструкции.
///
/// Аргумент [`Builder::instruction`], а не поле билдера, и разница
/// принципиальная: суффикс, лежащий полем, одинаков у всех инструкций подряд, а
/// ни одни из требуемых метаданных таковыми не являются. `!dbg` различается от
/// инструкции к инструкции - у пролога он свой (трек E, [`Builder::prologue`]).
/// Под scoped `!alias.scope`/`!noalias` механизм заводился тоже, и они его не
/// заняли: трек B их не поставил - регионов в IR нет, а на объектах они дают
/// ноль инструкций (`tests/alias.rs`). Довод про аргумент от этого не слабеет,
/// его держит `!dbg`: у пролога локация своя, у тела своя. Но других носителей
/// у механизма нет, и второй ожидался отсюда.
///
/// Собирается цепочкой: [`Notes::none`] плюс [`Notes::and`] на каждый узел.
/// Окружающие метаданные - те, что несёт всякая инструкция тела, - отдаёт
/// [`Builder::here`], и своё дописывается к ним:
/// `self.here().and("alias.scope", "!7")`.
#[derive(Clone, Debug, Default)]
struct Notes {
    /// Узлы в порядке печати.
    items: Vec<String>,
}

impl Notes {
    /// Ни одной.
    const fn none() -> Self {
        Self { items: Vec::new() }
    }

    /// Дописывает узел: `!kind !N`.
    fn and(mut self, kind: &str, node: &str) -> Self {
        self.items.push(format!("!{kind} {node}"));
        self
    }

    /// Хвост инструкции. Пустой список не печатает даже запятой.
    fn suffix(self) -> String {
        if self.items.is_empty() {
            return String::new();
        }
        format!(", {}", self.items.join(", "))
    }
}

/// Атрибуты параметра: пусто, и это результат замера (трек B).
///
/// Здесь стояли бы `noalias`, `dereferenceable` и `align`. Не стоит ни один, и
/// у каждого своя причина.
///
/// *`noalias` ничего не даёт.* Поставленный **щедро** - на каждый указательный
/// параметр - он меняет ноль инструкций на трёх нагрузках (`tests/alias.rs`).
/// Причина видна в выходе: после инлайнинга `noalias` превращается в scoped
/// `!noalias`, но горячий виток FBIP - это самохвостовая рекурсия, свёрнутая в
/// **один** цикл внутри одной области видимости, и разные итерации попадают в
/// одну и ту же scope. Различать им себя нечем.
///
/// *`dereferenceable` и `align` не просто бесполезны - на [`Repr::Boxed`] они
/// неверны.* `adamas.h` говорит прямо: ставить их законно только там, где
/// `adamas_is_imm` уже дал ложь, а `Boxed` покрывает и непосредственное
/// значение - нульарный конструктор приезжает числом `1`. Обещание разрешает
/// поднять чтение тега до проверки, и программа падает: свидетель
/// `dereferenceable_on_a_boxed_parameter_is_a_fault`.
///
/// Уникальность при этом **есть** и читается - [`Fact::unique`], - но не здесь:
/// её место [`Builder::salvaged_unique`], где она снимает вопрос рантайму, а не
/// обещает что-то оптимизатору.
fn parameter_attributes(fact: &Fact) -> String {
    let _ = fact;
    String::new()
}

/// Узлы метаданных модуля, нумерованные порядком заведения.
///
/// Номер выдаётся при записи и возвращается ссылкой `!N`: узлы DWARF ссылаются
/// друг на друга, и держать номер в голове пришлось бы иначе на каждом.
#[derive(Debug, Default)]
struct Metadata {
    /// Узлы по номеру.
    nodes: Vec<String>,
    /// Уже заведённые узлы: текст к ссылке.
    ///
    /// LLVM уникализирует неразличимые узлы сама, поэтому вторая копия
    /// `!DIBasicType(name: "Int64", ...)` не ошибка - она просто занимает место
    /// в тексте. Копий выходит по одной на каждое упоминание типа, и на
    /// программе из сотни функций это сотни строк ни о чём. `distinct` в кеш не
    /// идёт: он затем и написан, чтобы копии различались.
    seen: HashMap<String, String>,
    /// Именованные метаданные: имя и список ссылок.
    named: Vec<(String, Vec<String>)>,
}

impl Metadata {
    /// Заводит узел и отдаёт ссылку на него.
    fn node(&mut self, text: &str) -> String {
        if let Some(known) = self.seen.get(text) {
            return known.clone();
        }
        let at = self.nodes.len();
        self.nodes.push(text.to_owned());
        let reference = format!("!{at}");
        if !text.starts_with("distinct ") {
            self.seen.insert(text.to_owned(), reference.clone());
        }
        reference
    }

    /// Заводит именованный список: `!имя = !{...}`.
    fn name(&mut self, name: &str, refs: Vec<String>) {
        self.named.push((name.to_owned(), refs));
    }

    /// Печатает всё: сперва именованные, потом нумерованные.
    fn print(&self, out: &mut String) {
        for (name, refs) in &self.named {
            let _ = writeln!(out, "!{name} = !{{{}}}", refs.join(", "));
        }
        for (at, node) in self.nodes.iter().enumerate() {
            let _ = writeln!(out, "!{at} = {node}");
        }
    }
}

/// Общие узлы DWARF: файл, единица трансляции, пустой список.
///
/// Заводится ровно тогда, когда у программы назван исходник
/// ([`Program::source`](crate::ir::Program::source)). Нет исходника - нет и
/// отладочной информации, а выход байт в байт тот, что был до трека E.
///
/// `DW_LANG_C99`, а не `DW_LANG_Haskell` или свой код: язык в DWARF выбирает,
/// **каким синтаксисом отладчик разбирает выражения**, и на C-режиме `print x`
/// работает как ожидается. Кода Adamas в DWARF нет, а Haskell-режим включил бы
/// чужие правила печати. Цена названа: имя Adamas, не являющееся идентификатором
/// C (`f'`), отладчику придётся квотировать.
#[derive(Debug)]
struct Dwarf {
    /// Ссылка на `!DIFile`.
    file: String,
    /// Ссылка на `!DICompileUnit`.
    unit: String,
}

impl Dwarf {
    /// Заводит шапку DWARF: флаги модуля, файл, единицу трансляции.
    fn new(metadata: &mut Metadata, source: &Source) -> Self {
        let empty = metadata.node("!{}");
        let file = metadata.node(&format!(
            "!DIFile(filename: \"{}\", directory: \"{}\")",
            source.file, source.directory
        ));
        let unit = metadata.node(&format!(
            "distinct !DICompileUnit(language: DW_LANG_C99, file: {file}, \
             producer: \"adamas\", isOptimized: false, runtimeVersion: 0, \
             emissionKind: FullDebug, enums: {empty})"
        ));
        // Обе версии обязательны, и вторая - не украшение: без «Debug Info
        // Version» verifier выбрасывает метаданные целиком, и `.ll` собирается
        // молча без DWARF. Пятая версия читается и восемнадцатой, и двадцать
        // первой - проверено прогоном, а не таблицей совместимости.
        let dwarf_version = metadata.node("!{i32 7, !\"Dwarf Version\", i32 5}");
        let info_version = metadata.node("!{i32 2, !\"Debug Info Version\", i32 3}");
        metadata.name("llvm.dbg.cu", vec![unit.clone()]);
        metadata.name("llvm.module.flags", vec![dwarf_version, info_version]);
        Self { file, unit }
    }

    /// Тип DWARF под представление слота.
    ///
    /// Имя берётся у **Adamas** (§4.11), а не у машинного типа: `UInt64`, а не
    /// `i64`. Ради этого трек и заведён - отладчик показывает типы языка, а не
    /// типы бэкенда. Знаковость и плавучесть несёт кодировка, ширину - размер.
    ///
    /// `DW_ATE_float` у плавающего - **не** `DW_ATE_signed` с той же шириной:
    /// кодировкой отладчик решает, как читать биты, и спутай её - `1.0`
    /// показалось бы числом `4607182418800017408`.
    fn ty(metadata: &mut Metadata, repr: Repr) -> String {
        match repr.primitive() {
            Some(prim) => {
                let encoding = if prim.floating() {
                    "DW_ATE_float"
                } else if prim.signed() {
                    "DW_ATE_signed"
                } else {
                    "DW_ATE_unsigned"
                };
                metadata.node(&format!(
                    "!DIBasicType(name: \"{}\", size: {}, encoding: {encoding})",
                    prim.name(),
                    prim.size() * 8
                ))
            }
            // Объект кучи: своего имени у него в IR нет - представление знает
            // только, что это указатель. Показать «указатель» честнее, чем
            // выдумать имя типа, которого представление не несёт.
            None => metadata.node(
                "!DIDerivedType(tag: DW_TAG_pointer_type, name: \"объект\", \
                 baseType: null, size: 64)",
            ),
        }
    }

    /// Заводит `!DISubprogram` функции и её локацию тела.
    ///
    /// `linkageName` **не пишется**, и это измерено: с ним gdb показывает в
    /// кадре `fn_3`, без него - имя Adamas. Ради имени трек и существует, а
    /// связь с символом отладчик всё равно берёт по адресам.
    fn subprogram(
        &self,
        metadata: &mut Metadata,
        function: &Function,
        at: Location,
        signature: &[String],
    ) -> Scope {
        let types = metadata.node(&format!("!{{{}}}", signature.join(", ")));
        let subroutine = metadata.node(&format!("!DISubroutineType(types: {types})"));
        let subprogram = metadata.node(&format!(
            "distinct !DISubprogram(name: \"{}\", scope: {}, file: {}, line: {}, \
             type: {subroutine}, scopeLine: {}, \
             spFlags: DISPFlagDefinition | DISPFlagLocalToUnit, unit: {})",
            escaped_name(&function.name),
            self.file,
            self.file,
            at.line,
            at.line,
            self.unit
        ));
        let here = metadata.node(&format!(
            "!DILocation(line: {}, column: {}, scope: {subprogram})",
            at.line, at.column
        ));
        // Строка нуль - «код написан не человеком», и она здесь не заглушка, а
        // требование: `llc` ставит `prologue_end` на первую инструкцию с
        // ненулевой строкой, и без нулевого пролога точка останова вставала бы
        // **до** записи параметра в кадр. Измерено сеансом: параметр печатался
        // нулём вместо своего значения.
        let prologue = metadata.node(&format!("!DILocation(line: 0, scope: {subprogram})"));
        Scope {
            subprogram,
            here,
            prologue,
            at,
        }
    }
}

/// Отладочная подпись одной функции.
#[derive(Clone, Debug)]
struct Scope {
    /// Ссылка на `!DISubprogram`.
    subprogram: String,
    /// Локация тела: строка определения.
    here: String,
    /// Локация пролога: строка нуль.
    prologue: String,
    /// Где определение написано - им же датируются локальные переменные.
    at: Location,
}

/// Имя в кавычках метаданных: обратный слеш и кавычка экранируются.
fn escaped_name(name: &str) -> String {
    name.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Модуль целиком.
#[derive(Debug, Default)]
struct Module {
    /// Тела функций.
    bodies: String,
    /// Узлы метаданных модуля.
    metadata: Metadata,
    /// Шапка DWARF. `None` - исходника у программы нет.
    dwarf: Option<Dwarf>,
}

impl Module {
    /// Эмитит одну функцию.
    fn function(&mut self, program: &Program, function: &Function) -> Result<(), LlvmError> {
        if function.form == Form::Detached {
            return Err(LlvmError::Detached {
                function: function.name.clone(),
            });
        }
        if let Some(binding) = function.captured.first() {
            return Err(LlvmError::Shape {
                function: function.name.clone(),
                place: format!("захват `{}`", binding.name),
                shape: "среда замыкания".to_owned(),
            });
        }
        let result = slot_or(function, "ответ", function.result)?;

        let mut parameters = Vec::new();
        for binding in function.live_parameters() {
            let ty = slot_or(
                function,
                &format!("параметр `{}`", binding.name),
                binding.fact.repr,
            )?;
            let attributes = parameter_attributes(&binding.fact);
            let spaced = if attributes.is_empty() {
                String::new()
            } else {
                format!("{attributes} ")
            };
            parameters.push(format!("{ty} {spaced}%v{}", binding.local.0));
        }

        // Подпись функции для DWARF собирается **до** тела: `!DISubprogram`
        // обязан существовать раньше, чем на него сошлётся первая локация.
        let scope = match (&self.dwarf, function.position) {
            (Some(dwarf), Some(at)) => {
                let mut signature = vec![Dwarf::ty(&mut self.metadata, function.result)];
                signature.extend(
                    function
                        .live_parameters()
                        .map(|binding| Dwarf::ty(&mut self.metadata, binding.fact.repr)),
                );
                Some(dwarf.subprogram(&mut self.metadata, function, at, &signature))
            }
            _ => None,
        };

        let mut builder = Builder::new(
            program,
            function,
            result,
            &mut self.metadata,
            self.dwarf.as_ref(),
            scope.clone(),
        );
        builder.parameters_in_frame(function);
        // Тело стоит в **возвратной** позиции целиком, и обход её разносит:
        // хвостовой вызов печатается `musttail`, всё прочее - `ret`. Печатает
        // `ret` сам обход, потому что у разбора в хвосте их столько, сколько
        // ветвей (трек D).
        builder.tail(&function.body)?;

        let signed = scope.map_or_else(String::new, |scope| format!(" !dbg {}", scope.subprogram));
        let _ = writeln!(self.bodies, "; {}", function.name);
        let _ = writeln!(
            self.bodies,
            "define internal {CONVENTION} {result} @fn_{}({}) {DEFINITION_ATTRIBUTES}{signed} {{",
            function.id.0,
            parameters.join(", ")
        );
        self.bodies.push_str("entry:\n");
        self.bodies.push_str(&builder.head);
        self.bodies.push_str(&builder.body);
        self.bodies.push_str("}\n\n");
        Ok(())
    }

    /// Складывает модуль: шапка, объявления, константы, тела, метаданные.
    fn finish(self, program: &Program, answer: Answer) -> String {
        let mut out = String::new();
        out.push_str(concat!(
            "; Порождено понижением Adamas. Править нечего: правится тот, кто\n",
            "; породил. Договор с рантаймом - `adamas.h`.\n",
            ";\n",
            "; Подмножество IR консервативное (`emit_llvm.rs`): ни `nsw`/`nuw` у\n",
            "; арифметики, ни `inbounds`/`nuw` у `getelementptr`, ни строк цели -\n",
            "; её берёт `llc` у хоста. Проверяется прогоном на минимальной\n",
            "; версии, а не грепом.\n",
            "\n",
            "; Рантайм: те же точки входа, что зовёт C-бэкенд. Куча целиком за\n",
            "; ним; слот объекта читает и пишет сам IR (`emit_llvm.rs`).\n",
            "declare ptr @adamas_con0(i16)\n",
            "declare ptr @adamas_alloc(i16, i64)\n",
            "declare ptr @adamas_reuse(ptr, i16, i64)\n",
            "declare void @adamas_free(ptr)\n",
            "declare i16 @adamas_tag(ptr)\n",
            "declare i32 @adamas_is_unique(ptr)\n",
            "declare ptr @adamas_dup(ptr)\n",
            "declare void @adamas_drop(ptr, ptr)\n",
            "declare ptr @adamas_drop_reuse(ptr, ptr)\n",
            "declare void @adamas_fail(ptr) noreturn\n",
        ));
        // Дроп детей живёт в спутнике: таблица конструкторов, по которой он
        // идёт, - та же, по которой печатается ответ.
        let _ = writeln!(out, "declare void @{RELEASE_SYMBOL}(ptr)\n");

        if self.dwarf.is_some() {
            out.push_str(concat!(
                "; Отладочная информация. Вызов интринсика, а не запись\n",
                "; `#dbg_declare`: записи не читает восемнадцатая версия, а\n",
                "; вызов читают обе.\n",
                "declare void @llvm.dbg.declare(metadata, metadata, metadata)\n",
                "\n",
            ));
        }

        let _ = writeln!(
            out,
            "{TAG_MESSAGE} = private unnamed_addr constant [{} x i8] c\"{}\"\n",
            terminated(TAG_TEXT).len(),
            escaped(&terminated(TAG_TEXT))
        );

        out.push_str(&self.bodies);

        let _ = writeln!(out, "; Точка входа для спутника на C.");
        let _ = writeln!(
            out,
            "; Соглашение здесь C - её зовёт спутник; порождённые между собой\n\
             ; ходят по `{CONVENTION}` (трек D), и вызов ниже это называет."
        );
        let _ = writeln!(
            out,
            "define {} @{ENTRY_SYMBOL}() {DEFINITION_ATTRIBUTES} {{",
            answer.machine()
        );
        out.push_str("entry:\n");
        let _ = writeln!(
            out,
            "  %answer = call {CONVENTION} {} @fn_{}()",
            answer.machine(),
            program.entry.0
        );
        let _ = writeln!(out, "  ret {} %answer", answer.machine());
        out.push_str("}\n");

        if !self.metadata.nodes.is_empty() {
            out.push('\n');
            self.metadata.print(&mut out);
        }
        out
    }
}

/// Текст обрыва по неизвестному тегу.
const TAG_TEXT: &str = "разбор не знает конструктора";

/// Байты строки с завершающим нулём.
fn terminated(text: &str) -> Vec<u8> {
    let mut bytes = text.as_bytes().to_vec();
    bytes.push(0);
    bytes
}

/// Байты строковой константы в форме `.ll`.
///
/// Экранируется всё, кроме печатной латиницы и пробела: русский текст занимает
/// два байта на букву, и печатать их сырыми значило бы полагаться на кодировку
/// файла там, где `.ll` объявлен байтовым.
fn escaped(bytes: &[u8]) -> String {
    let mut out = String::new();
    for byte in bytes {
        if *byte == b' ' || (byte.is_ascii_graphic() && *byte != b'"' && *byte != b'\\') {
            out.push(char::from(*byte));
        } else {
            let _ = write!(out, "\\{byte:02X}");
        }
    }
    out
}

/// Тип регистра, в который представление ложится. `None` - не ложится.
///
/// Указательных два - [`Repr::Boxed`] и [`Repr::Record`]: в рантайме это один и
/// тот же объект с заголовком, а различие форм живёт в понижении (`ir.rs`,
/// [`Repr::pointer`]). Резумпция сюда **не** входит, хотя указатель тот же: у
/// неё свой дроп с ручкой стека (§3.4), и взять её сюда значило бы дропать её
/// как данные.
fn slot(repr: Repr) -> Option<&'static str> {
    match repr {
        Repr::Boxed | Repr::Record(_) => Some("ptr"),
        other => other.primitive().map(machine),
    }
}

/// Он же с названным отказом.
fn slot_or(function: &Function, place: &str, repr: Repr) -> Result<&'static str, LlvmError> {
    slot(repr).ok_or_else(|| LlvmError::Shape {
        function: function.name.clone(),
        place: place.to_owned(),
        shape: describe(repr),
    })
}

/// Состояние эмиссии одного тела.
struct Builder<'a> {
    program: &'a Program,
    function: &'a Function,
    /// Тип регистра, в котором функция отдаёт ответ.
    ///
    /// Нужен обходу хвостовой позиции: `ret` печатает он, а не вызывающий, и
    /// печатей этих у разбора столько, сколько ветвей.
    result: &'static str,
    /// Что в каком связывании лежит: от этого тип регистра.
    reprs: HashMap<LocalId, Repr>,
    /// Связывания, чьё производство уникально ([`Unique::Certain`], трек B).
    ///
    /// Заполняет его [`crate::unique`] на IR, а не эмиттер по виду выражения:
    /// факт этот межпроцедурный - параметр уникален потому, что **каждое**
    /// место вызова кладёт в позицию свежий объект, - и увидеть его из одного
    /// тела нельзя.
    certain: HashSet<LocalId>,
    /// Чем связывание представлено в тексте.
    ///
    /// Подстановка, а не своё имя на связывание: `let` в IR - дерево, значение
    /// у него единственное, и лишний регистр пришлось бы заводить инструкцией,
    /// у которой для указателя нет формы (`add ptr` не бывает).
    operands: HashMap<LocalId, String>,
    /// Начало блока `entry`: только `alloca`.
    ///
    /// Отдельно от тела, потому что ячейка кадра обязана лежать в `entry`:
    /// `alloca` в блоке разбора была бы динамической, а по динамической
    /// `llvm.dbg.declare` не даёт постоянного смещения в кадре, и отладчик
    /// показал бы переменную не там. Запись в ячейку остаётся на месте, где
    /// значение посчитано, - так же делает всякий компилятор на `-O0`.
    head: String,
    /// Текст тела: блоки в порядке печати.
    body: String,
    /// Узлы метаданных модуля: сюда идут переменные и локации.
    metadata: &'a mut Metadata,
    /// Шапка DWARF, если исходник назван.
    dwarf: Option<&'a Dwarf>,
    /// Подпись этой функции. `None` - позиции у неё нет, и DWARF ей не пишется.
    scope: Option<Scope>,
    /// Счётчик ячеек кадра, заведённых ради отладчика.
    frames: u32,
    /// Счётчик временных имён.
    temps: u32,
    /// Счётчик разборов: им нумеруются блоки.
    matches: u32,
    /// Имя блока, в который печатается инструкция.
    ///
    /// Нужно `phi`: предшественник ветви - блок, которым она **закончилась**, а
    /// не тот, которым началась, и различаются они, как только внутри ветви
    /// встал ещё один разбор.
    block: String,
}

impl<'a> Builder<'a> {
    fn new(
        program: &'a Program,
        function: &'a Function,
        result: &'static str,
        metadata: &'a mut Metadata,
        dwarf: Option<&'a Dwarf>,
        scope: Option<Scope>,
    ) -> Self {
        let mut reprs = HashMap::new();
        let mut operands = HashMap::new();
        let mut certain = HashSet::new();
        for binding in function.captured.iter().chain(&function.parameters) {
            reprs.insert(binding.local, binding.fact.repr);
            if binding.fact.unique == Unique::Certain {
                certain.insert(binding.local);
            }
        }
        // Значение получают только **дожившие** (§3.3): стёртого в рантайме нет
        // вовсе, и в сигнатуре его нет тоже. Упомяни его тело - и отказ придёт
        // названным, а не неопределённым именем в `.ll`.
        for binding in function.live_captured().chain(function.live_parameters()) {
            operands.insert(binding.local, format!("%v{}", binding.local.0));
        }
        collect(&function.body, &mut reprs, &mut certain);
        Self {
            program,
            function,
            result,
            reprs,
            certain,
            operands,
            head: String::new(),
            body: String::new(),
            metadata,
            dwarf,
            scope,
            frames: 0,
            temps: 0,
            matches: 0,
            block: "entry".to_owned(),
        }
    }

    /// Кладёт параметры в кадр, чтобы отладчик их видел.
    ///
    /// Ячейка **сверх** регистра, а не вместо него: вычисление по-прежнему идёт
    /// по `%vN`, а ячейка существует ровно ради `llvm.dbg.declare`. Переписывать
    /// тело на чтение из ячейки незачем - параметр в Adamas не переприсваивается,
    /// и записанное в прологе остаётся верным до конца.
    ///
    /// Цена названа: на `-O0` это лишняя запись в кадр на параметр. На `-O2`
    /// ячейка исчезает вместе с `mem2reg`, а вместе с ней и наблюдаемость - тот
    /// же размен, что у всякого компилятора.
    fn parameters_in_frame(&mut self, function: &Function) {
        if self.scope.is_none() {
            return;
        }
        for (at, binding) in function.live_parameters().enumerate() {
            let Some(ty) = slot(binding.fact.repr) else {
                continue;
            };
            let cell = self.frame_cell(ty);
            let prologue = self.synthetic();
            self.instruction(
                &format!("store {ty} %v{}, ptr {cell}", binding.local.0),
                prologue.clone(),
            );
            let argument = u32::try_from(at + 1).unwrap_or(u32::MAX);
            self.declare(
                &binding.name,
                binding.fact.repr,
                Some(argument),
                &cell,
                prologue,
            );
        }
    }

    /// Заводит ячейку кадра и отдаёт её имя.
    fn frame_cell(&mut self, ty: &str) -> String {
        let cell = format!("%f{}", self.frames);
        self.frames += 1;
        let _ = writeln!(self.head, "  {cell} = alloca {ty}");
        cell
    }

    /// Объявляет отладчику переменную, лежащую в названной ячейке.
    ///
    /// `llvm.dbg.declare`, а не `llvm.dbg.value`: восемнадцатая версия печатает
    /// отладочные записи вызовами интринсиков, двадцать первая - записями
    /// `#dbg_declare`, и **общий** у них ровно вызов: новая читает старую форму
    /// и поднимает её, старая новую не читает вовсе. Проверено прогоном обеих
    /// цепочек, а не таблицей совместимости.
    fn declare(&mut self, name: &str, repr: Repr, argument: Option<u32>, cell: &str, notes: Notes) {
        let (Some(dwarf), Some(scope)) = (self.dwarf, self.scope.clone()) else {
            return;
        };
        let ty = Dwarf::ty(self.metadata, repr);
        let arg = argument.map_or_else(String::new, |at| format!("arg: {at}, "));
        let variable = self.metadata.node(&format!(
            "!DILocalVariable(name: \"{}\", {arg}scope: {}, file: {}, line: {}, type: {ty})",
            escaped_name(name),
            scope.subprogram,
            dwarf.file,
            scope.at.line
        ));
        self.instruction(
            &format!(
                "call void @llvm.dbg.declare(metadata ptr {cell}, \
                 metadata {variable}, metadata !DIExpression())"
            ),
            notes,
        );
    }

    /// Кладёт связывание `let` в кадр - ради отладчика, как и параметры.
    ///
    /// Ячейка в `entry`, запись здесь: до этой записи значения ещё нет, и
    /// отладчик, остановленный раньше, покажет мусор. Так же ведёт себя всякая
    /// неинициализированная переменная на `-O0`, и врать об этом нечем.
    fn in_frame(&mut self, binding: &Binding, value: &str) {
        if self.scope.is_none() || !binding.fact.present {
            return;
        }
        let Some(ty) = slot(binding.fact.repr) else {
            return;
        };
        let cell = self.frame_cell(ty);
        self.instruction(&format!("store {ty} {value}, ptr {cell}"), self.here());
        self.declare(&binding.name, binding.fact.repr, None, &cell, self.here());
    }

    /// Локация ненаписанного кода: строка нуль. Пусто без отладочной
    /// информации.
    ///
    /// Не путать с `Builder::prologue` трека D: тот снимает узлы-приставки, а
    /// это - подпись инструкций, которых в исходнике нет.
    fn synthetic(&self) -> Notes {
        match &self.scope {
            Some(scope) => Notes::none().and("dbg", &scope.prologue),
            None => Notes::none(),
        }
    }

    /// Свежее временное имя.
    fn temp(&mut self) -> String {
        let name = format!("%t{}", self.temps);
        self.temps += 1;
        name
    }

    /// Единственная точка печати инструкции.
    ///
    /// Одна на весь эмиттер намеренно: форма суффикса метаданных живёт здесь, а
    /// не в двух десятках мест печати. Сами метаданные приходят **аргументом** -
    /// почему, сказано у [`Notes`].
    fn instruction(&mut self, text: &str, notes: Notes) {
        let _ = writeln!(self.body, "  {text}{}", notes.suffix());
    }

    /// Метаданные, которые несёт всякая инструкция тела.
    ///
    /// Сегодня это `!dbg` - строка определения. Своё дописывается поверх:
    /// `self.here().and("noalias", "!7")`.
    fn here(&self) -> Notes {
        match &self.scope {
            Some(scope) => Notes::none().and("dbg", &scope.here),
            None => Notes::none(),
        }
    }

    /// Начинает новый блок.
    fn start(&mut self, label: &str) {
        let _ = writeln!(self.body, "\n{label}:");
        label.clone_into(&mut self.block);
    }

    /// Отказ, названный этой функцией.
    fn node(&self, node: &'static str) -> LlvmError {
        LlvmError::Node {
            function: self.function.name.clone(),
            node,
        }
    }

    /// Текст, которым связывание попадает в инструкцию.
    fn operand(&self, local: LocalId) -> Result<String, LlvmError> {
        self.operands
            .get(&local)
            .cloned()
            .ok_or_else(|| self.node("связывание без значения"))
    }

    /// Представление значения выражения.
    fn shape(&self, expr: &Expr) -> Repr {
        match expr {
            Expr::Local(local) => self.reprs.get(local).copied().unwrap_or(Repr::Boxed),
            Expr::Literal { ty, .. } | Expr::Primitive { ty, .. } => Repr::Flat(*ty),
            Expr::Call { function, .. } => self.program.functions[function.0].result,
            Expr::Bind { body, .. }
            | Expr::Dup { body, .. }
            | Expr::Drop { body, .. }
            | Expr::Reclaim { body, .. } => self.shape(body),
            Expr::Match { arms, .. } => arms
                .first()
                .map_or(Repr::Boxed, |arm| self.shape(&arm.body)),
            // Ответ сравнения - конструктор `Bool` (§4.3): аргументы плоские,
            // ответ указательный. Ответ конструктора указателен по построению -
            // и объект, и форма записи в рантайме одно и то же. Прочее срез
            // отвергает, и представление его здесь не спрашивается.
            _ => Repr::Boxed,
        }
    }

    /// Тип регистра, в котором лежит значение выражения.
    fn typed(&self, expr: &Expr) -> Result<&'static str, LlvmError> {
        let repr = self.shape(expr);
        slot(repr).ok_or_else(|| LlvmError::Shape {
            function: self.function.name.clone(),
            place: "промежуточное значение".to_owned(),
            shape: describe(repr),
        })
    }

    /// Печатает узлы-приставки до упора и отдаёт то, что под ними.
    ///
    /// Приставка - `let`, `dup` и `drop`: узел печатает голову и передаёт
    /// позицию телу. Одна печать на **обе** позиции намеренно: разъедься они -
    /// хвостовой путь потерял бы счётчик молча, а расхождение вылезло бы
    /// течью, а не отказом.
    ///
    /// Отсюда же и то, что хвост считается контекстом, а не полем узла: дроп,
    /// вставленный Perceus **после** вызова, попадает в `value` и хвоста не
    /// получает; вставленный до - остаётся здесь, и хвост уезжает дальше в
    /// тело. Ни одного признака в представлении для этого не нужно.
    ///
    /// Цикл, а не рекурсия: цепочка `let` в понижении бывает длинной, и
    /// рекурсия по ней клала бы стек компилятора на ровном месте.
    fn prologue<'e>(&mut self, expr: &'e Expr) -> Result<&'e Expr, LlvmError> {
        let mut at = expr;
        loop {
            match at {
                Expr::Bind {
                    binding,
                    value,
                    body,
                } => {
                    let computed = self.value(value)?;
                    let _ = writeln!(self.body, "  ; {computed} - {}", binding.name);
                    self.in_frame(binding, &computed);
                    self.operands.insert(binding.local, computed);
                    at = body;
                }
                Expr::Dup { local, body } => {
                    let value = self.operand(*local)?;
                    let name = self.temp();
                    self.instruction(
                        &format!("{name} = call ptr @adamas_dup(ptr {value})"),
                        self.here(),
                    );
                    at = body;
                }
                Expr::Drop {
                    local,
                    salvage,
                    body,
                } => {
                    self.dropped(*local, salvage, None)?;
                    at = body;
                }
                Expr::Reclaim {
                    local,
                    token,
                    salvage,
                    body,
                } => {
                    self.dropped(*local, salvage, Some(*token))?;
                    at = body;
                }
                other => return Ok(other),
            }
        }
    }

    /// Эмитит выражение в **возвратной** позиции: блок кончается `ret`.
    ///
    /// Хвостовой вызов печатается `musttail` с `ret` следом - этого и требует
    /// LLVM, - а разбор раздаёт возвратную позицию своим ветвям, вместо того
    /// чтобы сводить их `phi` (трек D). `ret` печатает поэтому обход, а не
    /// вызывающий: у разбора их столько, сколько ветвей.
    fn tail(&mut self, expr: &Expr) -> Result<(), LlvmError> {
        let expr = self.prologue(expr)?;
        match expr {
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis_tail(scrutinee, arms),
            Expr::Call {
                function,
                arguments,
            } => {
                // `musttail` требует, чтобы `ret` вернул **значение вызова**, а
                // значит чтобы типы сошлись. У нашего понижения они сходятся по
                // построению - ответ функции и есть ответ хвостового вызова, -
                // но полагаться на это нечем: разойдись они, verifier отверг бы
                // модуль целиком. Обычный вызов в этом случае честнее отказа.
                let agreed = slot(self.program.functions[function.0].result)
                    .is_some_and(|it| it == self.result);
                let sort = if agreed { Tail::Must } else { Tail::Plain };
                let name = self.call(*function, arguments, sort)?;
                let result = self.result;
                self.instruction(&format!("ret {result} {name}"), self.here());
                Ok(())
            }
            other => {
                let value = self.value(other)?;
                let result = self.result;
                self.instruction(&format!("ret {result} {value}"), self.here());
                Ok(())
            }
        }
    }

    /// Эмитит выражение и отдаёт операнд, в котором лежит его значение.
    fn value(&mut self, expr: &Expr) -> Result<String, LlvmError> {
        let expr = self.prologue(expr)?;
        match expr {
            Expr::Local(local) => self.operand(*local),
            Expr::Literal { ty, bits } => Ok(constant(*ty, *bits)),
            Expr::Primitive {
                op,
                ty,
                left,
                right,
            } => self.arithmetic(*op, *ty, left, right),
            Expr::Compare {
                op,
                ty,
                left,
                right,
                yes,
                no,
            } => self.comparison(*op, *ty, left, right, (yes.0, no.0)),
            Expr::Call {
                function,
                arguments,
            } => self.call(*function, arguments, Tail::Plain),
            // Приставки сняты `prologue` выше, и досюда узел не
            // доезжает. Ветвь стоит ради исчерпывающего разбора: пропади она,
            // новый узел-приставка ушёл бы в тихий отказ вместо ошибки сборки.
            Expr::Bind { .. } | Expr::Dup { .. } | Expr::Drop { .. } | Expr::Reclaim { .. } => {
                Err(self.node("узел-приставка после снятия приставок"))
            }
            Expr::Match {
                scrutinee, arms, ..
            } => self.analysis(scrutinee, arms),
            Expr::Erased => Err(self.node("стёртая позиция значением")),
            Expr::Construct {
                constructor,
                reuse,
                arguments,
            } => self.construct(*constructor, *reuse, arguments),
            Expr::ConstructClosure { .. } => Err(self.node("конструктор значением")),
            Expr::Closure { .. } | Expr::Apply { .. } => Err(self.node("замыкание")),
            Expr::Pack { .. } | Expr::Unpack { .. } => Err(self.node("плотный агрегат")),
            Expr::Layout { .. } | Expr::LayoutField { .. } => Err(self.node("дескриптор укладки")),
            Expr::ArrayNew { .. } | Expr::ArraySet { .. } | Expr::ArrayIndex { .. } => {
                Err(self.node("массив"))
            }
            Expr::RegionNew
            | Expr::RegionAlloc { .. }
            | Expr::RegionLast { .. }
            | Expr::RegionRead { .. }
            | Expr::RegionWrite { .. }
            | Expr::RegionRecycle { .. }
            | Expr::RegionPop { .. } => Err(self.node("регион")),
            Expr::Handle { .. } | Expr::Perform { .. } | Expr::Mask { .. } => {
                Err(self.node("эффект"))
            }
            Expr::Resume { .. } => Err(self.node("резумпция")),
            Expr::Closing { .. } => Err(self.node("выход из scope с ресурсом")),
            Expr::Nursery { .. } | Expr::Fiber { .. } | Expr::Cancel { .. } => {
                Err(self.node("питомник"))
            }
        }
    }

    /// Арифметика: `add`/`sub`/`mul` у целого, `fadd`/`fsub`/`fmul` у
    /// плавающего - и ни у тех, ни у других **ни одного флага**.
    ///
    /// У целых отсутствие флагов - не забывчивость: §4.3 требует
    /// **заворачивания**, то есть определённого поведения, а `nsw`/`nuw`
    /// объявили бы переполнение невозможным и отдали бы его оптимизатору как
    /// `poison`.
    ///
    /// У плавающих отсутствие флагов - и есть строгий режим §4.3, и это
    /// **измерение, разошедшееся с постановкой** (замер 2026-09-15, LLVM 18.1.8
    /// и 21.1.8). Постановка трека F говорила «флаги на инструкциях запрещают
    /// контракцию»; в LLVM всё наоборот - флаг `contract` её **разрешает**, а
    /// запрещает его отсутствие. Проверено прямо: `fmul`+`fadd` без флагов при
    /// `llc -mattr=+fma` дают `vmulsd`+`vaddsd`, те же с `contract` -
    /// `vfmadd213sd`. Быстрая математика (`fast`, `reassoc`, `nsz`, `ninf`,
    /// `nnan`, `afn`, `arcp`) не эмитится по той же причине, что `nsw`:
    /// §4.3 не даёт `Float` кольца, и переписывать компилятору нечем.
    ///
    /// **Граница обещания названа и закреплена прогоном** (`tests/float.rs`):
    /// `llc -fp-contract=fast` контрактит и IR без флагов, потому что ключ
    /// сильнее их отсутствия. Ключ этот подаёт конвейер, а конвейер наш
    /// ([`llvm::Pipeline`](crate::llvm::Pipeline)), - поэтому обещание держится
    /// на всяком ключе, который подаём мы, и перестаёт держаться у того, кто
    /// возьмёт промежуточный `.ll` и соберёт его сам.
    ///
    /// Второй вариант - `llvm.experimental.constrained.*` - **не отвергнут по
    /// цене, потому что цены у него на сегодняшнем срезе не нашлось.** Замер
    /// 2026-09-15 на том же свидетеле: обе версии LLVM его разбирают, `opt -O2`
    /// сворачивает константы и делает CSE и в нём тоже, инлайнинг и
    /// `tailrecurse` идут теми же, а `llc -O2 -mattr=+fma` печатает **те же 77
    /// инструкций**. Покупает он при этом больше: `-fp-contract=fast` его не
    /// берёт (ноль слитых против двух). Взят всё-таки простой вариант, и доводы
    /// у этого два, оба не про цену: имя `experimental` в самом IR против
    /// правила консервативного подмножества, и вектор - трек H, которому
    /// векторизация нужна, а через непрозрачный вызов она не идёт. Второе не
    /// измерено: векторизуемого плавающего цикла в срезе пока нет. Развилка
    /// живая, и решать её на данных трека H дешевле, чем сейчас.
    fn arithmetic(
        &mut self,
        op: PrimOp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
    ) -> Result<String, LlvmError> {
        let opcode = match (op, ty.floating()) {
            (PrimOp::Add, false) => "add",
            (PrimOp::Sub, false) => "sub",
            (PrimOp::Mul, false) => "mul",
            (PrimOp::Add, true) => "fadd",
            (PrimOp::Sub, true) => "fsub",
            (PrimOp::Mul, true) => "fmul",
        };
        let left = self.value(left)?;
        let right = self.value(right)?;
        Ok(self.binary(opcode, "", machine(ty), &left, &right))
    }

    /// Двуместная инструкция.
    ///
    /// `flags` - поле между кодом операции и типом: предикат у `icmp`, флаги
    /// быстрой математики у плавающего. Пусто у всего, что эмитит этот срез,
    /// кроме предиката, - см. [`Self::arithmetic`].
    fn binary(&mut self, opcode: &str, flags: &str, ty: &str, left: &str, right: &str) -> String {
        let spaced = if flags.is_empty() {
            String::new()
        } else {
            format!("{flags} ")
        };
        let name = self.temp();
        self.instruction(
            &format!("{name} = {opcode} {spaced}{ty} {left}, {right}"),
            self.here(),
        );
        name
    }

    /// Сравнение: `icmp` по ключу порядка, затем нульарный конструктор `Bool`
    /// (§4.3).
    ///
    /// Тег выбирается `select`'ом, а значение строит **рантайм**
    /// (`adamas_con0`): непосредственное представление принадлежит ему, и
    /// вторая его запись здесь разъехалась бы с первой молча.
    ///
    /// **`fcmp` не эмитится ни в каком виде.** §4.3 наделяет `Eq`/`Ord` у
    /// `Float` семантикой IEEE-754 `totalOrder`, а не IEEE-сравнения, и
    /// расходятся они ровно в двух точках: `nan == nan` истинно, `0.0 /= -0.0`.
    /// Возьми эмиттер `fcmp olt` - и договор вычислителей разошёлся бы именно
    /// там, потому что C-сторона (`adamas_order_*` в `flat.c`) и машина
    /// (`PrimTy::key` в ядре) считают ключ. Знаковость у плавающих отсюда не
    /// спрашивается вовсе: ключ сравнивается **беззнаково** у всех десяти
    /// типов, а знаковый предикат берут только знаковые целые.
    fn comparison(
        &mut self,
        op: PrimCmp,
        ty: PrimTy,
        left: &Expr,
        right: &Expr,
        verdict: (u16, u16),
    ) -> Result<String, LlvmError> {
        let predicate = match (op, ty.signed()) {
            (PrimCmp::Eq, _) => "eq",
            (PrimCmp::Ne, _) => "ne",
            (PrimCmp::Lt, true) => "slt",
            (PrimCmp::Lt, false) => "ult",
            (PrimCmp::Le, true) => "sle",
            (PrimCmp::Le, false) => "ule",
            (PrimCmp::Gt, true) => "sgt",
            (PrimCmp::Gt, false) => "ugt",
            (PrimCmp::Ge, true) => "sge",
            (PrimCmp::Ge, false) => "uge",
        };
        let left = self.value(left)?;
        let right = self.value(right)?;
        let (left, right) = if ty.floating() {
            (self.key(ty, &left), self.key(ty, &right))
        } else {
            (left, right)
        };
        let verdicted = self.binary("icmp", predicate, word(ty), &left, &right);
        let (yes, no) = verdict;
        let tag = self.temp();
        self.instruction(
            &format!("{tag} = select i1 {verdicted}, i16 {yes}, i16 {no}"),
            self.here(),
        );
        let name = self.temp();
        self.instruction(
            &format!("{name} = call ptr @adamas_con0(i16 {tag})"),
            self.here(),
        );
        Ok(name)
    }

    /// Ключ `totalOrder` у плавающего (§4.3): беззнаковый порядок ключей и есть
    /// порядок значений.
    ///
    /// Три инструкции без ветвления, и они **дословно** то же преобразование,
    /// что `adamas_order_*` в `flat.c` и `PrimTy::key` в ядре: у отрицательного
    /// биты инвертируются целиком, у неотрицательного ставится старший разряд.
    /// Отсюда `-0.0 < 0.0`, `nan == nan`, и NaN упорядочены знаком и полезной
    /// нагрузкой.
    ///
    /// Записано маской, а не `select`: `ashr` на ширину минус один даёт либо
    /// все единицы, либо ноль, `or` со старшим разрядом достраивает маску до
    /// нужной, и `xor` применяет её. Три те же значения при любом входе, без
    /// ветви и без обращения к памяти.
    fn key(&mut self, ty: PrimTy, value: &str) -> String {
        let word = word(ty);
        let last = ty.size() * 8 - 1;
        let top = 1u64 << last;
        let bits = self.temp();
        self.instruction(
            &format!("{bits} = bitcast {} {value} to {word}", machine(ty)),
            self.here(),
        );
        let sign = self.binary("ashr", "", word, &bits, &last.to_string());
        let mask = self.binary("or", "", word, &sign, &top.to_string());
        self.binary("xor", "", word, &bits, &mask)
    }

    /// Адрес слота: заголовок плюс номер слота на его ширину.
    ///
    /// `getelementptr i8` без `inbounds` и без `nuw` - правило консервативного
    /// подмножества. Разбор 18.1.8 ломает ровно `nuw` (перемерено 2026-09-15,
    /// см. шапку модуля); `inbounds` она читает, но причины ставить его,
    /// предъявимой числом, нет.
    ///
    /// Байтовый шаг, а не `getelementptr ptr`: слот носит и указатель, и биты
    /// числа в целом слове, а смещение у обоих одно (`flat.c`). Считать его
    /// типом элемента значило бы завести два разных GEP там, где адрес один.
    fn slot_pointer(&mut self, object: &str, slot: u32) -> String {
        let offset = HEADER_BYTES + slot * SLOT_BYTES;
        let name = self.temp();
        self.instruction(
            &format!("{name} = getelementptr i8, ptr {object}, i64 {offset}"),
            self.here(),
        );
        name
    }

    /// Пишет слот: плоское - битами в целое слово, ссылка - собой.
    ///
    /// Расширение беззнаковое, потому что таким его считает `adamas_word_*`
    /// (`flat.c`): биты типа берутся как есть и доливаются нулями. Читающая
    /// сторона - и здесь, и в печати - слово обрезает, поэтому верх не наблюдаем;
    /// но разойтись с C-бэкендом в **записанных байтах** незачем.
    fn store_slot(&mut self, object: &str, slot: u32, repr: Repr, value: &str) {
        let address = self.slot_pointer(object, slot);
        match repr.primitive() {
            Some(ty) => {
                let word = self.widen(ty, value);
                self.instruction(&format!("store i64 {word}, ptr {address}"), self.here());
            }
            None => {
                self.instruction(&format!("store ptr {value}, ptr {address}"), self.here());
            }
        }
    }

    /// Читает слот: обратная сторона [`Builder::store_slot`].
    fn load_slot(&mut self, object: &str, slot: u32, repr: Repr) -> String {
        let address = self.slot_pointer(object, slot);
        if let Some(ty) = repr.primitive() {
            let word = self.temp();
            self.instruction(&format!("{word} = load i64, ptr {address}"), self.here());
            return self.narrow(ty, &word);
        }
        let name = self.temp();
        self.instruction(&format!("{name} = load ptr, ptr {address}"), self.here());
        name
    }

    /// Плоское значение в слово слота.
    ///
    /// Плавающее сперва **переливается** в целое своей ширины ([`word`]), и это
    /// не украшение: `zext` от `float` LLVM отвергает разбором, а перелив через
    /// `bitcast` есть ровно то, что делает `adamas_word_Float32` в `flat.c` -
    /// `memcpy` в `uint32_t` и расширение. Расхождение здесь было бы не
    /// отказом, а другими байтами в слоте.
    fn widen(&mut self, ty: PrimTy, value: &str) -> String {
        let mut current = value.to_owned();
        if ty.floating() {
            let bits = self.temp();
            self.instruction(
                &format!("{bits} = bitcast {} {current} to {}", machine(ty), word(ty)),
                self.here(),
            );
            current = bits;
        }
        if ty.size() * 8 == 64 {
            return current;
        }
        let name = self.temp();
        self.instruction(
            &format!("{name} = zext {} {current} to i64", word(ty)),
            self.here(),
        );
        name
    }

    /// Слово слота обратно в плоское значение.
    fn narrow(&mut self, ty: PrimTy, slot: &str) -> String {
        let mut current = slot.to_owned();
        if ty.size() * 8 != 64 {
            let cut = self.temp();
            self.instruction(
                &format!("{cut} = trunc i64 {current} to {}", word(ty)),
                self.here(),
            );
            current = cut;
        }
        if !ty.floating() {
            return current;
        }
        let name = self.temp();
        self.instruction(
            &format!("{name} = bitcast {} {current} to {}", word(ty), machine(ty)),
            self.here(),
        );
        name
    }

    /// Объект конструктора: сперва аргументы, потом блок, потом слоты.
    ///
    /// Порядок тот же, что у C-бэкенда ([`crate::emit_c`]), и он не косметика:
    /// аргумент вправе сам аллоцировать, и посчитай его после `adamas_alloc` -
    /// счётчик выданных блоков разошёлся бы между двумя бэкендами при том же
    /// ответе.
    ///
    /// Придержанная ячейка (§5.1) занимает место `adamas_alloc`: `adamas_reuse`
    /// её переписывает, а на пустой аллоцирует сам - решается это в рантайме,
    /// потому что уникальность разобранного известна только там.
    fn construct(
        &mut self,
        constructor: CtorId,
        reuse: Option<LocalId>,
        arguments: &[Expr],
    ) -> Result<String, LlvmError> {
        let described = self.program.constructors[usize::from(constructor.0)].clone();
        let slots = described.slots();
        if slots == 0 {
            // Нульарный непосредствен: блока под него не выдаётся вовсе, и это
            // видно счётчиком (`main.c` печатает выданные и живые).
            let name = self.temp();
            self.instruction(
                &format!(
                    "{name} = call ptr @adamas_con0(i16 {}) ; {}",
                    constructor.0, described.name
                ),
                self.here(),
            );
            return Ok(name);
        }
        let given = self.given(&described, arguments)?;
        let object = self.temp();
        match reuse {
            Some(token) => {
                let block = self.operand(token)?;
                self.instruction(
                    &format!(
                        "{object} = call ptr @adamas_reuse(ptr {block}, i16 {}, i64 {slots}) ; {}",
                        constructor.0, described.name
                    ),
                    self.here(),
                );
            }
            None => {
                self.instruction(
                    &format!(
                        "{object} = call ptr @adamas_alloc(i16 {}, i64 {slots}) ; {}",
                        constructor.0, described.name
                    ),
                    self.here(),
                );
            }
        }
        for (slot, (argument, repr)) in given.into_iter().zip(described.slot_reprs()).enumerate() {
            let at = u32::try_from(slot).unwrap_or(u32::MAX);
            self.store_slot(&object, at, repr, &argument);
        }
        Ok(object)
    }

    /// Аргументы дожившим связываниям конструктора, в порядке слотов.
    fn given(
        &mut self,
        described: &Constructor,
        arguments: &[Expr],
    ) -> Result<Vec<String>, LlvmError> {
        let present: Vec<usize> = described
            .binders
            .iter()
            .enumerate()
            .filter(|(_, fact)| fact.present)
            .map(|(position, _)| position)
            .collect();
        let mut given = Vec::new();
        for position in present {
            let Some(argument) = arguments.get(position) else {
                continue;
            };
            given.push(self.value(argument)?);
        }
        Ok(given)
    }

    /// Отданная ссылка: [`Expr::Drop`] и [`Expr::Reclaim`] одной печатью.
    ///
    /// Различаются они одним - достаётся ли блок `token`, - и в схлопнутой
    /// форме тем же одним. Печатать их порознь значило бы завести четыре места,
    /// где стоит имя дропа детей.
    fn dropped(
        &mut self,
        local: LocalId,
        salvage: &Salvage,
        token: Option<LocalId>,
    ) -> Result<(), LlvmError> {
        if salvage.collapses() {
            return self.salvaged(local, salvage, token);
        }
        let value = self.operand(local)?;
        match token {
            Some(token) => {
                let name = self.temp();
                self.instruction(
                    &format!(
                        "{name} = call ptr @adamas_drop_reuse(ptr {value}, ptr @{RELEASE_SYMBOL})"
                    ),
                    self.here(),
                );
                self.operands.insert(token, name);
            }
            None => self.instruction(
                &format!("call void @adamas_drop(ptr {value}, ptr @{RELEASE_SYMBOL})"),
                self.here(),
            ),
        }
        Ok(())
    }

    /// Дроп разобранного, схлопнутый с `dup` его полей (§5.1, [`Salvage`]).
    ///
    /// Форма та же, что у C-бэкенда, и различает ветви та же уникальность в
    /// рантайме (`adamas_is_unique`, §10 вопрос 149): у уникального взятые поля
    /// достаются ветви даром, невзятые дропаются здесь, блок либо освобождается,
    /// либо достаётся `token`; у разделённого берётся ссылка на каждое взятое,
    /// счётчик родителя идёт вниз, придержать нечего.
    ///
    /// Ветвление здесь, а не `select`: у ветвей разные **побочные действия**, и
    /// посчитать обе значило бы дропнуть невзятые поля разделённого родителя,
    /// который их держит.
    fn salvaged(
        &mut self,
        local: LocalId,
        salvage: &Salvage,
        token: Option<LocalId>,
    ) -> Result<(), LlvmError> {
        if self.certain.contains(&local) {
            return self.salvaged_unique(local, salvage, token);
        }
        let value = self.operand(local)?;
        let at = self.matches;
        self.matches += 1;
        let unique = format!("s{at}.unique");
        let shared = format!("s{at}.shared");
        let join = format!("s{at}.join");

        let answer = self.temp();
        self.instruction(
            &format!("{answer} = call i32 @adamas_is_unique(ptr {value})"),
            self.here(),
        );
        let verdict = self.temp();
        self.instruction(&format!("{verdict} = icmp ne i32 {answer}, 0"), self.here());
        self.instruction(
            &format!("br i1 {verdict}, label %{unique}, label %{shared}"),
            self.here(),
        );

        self.start(&unique);
        for field in &salvage.spare {
            let spare = self.operand(*field)?;
            self.instruction(
                &format!("call void @adamas_drop(ptr {spare}, ptr @{RELEASE_SYMBOL})"),
                self.here(),
            );
        }
        if token.is_none() {
            self.instruction(&format!("call void @adamas_free(ptr {value})"), self.here());
        }
        let from_unique = self.block.clone();
        self.instruction(&format!("br label %{join}"), self.here());

        self.start(&shared);
        for field in &salvage.taken {
            let named = self.operand(*field)?;
            let name = self.temp();
            self.instruction(
                &format!("{name} = call ptr @adamas_dup(ptr {named})"),
                self.here(),
            );
        }
        self.instruction(
            &format!("call void @adamas_drop(ptr {value}, ptr @{RELEASE_SYMBOL})"),
            self.here(),
        );
        let from_shared = self.block.clone();
        self.instruction(&format!("br label %{join}"), self.here());

        self.start(&join);
        if let Some(token) = token {
            let name = self.temp();
            self.instruction(
                &format!("{name} = phi ptr [ {value}, %{from_unique} ], [ null, %{from_shared} ]"),
                self.here(),
            );
            self.operands.insert(token, name);
        }
        Ok(())
    }

    /// Тот же дроп, когда уникальность известна статически ([`crate::unique`]).
    ///
    /// Печатается **одна** ветвь из двух - та, которую взял бы рантайм, - и
    /// вопроса `adamas_is_unique` не остаётся вовсе. Экономия не в одном вызове:
    /// уходят `dup` каждого взятого поля, `adamas_drop` родителя, два блока,
    /// ветвление и `phi` придержанной ячейки.
    ///
    /// Довод законности - у [`crate::unique`], и он проверяем: `rc` поднимает
    /// только `adamas_dup`, а его на это связывание в программе нет. Довод
    /// неверный виден **прогоном**: `tests/alias.rs` объявляет уникальным
    /// разделённое и получает другой ответ.
    fn salvaged_unique(
        &mut self,
        local: LocalId,
        salvage: &Salvage,
        token: Option<LocalId>,
    ) -> Result<(), LlvmError> {
        let value = self.operand(local)?;
        for field in &salvage.spare {
            let spare = self.operand(*field)?;
            self.instruction(
                &format!("call void @adamas_drop(ptr {spare}, ptr @{RELEASE_SYMBOL})"),
                self.here(),
            );
        }
        match token {
            // Блок достаётся придержавшему: `phi` не нужен, второго исхода нет.
            Some(token) => {
                self.operands.insert(token, value);
            }
            None => self.instruction(&format!("call void @adamas_free(ptr {value})"), self.here()),
        }
        Ok(())
    }

    /// Прямой вызов: стёртые позиции в вызов не идут.
    ///
    /// `sort` - шов трека D: [`Tail::Must`] печатает `musttail`, и следом за
    /// такой инструкцией обязан идти `ret` - его ставит [`Self::tail`].
    /// Соглашение [`CONVENTION`] печатается **всегда**, и не для красоты: оно
    /// объявлено у определения, и вызов, не назвавший его, звал бы по другому.
    fn call(
        &mut self,
        function: FuncId,
        arguments: &[Expr],
        sort: Tail,
    ) -> Result<String, LlvmError> {
        let called = &self.program.functions[function.0];
        if called.form == Form::Detached {
            return Err(LlvmError::Detached {
                function: called.name.clone(),
            });
        }
        let result = slot(called.result).ok_or_else(|| LlvmError::Shape {
            function: self.function.name.clone(),
            place: format!("ответ `{}`", called.name),
            shape: describe(called.result),
        })?;
        let present: Vec<usize> = called
            .parameters
            .iter()
            .enumerate()
            .filter(|(_, binding)| binding.fact.present)
            .map(|(position, _)| position)
            .collect();
        let mut given = Vec::new();
        for position in present {
            let Some(argument) = arguments.get(position) else {
                continue;
            };
            let ty = self.typed(argument)?;
            let operand = self.value(argument)?;
            given.push(format!("{ty} {operand}"));
        }
        let name = self.temp();
        self.instruction(
            &format!(
                "{name} = {}call {CONVENTION} {result} @fn_{}({})",
                sort.prefix(),
                function.0,
                given.join(", ")
            ),
            self.here(),
        );
        Ok(name)
    }

    /// Голова разбора: тег, `switch` и блок обрыва.
    ///
    /// Разбираемое **заимствуется**: поля читаются по нему, а отдаёт его сама
    /// ветвь - [`Expr::Drop`] либо [`Expr::Reclaim`] внутри неё
    /// (`perceus::arm`). Владения поля не заводят: ссылку на нужное берёт
    /// `Dup`, поставленный тем же проходом, а ненужное не читается вовсе.
    /// Нульарный конструктор непосредствен, и тег у него - он сам.
    ///
    /// Одна на обе позиции намеренно: разъедься головы - хвостовой разбор
    /// поехал бы по другому тегу, и заметить это было бы нечем. Отдаёт
    /// разбираемое, номер разбора и метки ветвей; ветви печатает вызывающий,
    /// потому что позиция у них его. Разбираемое ему нужно затем же, зачем и
    /// голове: по нему читаются поля.
    fn dispatch(
        &mut self,
        scrutinee: &Expr,
        arms: &[Arm],
    ) -> Result<(String, u32, Vec<String>), LlvmError> {
        if arms.is_empty() {
            return Err(self.node("разбор пустого типа"));
        }

        let scrutinised = self.value(scrutinee)?;
        let at = self.matches;
        self.matches += 1;
        let tag = self.temp();
        self.instruction(
            &format!("{tag} = call i16 @adamas_tag(ptr {scrutinised})"),
            self.here(),
        );

        let labels: Vec<String> = (0..arms.len()).map(|it| format!("m{at}.a{it}")).collect();
        let fail = format!("m{at}.fail");
        let cases: Vec<String> = arms
            .iter()
            .zip(&labels)
            .map(|(arm, label)| format!("i16 {}, label %{label}", arm.constructor.0))
            .collect();
        self.instruction(
            &format!("switch i16 {tag}, label %{fail} [ {} ]", cases.join(" ")),
            self.here(),
        );

        self.start(&fail);
        self.instruction(
            &format!("call void @adamas_fail(ptr {TAG_MESSAGE})"),
            self.here(),
        );
        self.instruction("unreachable", self.here());
        Ok((scrutinised, at, labels))
    }

    /// Разбор значением: ветви сводятся `phi` в блоке стыковки.
    fn analysis(&mut self, scrutinee: &Expr, arms: &[Arm]) -> Result<String, LlvmError> {
        let (scrutinised, at, labels) = self.dispatch(scrutinee, arms)?;
        let answer = self.typed(&arms[0].body)?;
        let join = format!("m{at}.join");

        let mut incoming = Vec::new();
        for (arm, label) in arms.iter().zip(&labels) {
            self.start(label);
            self.bind_fields(&scrutinised, arm);
            let value = self.value(&arm.body)?;
            // Предшественник - блок, которым ветвь **закончилась**: вложенный
            // разбор внутри неё сменил бы его.
            incoming.push(format!("[ {value}, %{} ]", self.block));
            self.instruction(&format!("br label %{join}"), self.here());
        }

        self.start(&join);
        let name = self.temp();
        self.instruction(
            &format!("{name} = phi {answer} {}", incoming.join(", ")),
            self.here(),
        );
        Ok(name)
    }

    /// Разбор в хвостовой позиции: ветвь возвращает сама, `phi` не строится.
    ///
    /// Так и снимается препятствие трека D. `musttail` требует `ret` **в том же
    /// блоке**, а ветвь, кончающаяся `br label %join`, его не даёт; блока
    /// стыковки здесь нет вовсе, и хвост уезжает в каждую ветвь целым.
    fn analysis_tail(&mut self, scrutinee: &Expr, arms: &[Arm]) -> Result<(), LlvmError> {
        let (scrutinised, _, labels) = self.dispatch(scrutinee, arms)?;
        for (arm, label) in arms.iter().zip(&labels) {
            self.start(label);
            self.bind_fields(&scrutinised, arm);
            self.tail(&arm.body)?;
        }
        Ok(())
    }

    /// Поля ветви: слот у каждого свой, стёртое слота не занимает.
    ///
    /// Номер слота спрашивается у [`Constructor::slot`], а не считается здесь
    /// заново: стёртые связывания в объекте отсутствуют, и вторая арифметика
    /// нумерации разошлась бы с первой на первом же стёртом поле - молча и с
    /// перепутанными значениями, а не отказом.
    fn bind_fields(&mut self, object: &str, arm: &Arm) {
        let described = self.program.constructors[usize::from(arm.constructor.0)].clone();
        let params = described.params as usize;
        for (position, binding) in arm.fields.iter().enumerate() {
            let Some(slot) = described.slot(params + position) else {
                continue;
            };
            let taken = self.load_slot(object, slot, binding.fact.repr);
            let _ = writeln!(self.body, "  ; {taken} - {}", binding.name);
            self.operands.insert(binding.local, taken);
        }
    }
}

/// Представления связываний, заведённых телом, и уникальность их производства.
///
/// Оба сразу, а не двумя обходами: собираются они из одного и того же
/// [`Fact`], и второй обход разошёлся бы с первым молча - ровно тот жанр
/// дефекта, ради которого [`Expr::children`] живёт одной штукой.
fn collect(expr: &Expr, found: &mut HashMap<LocalId, Repr>, certain: &mut HashSet<LocalId>) {
    let mut note = |binding: &Binding| {
        found.insert(binding.local, binding.fact.repr);
        if binding.fact.unique == Unique::Certain {
            certain.insert(binding.local);
        }
    };
    match expr {
        Expr::Bind { binding, .. } => note(binding),
        Expr::Match { arms, .. } => {
            for arm in arms {
                for field in &arm.fields {
                    note(field);
                }
            }
        }
        Expr::Reclaim { token, .. } => {
            // Придержанный блок - сырая ячейка, представление у неё одно.
            found.insert(*token, Repr::Boxed);
        }
        _ => {}
    }
    for child in expr.children() {
        collect(child, found, certain);
    }
}

/// Спутник на C: таблица конструкторов, печать, дроп детей и точка входа.
///
/// `flat.c`, `print.c`, `release.c` и `main.c` берутся **дословно** теми же
/// `include_str!`, какими их берёт C-бэкенд, и над той же таблицей: печать и
/// дроп у двух бэкендов обязаны быть одними, иначе «печатает то же» держалось
/// бы на совпадении двух печатей, а не на их тождестве.
fn support(program: &Program, answer: Answer) -> String {
    let mut out = String::new();
    out.push_str(concat!(
        "/* Порождено понижением Adamas: спутник `.ll`.\n",
        " *\n",
        " * Программу считает `.ll` целиком; здесь только таблица конструкторов,\n",
        " * печать ответа, дроп его детей и точка входа. `flat.c`, `print.c`,\n",
        " * `release.c` и `main.c` - те же файлы, что собирает C-бэкенд, взятые\n",
        " * дословно.\n",
        " */\n",
        "\n",
        "#include \"adamas.h\"\n",
        "\n",
        "#include <stdio.h>\n",
        "\n",
    ));
    out.push_str(crate::emit_c::FLAT);
    out.push('\n');
    crate::emit_c::table(&mut out, program);
    out.push_str(crate::emit_c::RELEASE);
    out.push('\n');
    out.push_str(crate::emit_c::PRINTER);
    out.push('\n');

    // Раскладка объекта записана дважды - здесь и в `emit_llvm.rs`, - потому
    // что слот `.ll` читает инструкцией. Расхождение обязано ронять **сборку**,
    // а не ответ: числа подставлены отсюда, а не написаны в файле руками.
    out.push_str(concat!(
        "/* Раскладка объекта: те же числа, по которым `.ll` считает адрес\n",
        " * слота. Разъедься они с рантаймом - не соберётся спутник. */\n"
    ));
    let _ = writeln!(
        out,
        "_Static_assert(offsetof(adamas_object, fields) == {HEADER_BYTES}u, \
         \"заголовок объекта разошёлся с `emit_llvm.rs`\");"
    );
    let _ = writeln!(
        out,
        "_Static_assert(sizeof(adamas_value) == {SLOT_BYTES}u, \
         \"слот объекта разошёлся с `emit_llvm.rs`\");\n"
    );

    out.push_str(concat!(
        "/* Дроп детей, видимый из `.ll`: тот же `adamas_release_value`, только\n",
        " * не `static` - порождённый IR лежит в другой единице трансляции. */\n"
    ));
    let _ = writeln!(
        out,
        "void {RELEASE_SYMBOL}(adamas_value value) {{ adamas_release_value(value); }}\n"
    );

    out.push_str("/* Ответ считает `.ll`, печатает `main.c` ниже. */\n");
    match answer {
        Answer::Flat(ty) => {
            let ctype = crate::emit_c::scalar(Repr::Flat(ty));
            let _ = writeln!(out, "{ctype} {ENTRY_SYMBOL}(void);");
            let _ = writeln!(out, "#define ADAMAS_ENTRY {ENTRY_SYMBOL}");
            let _ = writeln!(out, "#define ADAMAS_ANSWER_FLAT adamas_word_{}", ty.name());
            let _ = writeln!(out, "#define ADAMAS_ANSWER_TYPE {ctype}");
            let _ = writeln!(
                out,
                "#define ADAMAS_ANSWER_KIND {}u",
                crate::emit_c::kind(ty)
            );
        }
        // Без `ADAMAS_ANSWER_FLAT`: `main.c` разводит две формы ответа
        // препроцессором, и объектная - его же вторая ветка, с печатью по
        // таблице и дропом после.
        Answer::Boxed => {
            let _ = writeln!(out, "adamas_value {ENTRY_SYMBOL}(void);");
            let _ = writeln!(out, "#define ADAMAS_ENTRY {ENTRY_SYMBOL}");
        }
    }
    out.push('\n');
    out.push_str(crate::emit_c::ENTRY);
    out
}

#[cfg(test)]
mod tests {
    use adamas_core::prim::PrimTy;

    use super::{constant, widened};

    /// Сколько младших бит расширения обязаны быть нулевыми.
    ///
    /// Двадцать девять - разница ширин мантисс, и на неё смотрит сам `llvm-as`:
    /// шестнадцатеричная константа типа `float` принимается только тогда, когда
    /// сужение обратно точно.
    const TAIL: u64 = (1 << 29) - 1;

    #[test]
    fn a_double_is_written_by_its_bits() {
        assert_eq!(
            constant(PrimTy::Float64, 1.0f64.to_bits()),
            "0x3FF0000000000000"
        );
        assert_eq!(
            constant(PrimTy::Float64, (-0.0f64).to_bits()),
            "0x8000000000000000"
        );
        assert_eq!(
            constant(PrimTy::Float32, u64::from(1.0f32.to_bits())),
            "0x3FF0000000000000"
        );
    }

    /// Расширение любого `float` оставляет хвост нулевым.
    ///
    /// Перебор идёт умножением на нечётное: оно биекция на `u32`, поэтому
    /// шестьдесят пять тысяч шагов раскладываются по всему диапазону, а не
    /// толпятся у нуля, где живут одни субнормали.
    #[test]
    fn widening_a_single_leaves_the_tail_clear() {
        for step in 0..=0xffffu32 {
            let bits = step.wrapping_mul(65_537);
            assert_eq!(
                widened(u64::from(bits)) & TAIL,
                0,
                "хвост не нулевой у {bits:#010x}"
            );
        }
    }

    /// NaN переносится вместе со знаком и полезной нагрузкой.
    ///
    /// Ветвь эта программой не достигается - литерала NaN в языке нет, - и
    /// стоит она потому, что приведение железом квитирует сигнальный NaN, то
    /// есть меняет ровно те биты, которые §4.3 обещает сохранить.
    #[test]
    fn a_single_nan_keeps_its_sign_and_payload() {
        assert_eq!(widened(0x7fc0_0001), 0x7ff8_0000_2000_0000);
        let signalling = (1u64 << 63) | (0x7ffu64 << 52) | (0x0020_0003u64 << 29);
        assert_eq!(widened(0xffa0_0003), signalling);
        assert_eq!(widened(0xffa0_0003) & TAIL, 0);
    }
}

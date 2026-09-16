//! Вектор - инструкцией, а не надеждой (§4.9, трек H Фазы 7).
//!
//! Трек H про **выразимость**: план говорит, что «ради vector types LLVM всё
//! это и затевалось; на C-бэкенде разрыв здесь и так около нуля». Критерий,
//! стало быть, - что программы на `Simd` пишутся, считаются и сходятся с
//! машиной, а не что они быстрее. Первые три проверяет корпус
//! (`simd-lanes`, `simd-wrapping` в `agreement.rs` и `llvm.rs`).
//!
//! Здесь проверяется то, чего корпус проверить не может по построению:
//! **векторность**. Ответ её не показывает - поэлементный цикл даёт то же
//! число, - поэтому свидетель смотрит на инструкции дизассемблером.
//!
//! # Наивный свидетель не работает, и это измерено
//!
//! Первая редакция считала пакетные инструкции в штатном выходе (`opt -O2`,
//! `llc -O2`) и **не убивала мутанта**. Мутант - понижение `simdAdd`/`simdMul`
//! поэлементно: `extractelement`, скалярная операция, `insertelement` обратно,
//! то есть ровно то, от чего §4.9 отговаривает. Замер 2026-09-16 на [`KERNEL`],
//! LLVM 21.1.8, хост x86-64:
//!
//! | что понижает эмиттер | конвейер | пакетных | скалярных | всего | ответ |
//! |---|---|---|---|---|---|
//! | вектор (штатно) | `-O2` | 4 | 0 | 51 | 2.0 |
//! | поэлементно (мутант) | `-O2` | **4** | **0** | 51 | 2.0 |
//! | вектор (штатно) | без `opt`, `llc -O0` | **4** | **0** | 110 | 2.0 |
//! | поэлементно (мутант) | без `opt`, `llc -O0` | **0** | **16** | 150 | 2.0 |
//!
//! Верхние две строки совпадают дословно: SLP-векторизатор `opt -O2` собирает
//! вектор обратно из восьми скалярных операций, и отличить эмиттер от мутанта
//! в штатном выходе **нечем**. Нижние две расходятся полностью.
//!
//! Отсюда два следствия, и оба названы, а не спрятаны.
//!
//! *Свидетель меряет на неоптимизированном конвейере* ([`Pipeline::plain`]), и
//! это не слабее, а точнее: вопрос трека - «что печатает эмиттер», а не «что
//! умеет `opt`». На штатном конвейере вопрос не задаётся вовсе, потому что
//! ответ на него один при обоих понижениях.
//!
//! *Что §4.9 покупает на LLVM-пути для element-wise ядра - это **гарантия**, а
//! не инструкции.* Инструкции оптимизатор нашёл бы сам на этом ядре. Гарантия
//! же не зависит ни от порогов SLP, ни от формы цикла, ни от уровня
//! оптимизации: `fmul <8 x float>` написан в IR, и разобрать его иначе нельзя.
//! Разница эта - ровно та, ради которой §2.1 п.6 требует механизм в языке, а не
//! надежду на бэкенд; числом она здесь названа, а не заявлена.

mod harness;

use std::path::Path;
use std::process::Command;

use adamas_codegen::llvm::{Pipeline, Toolchain};

/// Векторное ядро §4.9 дословно: `x := x·gain + bias` над `Simd 8 Float32`.
///
/// Ширина восемь - та самая, которую §4.9 называет в разборе про геометрию:
/// «внутренний цикл работает с `Simd 8 Float32` над колонкой». На baseline
/// x86-64 (SSE2, без `-mattr`) она ложится в **два** регистра XMM, поэтому
/// пакетных инструкций на витке четыре, а не две.
///
/// # Виток настоящий, и это требование свидетеля
///
/// Программа без цикла свернулась бы константой раньше, чем дошла до
/// кодогенерации, - ровно так первая редакция свидетеля трека F потеряла
/// контракцию (`tests/float.rs`). Здесь виток даёт 4096 оборотов: полностью
/// развернуть его `opt` не станет (порог развёртки на два порядка ниже), а
/// свернуть в замкнутую форму не сможет - строгий режим §4.3 не даёт
/// переассоциации плавающего.
///
/// `gain` равен половине, поэтому колонка сходится к неподвижной точке `2.0`.
/// **Ответ этого ядра свидетелем не является и быть не может**: у сходящегося
/// прохода он перестаёт зависеть и от заполнения, и от числа витков - замерено
/// 2026-09-16, перестановка дорожек даёт те же `2.0`. Наблюдаемое здесь -
/// инструкции; различимость дорожек показывает корпусная фикстура, у которой
/// витка нет и ответ от заполнения зависит.
///
/// Вектор в аргументе рекурсивного вызова назван `let`-связыванием с
/// **написанным** типом. Это обход дефекта, к `Simd` отношения не имеющего:
/// тип члена объявляемой группы в сигнатуре ещё не стоит (§10 вопрос 50),
/// поэтому аргумент рекурсивного вызова типизируется дыркой, и разрешение
/// инстанса не находит `Primitive ?a`. Тот же узор с `Flat` и `regionAlloc`
/// отказывает дословно так же - проверено 2026-09-16, - см. отчёт трека H.
const KERNEL: &str = "\
data Bool where
  True : Bool
  False : Bool

type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

turns : UInt64
turns = 4096

zero : Float32
zero = 0.0

one : Float32
one = 1.0

four : Float32
four = 4.0

gain : Float32
gain = 0.5

seeded : Simd 8 Float32
seeded = simdSet (simdSet (simdSplat 8 zero) 0 one) 7 four

step : UInt64 -> Simd 8 Float32 -> Simd 8 Float32
step 0 acc = acc
step n acc =
  let next : Simd 8 Float32 = simdAdd (simdMul acc (simdSplat 8 gain)) (simdSplat 8 one)
  step (subUInt64 n 1) next

main : Float32
main = simdLane (step turns seeded) 7
";

/// Строка заполнения корпусной фикстуры `simd-lanes`, как она там написана.
///
/// Свидетель перестановки берёт **корпусную** программу, а не [`KERNEL`], и
/// довод измеренный: у ядра с `gain` меньше единицы есть неподвижная точка, и
/// за четыре тысячи витков колонка сходится к ней - ответ перестаёт зависеть от
/// заполнения вовсе (замер 2026-09-16: `2.0` при обоих заполнениях). Тот же
/// довод записан в шапке `workload-column`, и здесь он подтвердился ещё раз.
///
/// Корпусная фикстура витка не имеет, зато её свёртка чередует знак, поэтому
/// перестановка любых двух дорожек видна ответом. Заодно свидетель тем самым
/// стоит на программе, которую **договор трёх вычислителей** уже держит.
const SEEDED: &str =
    "  simdSet (simdSet (simdSet (simdSet (simdSplat 4 zero) 0 one) 1 two) 2 four) 3 eight";

/// Она же с переставленными дорожками 0 и 1.
const SWAPPED: &str =
    "  simdSet (simdSet (simdSet (simdSet (simdSplat 4 zero) 1 one) 0 two) 2 four) 3 eight";

/// Сколько пакетных и сколько скалярных плавающих инструкций в объектнике.
///
/// Мнемоники перечислены по архитектурам, а неизвестная - **отказ**, а не
/// пропуск: свидетель, молча считающий ноль там, где инструкций не узнал, есть
/// обманчивый свидетель худшего рода. Двух архитектур довольно: CI ходит на
/// x86-64 Linux и на macOS, где LLVM объявлен отсутствующим и сюда не доходит.
fn packed_and_scalar(tools: &Toolchain, object: &Path) -> (usize, usize) {
    let shown = Command::new(tools.tool("llvm-objdump"))
        .arg("-d")
        .arg(object)
        .output()
        .unwrap_or_else(|error| panic!("дизассемблер не запустился: {error}"));
    assert!(
        shown.status.success(),
        "`{}` не дизассемблировался",
        object.display()
    );
    let text = String::from_utf8_lossy(&shown.stdout);
    let (packed, scalar): (&[&str], &[&str]) = if cfg!(target_arch = "x86_64") {
        (&["mulps", "addps", "mulpd", "addpd"], &["mulss", "addss"])
    } else if cfg!(target_arch = "aarch64") {
        // У ARM64 форму несёт операнд: `fmul v0.4s` пакетная, `fmul s0` нет.
        (&["fmul\tv", "fadd\tv"], &["fmul\ts", "fadd\ts"])
    } else {
        panic!(
            "мнемоник этой архитектуры свидетель не знает: посчитать ноль \
             значило бы соврать - допишите её в `packed_and_scalar`"
        );
    };
    let count = |needles: &[&str]| {
        text.lines()
            .filter(|line| needles.iter().any(|it| line.contains(it)))
            .count()
    };
    (count(packed), count(scalar))
}

/// Эмиттер печатает **векторную** инструкцию, а не восемь скалярных.
///
/// Мерится на неоптимизированном конвейере, и почему - в шапке модуля: на
/// штатном `opt -O2` мутант «поэлементно» неотличим от эмиттера, потому что
/// SLP собирает вектор обратно.
///
/// Утверждений два, и второе несущее. Пакетных обязано быть **больше нуля** -
/// иначе вектора нет вовсе. Скалярных плавающих обязано быть **ровно ноль** -
/// иначе часть дорожек поехала по скалярному пути, а ответ этого не покажет.
#[test]
fn the_emitter_prints_a_vector_instruction_not_eight_scalar_ones() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("simd-kernel", KERNEL)
        .unwrap_or_else(|error| panic!("ядро не понизилось: {error}"));
    assert!(
        artefacts.ll.contains("fmul <8 x float>") && artefacts.ll.contains("fadd <8 x float>"),
        "в IR нет векторной арифметики - дизассемблировать нечего"
    );
    let object = harness::llvm_object("simd-kernel.plain", &artefacts, &tools, &Pipeline::plain());
    let (packed, scalar) = packed_and_scalar(&tools, &object);
    assert!(
        packed > 0,
        "пакетных инструкций ноль: вектор до объектника не доехал"
    );
    assert_eq!(
        scalar, 0,
        "скалярных плавающих {scalar}: часть дорожек поехала скаляром, \
         а ответ этого не покажет"
    );

    // Проверка номера дорожки на литеральном номере обязана **исчезнуть**:
    // `Builder::lane_in_range` эмитит её всегда, а стоить она должна ноль.
    // Обрыва в штатном выходе поэтому не остаётся ни одного, и ветки тоже.
    let optimised = harness::llvm_object(
        "simd-kernel.opt",
        &artefacts,
        &tools,
        &Pipeline::optimised(),
    );
    let (fast, fast_scalar) = packed_and_scalar(&tools, &optimised);
    let total = harness::instructions(&tools, &optimised);
    assert!(
        fast > 0 && fast_scalar == 0,
        "после `-O2` вектор пропал: пакетных {fast}, скалярных {fast_scalar}"
    );
    eprintln!(
        "LLVM без `opt`: пакетных {packed}, скалярных {scalar}; \
         с `-O2`: пакетных {fast}, инструкций всего {total}"
    );
}

/// То же на C-бэкенде: `vector_size` доезжает до пакетной инструкции.
///
/// §4.9 разрешает non-LLVM бэкендам «эквивалентные intrinsics либо scalar
/// fallback», и взято первое. Проверяется это тем же дизассемблером и на том же
/// уровне оптимизации, на каком проверяется LLVM-путь: `-O0`, потому что
/// векторизатор gcc собрал бы вектор и из скалярного цикла.
///
/// Скалярные плавающие здесь **допускаются**: спутник печати и чтение дорожки
/// работают со скаляром по существу, а `-O0` их не убирает. Утверждается
/// поэтому только наличие пакетных - вопрос «вектор или цикл» решает именно
/// оно, а их отсутствие означало бы цикл.
#[test]
fn the_c_backend_reaches_a_packed_instruction_too() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let text = harness::text(KERNEL).unwrap_or_else(|error| panic!("ядро не понизилось: {error}"));
    assert!(
        text.contains("__attribute__((vector_size("),
        "в порождённом C нет векторного типа: §4.9 взят скалярным путём"
    );
    let dir = harness::scratch();
    let source = dir.join("simd-kernel.c");
    std::fs::write(&source, &text).unwrap_or_else(|error| panic!("исходник не записался: {error}"));
    let object = dir.join("simd-kernel.c.o");
    let built = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O0", "-fwrapv", "-w", "-c"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg("-o")
        .arg(&object)
        .arg(&source)
        .output()
        .unwrap_or_else(|error| panic!("компилятор C не запустился: {error}"));
    assert!(
        built.status.success(),
        "порождённый C не собрался - расширение `vector_size` этим компилятором \
         не принимается:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let (packed, _) = packed_and_scalar(&tools, &object);
    assert!(
        packed > 0,
        "пакетных инструкций ноль: `vector_size` до инструкции не доехал"
    );
    eprintln!("C при -O0: пакетных {packed}");
}

/// Перепутанные дорожки меняют ответ - на всех трёх вычислителях.
///
/// Свидетель того, что дорожки различимы. Без него «вектор работает» значило бы
/// «печатает число», а число печатает и понижение, кладущее все дорожки в одну.
///
/// Сверяются три ответа на двух программах: машина, C и LLVM. Внутри каждой
/// программы три ответа обязаны **совпасть** (договор трёх вычислителей), между
/// программами - **разойтись**.
#[test]
fn a_swapped_lane_changes_the_answer() {
    let straight = std::fs::read_to_string(harness::corpus().join("simd-lanes.adamas"))
        .unwrap_or_else(|error| panic!("корпусная фикстура не прочиталась: {error}"));
    assert_eq!(
        straight.matches(SEEDED).count(),
        1,
        "строка заполнения в `simd-lanes` встретилась не однажды: свидетель \
         подменяет не то, что думает"
    );
    let swapped = straight.replace(SEEDED, SWAPPED);

    let straight_machine = harness::printed(&straight);
    let swapped_machine = harness::printed(&swapped);
    assert_ne!(
        straight_machine, swapped_machine,
        "машина не заметила перестановки дорожек: {straight_machine}"
    );

    // C-сторона расходится **следствием**, а не отдельным утверждением:
    // `harness::agreed` роняет прогон, если C посчитал не то, что машина, а
    // машина, как только что показано, считает два разных числа. Сравнивать
    // здесь пришлось бы счётчики блоков - их `agreed` и отдаёт, - и они у обеих
    // программ одинаковы законно.
    harness::agreed("simd-straight", &straight)
        .unwrap_or_else(|error| panic!("прямая фикстура на C: {error}"));
    harness::agreed("simd-swapped", &swapped)
        .unwrap_or_else(|error| panic!("переставленная фикстура на C: {error}"));

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let straight_llvm = harness::llvm_agreed(
        "simd-straight",
        &straight,
        &tools,
        &pipeline,
        "simd.straight",
    )
    .unwrap_or_else(|error| panic!("прямая фикстура на LLVM: {error}"))
    .0;
    let swapped_llvm =
        harness::llvm_agreed("simd-swapped", &swapped, &tools, &pipeline, "simd.swapped")
            .unwrap_or_else(|error| panic!("переставленная фикстура на LLVM: {error}"))
            .0;
    assert_ne!(
        straight_llvm, swapped_llvm,
        "LLVM не заметила перестановки дорожек: {straight_llvm}"
    );
    eprintln!("прямое {straight_llvm}, переставленное {swapped_llvm}");
}

/// Минимальная поддерживаемая LLVM читает векторный IR и считает то же.
///
/// Треугольник версий у трека H **свой**, отдельно от `llvm.rs`: корпусные
/// фикстуры проходят там, но ядро несёт три формы, которых в корпусе нет, -
/// `poison` в исходном операнде splat'а, `shufflevector` нулевой маской и
/// векторный тип в **сигнатуре** функции (`tailcc <8 x float>`). Векторные типы
/// LLVM устоявшиеся, а вот `llvm.vector.*`-интринсики между мажорами двигались;
/// здесь проверяется, что ни одного из них срез не эмитит.
#[test]
fn the_minimum_llvm_reads_the_vector_kernel() {
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("simd-kernel", KERNEL)
        .unwrap_or_else(|error| panic!("ядро не понизилось: {error}"));
    assert!(
        !artefacts.ll.contains("llvm.vector."),
        "срез эмитит `llvm.vector.*`: правило консервативного подмножества \
         требует причины, а причина - число"
    );
    let pipeline = Pipeline::optimised();
    let new = harness::llvm_agreed("simd-kernel", KERNEL, &tools, &pipeline, "simd.kernel.new")
        .unwrap_or_else(|error| panic!("штатная цепочка: {error}"))
        .0;
    let old = harness::llvm_agreed(
        "simd-kernel",
        KERNEL,
        &minimum,
        &pipeline,
        "simd.kernel.old",
    )
    .unwrap_or_else(|error| panic!("минимальная цепочка: {error}"))
    .0;
    assert_eq!(new, old, "минимальная LLVM посчитала вектор не так");
}

/// Дорожкой бывает только примитив (§4.9), и отказ назван.
///
/// Это то самое ограничение, ради которого §4.9 заводит `Primitive`: «`Simd 4
/// (Ref r Packet)` - типовая ошибка, потому что `Ref` не Primitive. Реальные
/// SIMD-инструкции работают с primitive numeric layout'ом, „SIMD-вектор
/// pointer'ов“ - концептуально скалярный цикл».
///
/// **Названная граница расхождения с §4.9.** Ограничение стоит на операциях, а
/// не на кайнде `Simd`, поэтому отвергается не написание типа, а построение
/// значения. Тип, только объявленный и ни разу не построенный, проверку
/// проходит - второе утверждение здесь про это, и стоит оно затем, чтобы
/// расхождение оставалось измеренным, а не описанным.
#[test]
fn a_lane_must_be_a_primitive() {
    const BUILT: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

data Packet where
  Wrap : Int64 -> Packet

empty : Packet
empty = Wrap 0

bad : Simd 4 Packet
bad = simdSplat 4 empty

main : Int64
main = 0
";
    // Та же дорожка, но значение не строится: граница расхождения с §4.9.
    const DECLARED: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

data Packet where
  Wrap : Int64 -> Packet

type Lanes = Simd 4 Packet

main : Int64
main = 0
";
    let why = harness::rejected(BUILT);
    assert!(
        why.contains("Primitive Packet"),
        "отказ не называет класс дорожки: {why}"
    );
    assert_eq!(
        harness::printed(DECLARED),
        "0",
        "объявленный, но не построенный `Simd 4 Packet` отвергнут: расхождение \
         с §4.9 сместилось, и отчёт трека H называет не ту границу"
    );
}

/// Вектор в поле конструктора отвергается **понижением**, а не компилятором C.
///
/// Слот объекта - одно машинное слово (`adamas.h`), а `Simd 4 Float32` занимает
/// шестнадцать байт. Плоский агрегат из той же беды выходит боксированием, у
/// вектора боксированной формы нет: ни укладки в дескрипторе - `Flat` для него
/// не выводится, - ни конструктора-обёртки.
///
/// Свидетель написан по **измеренному** дефекту (2026-09-16): до отказа
/// понижение печатало `adamas_set_field(t, 0, v)` с вектором третьим
/// аргументом, и ловил это gcc - «несовместимый тип аргумента 3 функции
/// `adamas_set_field`». То есть компилятор Adamas на валидной программе
/// порождал не собирающийся код, а это отказ худшего рода: пользователь видит
/// ошибку чужого компилятора в файле, которого не писал.
///
/// Машина при этом считает такую программу как ни в чём не бывало - вектор у
/// неё спайн, и слотов у неё нет вовсе. Расхождение названное, того же жанра,
/// что `LowerError::ArrayAnswer`: два вычислителя сходятся лишь в том, что
/// понижение отвечать отказывается вслух.
#[test]
fn a_vector_does_not_fit_an_object_slot() {
    const BOXED: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

data Boxed where
  MkBoxed : Simd 4 Float32 -> Boxed

one : Float32
one = 1.0

two : Float32
two = 2.0

held : Boxed
held = MkBoxed (simdSet (simdSplat 4 one) 2 two)

taken : Boxed -> Float32
taken (MkBoxed v) = simdLane v 2

main : Float32
main = taken held
";
    assert_eq!(
        harness::printed(BOXED),
        "2.0",
        "машина перестала считать вектор в поле: расхождение не то, что описано"
    );
    let why = harness::text(BOXED).err().map_or_else(
        || panic!("вектор в поле конструктора взят понижением: слот в слово не влезает"),
        |error| error.to_string(),
    );
    assert!(
        why.contains("поле конструктора") && why.contains("Simd 4 Float32"),
        "отказ не называет ни позицию, ни вектор: {why}"
    );
}

/// Номер дорожки вне ширины обрывает прогон, и одинаково у обоих бэкендов.
///
/// Свидетель написан по **измеренному** расхождению. `extractelement` с
/// номером вне ширины отдаёт `poison`, то есть молча неверный ответ, тогда как
/// C-сторона зовёт `adamas_fail`; до правки два бэкенда на такой программе
/// расходились, а договор трёх вычислителей обещает одно значение на всех.
/// Машина третьей стороной не сводит такое чтение вовсе - `simdLane` остаётся
/// застрявшим спайном, - и сходятся все трое в том, что **ответа не даёт
/// никто**. Та же форма границы, что у выхода за длину массива (§4.11).
///
/// Номер здесь написан литералом нарочно: на нём `opt` вправе свернуть проверку
/// вместе с веткой, и свидетель показывает, что свернулось **ветвление**, а не
/// обрыв.
#[test]
fn a_lane_beyond_the_width_stops_both_backends() {
    const OUTSIDE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

one : Float32
one = 1.0

main : Float32
main = simdLane (simdSplat 4 one) 9
";
    // Машина ответа не даёт: чтение остаётся спайном, и печатается он.
    let machine = harness::printed(OUTSIDE);
    assert!(
        machine.contains("simdLane"),
        "машина свела чтение вне ширины до значения: {machine}"
    );

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("simd-outside", OUTSIDE)
        .unwrap_or_else(|error| panic!("программа не понизилась: {error}"));
    let binary = harness::llvm_binary("simd.outside", &artefacts, &tools, &Pipeline::optimised());
    let run = Command::new(&binary)
        .output()
        .unwrap_or_else(|error| panic!("прогон не запустился: {error}"));
    assert!(
        !run.status.success(),
        "LLVM ответила на дорожку вне ширины: `{}`",
        String::from_utf8_lossy(&run.stdout)
    );
    let said = String::from_utf8_lossy(&run.stderr);
    assert!(
        said.contains(adamas_codegen::ir::LANE_OUTSIDE),
        "оборвалось не тем и не там: {said}"
    );

    // C-сторона обязана оборваться **тем же** текстом. Проверяется он, а не
    // сам факт обрыва: текст один на два эмиттера по построению
    // (`ir::LANE_OUTSIDE`), и свидетель здесь стережёт как раз то, что
    // построение не разошлось с прогоном.
    let printed = harness::text(OUTSIDE).unwrap_or_else(|error| panic!("C не собрался: {error}"));
    assert!(
        printed.contains(adamas_codegen::ir::LANE_OUTSIDE),
        "порождённый C не несёт проверки номера дорожки"
    );
}

// --- окно колонки: `load`/`store` §4.9 над памятью (трек D волны 3) --------
//
// Свидетель векторности у памяти **другой**, чем у арифметики, и это измерено,
// а не предположено. Трек H поймал поэлементную арифметику счётом инструкций
// на неоптимизированном конвейере: `opt -O2` собирал вектор обратно (SLP), а
// без него мутант расходился с эмиттером дословно. У памяти правило это
// работает **наполовину**, и вторая половина названа ниже: поэлементное
// чтение по соседним `getelementptr` неотличимо от векторного даже без `opt`,
// потому что сводит его SelectionDAG, а он не пас `opt` и снять его нечем.
//
// Замер 2026-09-17 на `workload-vector`, LLVM 21.1.8, x86-64 baseline, счёт по
// телу ядра (`llc -O0`, без `opt`):
//
// | что понижает эмиттер | movups | movss |
// |---|---|---|
// | окно вектором (штатно) | **4** | **0** |
// | по дорожке через `adamas_array_at` | **2** | **8** |
// | по дорожке по соседним `getelementptr` | 4 | 0 - **не отличается** |
//
// Отсюда форма свидетеля: он ловит ту подделку, которая наблюдаема, и
// **называет** ту, которая нет. Вторая при этом и не подделка по существу:
// адрес там считает сам IR теми же байтами, и машинный код у неё честно
// векторный. Различались бы они только текстом IR, а измеряется здесь
// объектник - как того и требует правило «свидетель обязан различать».

/// Имя функции, в теле которой стоит окно: `fn_N` у порождённого `.ll`.
///
/// Ищется по тексту, а не пишется числом: номер функции зависит от порядка
/// понижения, и прибитый гвоздями `fn_8` разъехался бы с первой же правкой
/// фикстуры - молча, потому что несуществующий символ дизассемблер просто не
/// печатает, а счёт по пустому выводу даёт ноль.
fn window_symbol(ll: &str) -> String {
    let mut current = None;
    for line in ll.lines() {
        if let Some(rest) = line.strip_prefix("define ") {
            current = rest
                .split('@')
                .nth(1)
                .and_then(|tail| tail.split('(').next())
                .map(str::to_owned);
        }
        if line.contains("load <8 x float>") {
            return current.unwrap_or_else(|| panic!("загрузка окна стоит вне функции"));
        }
    }
    panic!("в порождённом IR нет загрузки окна - мерить нечего");
}

/// Сколько пакетных и сколько скалярных перемещений в теле названной функции.
///
/// Мнемоники перечислены по архитектурам, а неизвестная - **отказ**, по тому
/// же правилу, что у [`packed_and_scalar`]: свидетель, молча считающий ноль
/// там, где инструкций не узнал, обманчив.
fn window_moves(tools: &Toolchain, object: &Path, symbol: &str) -> (usize, usize) {
    let shown = Command::new(tools.tool("llvm-objdump"))
        .arg("-d")
        .arg(format!("--disassemble-symbols={symbol}"))
        .arg(object)
        .output()
        .unwrap_or_else(|error| panic!("дизассемблер не запустился: {error}"));
    assert!(shown.status.success(), "`{symbol}` не дизассемблировался");
    let text = String::from_utf8_lossy(&shown.stdout);
    assert!(
        text.contains(symbol),
        "дизассемблер не нашёл `{symbol}`: счёт по пустому выводу дал бы ноль"
    );
    let (packed, scalar): (&[&str], &[&str]) = if cfg!(target_arch = "x86_64") {
        // `movups`, а не `movaps`: окно стоит по шагу колонки, и выровненного
        // перемещения у него быть не должно. `movaps` в теле - пролог и
        // разливы регистров, к окну отношения не имеющие.
        (&["movups"], &["movss"])
    } else if cfg!(target_arch = "aarch64") {
        // У ARM64 форму несёт операнд, как и у арифметики.
        (&["ldr\tq", "str\tq"], &["ldr\ts", "str\ts"])
    } else {
        panic!(
            "мнемоник этой архитектуры свидетель не знает: посчитать ноль \
             значило бы соврать - допишите её в `window_moves`"
        );
    };
    let count = |needles: &[&str]| {
        text.lines()
            .filter(|line| needles.iter().any(|it| line.contains(it)))
            .count()
    };
    (count(packed), count(scalar))
}

/// Поэлементное понижение окна **через рантайм** - та подделка, что наблюдаема.
///
/// Восемь `adamas_array_at` вместо одного `adamas_array_window`: вызов
/// непрозрачен, и свести восемь чтений обратно в одно не вправе ни `opt`, ни
/// выбор инструкций.
fn per_lane_through_runtime(ll: &str) -> String {
    let mut out = String::new();
    let mut hit = false;
    for line in ll.lines() {
        if line
            .trim_start()
            .starts_with("%t6 = load <8 x float>, ptr ")
        {
            hit = true;
            out.push_str("  %p0 = call ptr @adamas_array_at(ptr %v0, i64 %t4)\n");
            out.push_str("  %l0 = load float, ptr %p0, align 4\n");
            out.push_str("  %w0 = insertelement <8 x float> poison, float %l0, i64 0\n");
            for lane in 1..8u32 {
                let _ = std::fmt::Write::write_fmt(
                    &mut out,
                    format_args!(
                        "  %k{lane} = add i64 %t4, {lane}\n  \
                         %p{lane} = call ptr @adamas_array_at(ptr %v0, i64 %k{lane})\n  \
                         %l{lane} = load float, ptr %p{lane}, align 4\n  \
                         %w{lane} = insertelement <8 x float> %w{}, float %l{lane}, i64 {lane}\n",
                        lane - 1
                    ),
                );
            }
            out.push_str("  %t6 = fadd <8 x float> %w7, zeroinitializer\n");
            continue;
        }
        out.push_str(line);
        out.push('\n');
    }
    assert!(
        hit,
        "мутант не нашёл загрузку окна: форма эмиттера уехала, и свидетель \
         мерил бы нетронутую программу"
    );
    out
}

/// Корпусная программа векторного ядра, как она лежит в `tests/golden/eval`.
fn vector_corpus() -> String {
    std::fs::read_to_string(harness::corpus().join("workload-vector.adamas"))
        .unwrap_or_else(|error| panic!("фикстура векторного ядра не читается: {error}"))
}

/// Окно колонки - одно векторное обращение, а не восемь скалярных (§4.9).
///
/// Свидетель несёт **свой мутант**, а не описание мутанта: проверка, которую
/// не ломали, за фазу трижды оказывалась ложной. Ломается здесь ровно то, что
/// проверяется, - форма обращения к окну, - и числа обеих половин печатаются.
#[test]
fn a_window_is_one_vector_access_not_eight_scalar_ones() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = vector_corpus();
    let mut artefacts = harness::llvm_text("window-kernel", &source)
        .unwrap_or_else(|error| panic!("векторное ядро не понизилось: {error}"));
    assert!(
        artefacts.ll.contains("load <8 x float>") && artefacts.ll.contains("store <8 x float>"),
        "в IR нет векторного обращения к окну - дизассемблировать нечего"
    );
    // Граница обещана **дорожкой**, а не типом вектора: ячейка стоит по шагу
    // колонки. `align 32` здесь был бы обещанием, которого никто не давал.
    assert!(
        artefacts.ll.contains("load <8 x float>, ptr %t5, align 4")
            && artefacts
                .ll
                .contains("store <8 x float> %t14, ptr %t16, align 4"),
        "обращение к окну обещает не ту границу: ячейка `Float32` стоит по четырём"
    );
    let symbol = window_symbol(&artefacts.ll);

    let object = harness::llvm_object("window.plain", &artefacts, &tools, &Pipeline::plain());
    let (packed, scalar) = window_moves(&tools, &object, &symbol);
    assert!(
        packed > 0,
        "пакетных перемещений ноль: окно до объектника не доехало"
    );
    assert_eq!(
        scalar, 0,
        "скалярных перемещений {scalar}: часть окна поехала по дорожке, \
         а ответ этого не покажет"
    );

    artefacts.ll = per_lane_through_runtime(&artefacts.ll);
    let mutant = harness::llvm_object("window.mutant", &artefacts, &tools, &Pipeline::plain());
    let (fake_packed, fake_scalar) = window_moves(&tools, &mutant, &symbol);
    assert!(
        fake_scalar > 0 && fake_packed < packed,
        "мутант «по дорожке через рантайм» неотличим от эмиттера: \
         пакетных {fake_packed} против {packed}, скалярных {fake_scalar} против {scalar} - \
         свидетель перестал различать"
    );
    eprintln!(
        "окно: пакетных {packed}, скалярных {scalar}; \
         по дорожке через рантайм: пакетных {fake_packed}, скалярных {fake_scalar}"
    );
}

/// Векторная колонка отвечает то же, что скалярная, - побитово.
///
/// Две **разные программы** корпуса считают одно ядро: `workload-column`
/// по ячейке, `workload-vector` окном в восемь дорожек. Element-wise проход от
/// ширины не зависит, значит числа обязаны совпасть - и совпадение это ловит
/// то, чего не ловит ни один свидетель внутри одной программы: перепутанное
/// окно, перепутанную дорожку внутри окна и потерянный хвост колонки. У каждой
/// из двух за спиной договор трёх вычислителей, так что сверяются здесь шесть
/// ответов, а не два.
#[test]
fn the_vector_column_answers_what_the_scalar_column_answers() {
    let vector = vector_corpus();
    let scalar = std::fs::read_to_string(harness::corpus().join("workload-column.adamas"))
        .unwrap_or_else(|error| panic!("скалярная фикстура не читается: {error}"));
    // Размеры у двух фикстур обязаны совпасть, иначе сравнивались бы две
    // разные работы. Проверяется это по тексту: обе несут `cells` и `passes`
    // именованными строками, и стенд подставляет в них одно и то же.
    for size in ["cells = 8", "passes = 3"] {
        assert!(
            vector.contains(size) && scalar.contains(size),
            "фикстуры разошлись размером `{size}` - сравнивались бы разные работы"
        );
    }
    let expected = harness::printed(&scalar);
    assert_eq!(
        harness::printed(&vector),
        expected,
        "машина считает вектором не то, что считает скаляром"
    );
    // `agreed` сверяет понижение с машиной сам и падает при расхождении; здесь
    // читается его **счётчик**: колонка обязана стоить один блок, сколько бы
    // окон по ней ни прошло. Перепиши `simdStore` колонку копией - и число
    // выросло бы, а ответ остался бы тем же.
    let blocks = harness::agreed("window-agrees", &vector)
        .unwrap_or_else(|error| panic!("векторная колонка не понизилась: {error}"));
    assert!(
        blocks.contains("блоков выдано 1, живо 0"),
        "векторное ядро выдало не один блок: `simdStore` перестал писать по месту ({blocks})"
    );
}

/// Окно, чей хвост вышел за колонку, обрывает прогон - у обоих бэкендов.
///
/// Граница у окна **своя**, и проверять её обязана своя точка входа:
/// `adamas_array_at` спрашивает про начало, а за конец блока уходит хвост. На
/// колонке из четырёх ячеек окно ширины четыре с номера один читало бы четыре
/// чужих байта **при верном ответе на первые три дорожки** - то есть молча.
/// Свидетель написан по этой форме дефекта, а не по факту обрыва.
///
/// Машина третьей стороной ответа тоже не даёт: `simdLoad` за длиной не
/// сводится и остаётся застрявшим спайном. Сходятся все трое в том, что
/// ответа не даёт никто, - та же форма границы, что у номера дорожки вне
/// ширины и у номера ячейки вне длины.
#[test]
fn a_window_past_the_end_stops_both_backends() {
    const OUTSIDE: &str = "\
type Layout = { size : UInt32, align : UInt32 }

class Primitive a where
  simdLayout : Layout

zero : Float32
zero = 0.0

cells : UInt64
cells = 4

column : Array cells Float32
column = arrayNew cells zero

main : Float32
main = simdLane (simdLoad 4 column 1) 0
";
    let machine = harness::printed(OUTSIDE);
    assert!(
        machine.contains("simdLoad"),
        "машина свела окно за длиной до значения: {machine}"
    );

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("window-outside", OUTSIDE)
        .unwrap_or_else(|error| panic!("программа не понизилась: {error}"));
    let binary = harness::llvm_binary("window.outside", &artefacts, &tools, &Pipeline::optimised());
    let run = Command::new(&binary)
        .output()
        .unwrap_or_else(|error| panic!("прогон не запустился: {error}"));
    assert!(
        !run.status.success(),
        "LLVM ответила на окно за длиной: `{}`",
        String::from_utf8_lossy(&run.stdout)
    );
    let said = String::from_utf8_lossy(&run.stderr);
    assert!(
        said.contains(WINDOW_OUTSIDE),
        "оборвалось не тем и не там: {said}"
    );

    // C-сторона обязана оборваться тем же текстом, и текст этот один на два
    // бэкенда потому, что живёт в рантайме: обе стороны зовут
    // `adamas_array_window`, и второй записи сообщения не существует.
    let c = harness::c_printed("window-outside-c", OUTSIDE);
    assert!(
        c.reason.contains(WINDOW_OUTSIDE),
        "C-сторона окно за длиной пропустила: `{}` / `{}`",
        c.printed,
        c.reason
    );
}

/// Текст обрыва по выходу окна за колонку - как его пишет рантайм.
///
/// Записан здесь **второй** раз (первый - `adamas-runtime/c/array.c`), и это
/// не та копия, которой стоит бояться: у обоих эмиттеров записи нет вовсе -
/// оба зовут `adamas_array_window`, - а здесь стоит ожидание свидетеля.
/// Разъехавшись, оно уронит прогон, а не пропустит его.
const WINDOW_OUTSIDE: &str = "окно вектора вне длины массива";

//! Строгий режим плавающей арифметики: §4.3 на двух бэкендах (трек F Фазы 7).
//!
//! Два обещания §4.3 проверяются здесь, и оба - **программой**, чей ответ от
//! обещания зависит.
//!
//! *Контракции нет.* `a * b + c` не сливается в `fma` ни на каком уровне
//! оптимизации и ни на одном из двух бэкендов. Свидетель - [`CONTRACTION`]: он
//! отвечает `0.0`, пока контракции нет, и `1000.0`, стоит её разрешить.
//!
//! *Порядок - `totalOrder`, а не IEEE.* Свидетель - [`ORDER`]: он считает те
//! самые значения, на которых две семантики расходятся, - NaN и знаковый ноль.
//!
//! *Вычисленный NaN - один элемент порядка* (вопрос 172). Свидетель -
//! [`NAN_SIGN`]: `clamp` от NaN, чей ответ до канонизации зависел от уровня
//! оптимизации и от того, каким сишным компилятором собрано.
//!
//! # Почему отдельным файлом
//!
//! По тому же доводу, по которому `llvm.rs` стоит рядом с `agreement.rs`, а не
//! внутри: **знаменатели разные**. Здесь мерится не «сколько корпуса берёт
//! эмиттер», а «сходятся ли два бэкенда при переборе ключей сборки», и перебор
//! этот - своя ось, которой нет ни у одного соседа. Плюс матрица: у C-стороны
//! ключи компилятора, у LLVM-стороны стадии конвейера, и общего списка у них
//! нет.
//!
//! # Обе программы написаны здесь, а не в корпусе
//!
//! Тем же доводом, каким там стоит `VERDICTS` (`llvm.rs`): корпус показывает
//! форму языка, а эти две - **границу обещания**. Половина того, что они
//! наблюдают, наблюдаема только перебором ключей, которого у корпусного прогона
//! нет.

mod harness;

use std::process::Command;

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::llvm::{Pipeline, Stage, Toolchain};

/// Свидетель контракции: `x·x - C` при `C`, равном округлённому `x·x`.
///
/// `x` есть 2²⁷+1, и квадрат его - 2⁵⁴+2²⁸+1 - в пятьдесят три бита мантиссы
/// не влезает: округление съедает ровно единицу. Отсюда два разных ответа, и
/// разница между ними **точная**, а не «в младшем разряде»:
///
/// - без контракции `x·x` округляется до `C`, разность нулевая, сумма за
///   тысячу витков - `0.0`;
/// - с контракцией `fma` вычитает `C` из **неокруглённого** произведения,
///   разность равна `1.0`, сумма - `1000.0`.
///
/// **`x` не константа, и это измеренное требование, а не украшение.** Первая
/// редакция свидетеля подставляла `x` прямо: оптимизатор свернул `x·x`, свернул
/// разность в ноль и вернул `ret double 0.0` - контракции в кодогенерации уже
/// нечего было делать, и мутант не убивал. Свёртка констант рвёт свидетеля
/// раньше, чем начинается то, ради чего он написан, и держать её надо в уме при
/// всяком замере плавающего.
///
/// Вторая редакция везла `x` витком через тождество `(x+1)-1`. Не помогло:
/// оптимизатор **отшелушил** первый виток, увидел, что дальше `x` не меняется,
/// и свернул то же самое.
///
/// Держит третья: `x = tick·0 + seed`, где `tick` - счётчик витков в плавающем.
/// `tick·0` не свёртывается в ноль без `nnan` и `nsz` - при бесконечном или
/// нечисловом `tick` ноль был бы неверен, - а этих флагов §4.3 не даёт. Значит
/// `x` непрозрачен для оптимизатора и равен `seed` на прогоне. Контракции самой
/// этой связки безразлично: `tick·0` точен, и `fma(tick, 0, seed)` даёт тот же
/// `seed`.
const CONTRACTION: &str = "\
data Bool where
  True : Bool
  False : Bool

turns : UInt64
turns = 1000

seed : Float64
seed = 134217729.0

rounded : Float64
rounded = 18014398777917440.0

step : UInt64 -> Float64 -> Float64 -> Float64
step 0 tick acc = acc
step n tick acc =
  let x : Float64 = addFloat64 (mulFloat64 tick 0.0) seed
  let piece : Float64 = subFloat64 (mulFloat64 x x) rounded
  step (subUInt64 n 1) (addFloat64 tick 1.0) (addFloat64 acc piece)

main : Float64
main = step turns 0.0 0.0
";

/// Свидетель `totalOrder`: те значения, на которых он расходится с IEEE.
///
/// Веса разрядов различны, поэтому перевёрнутый вердикт меняет сумму, а не
/// переставляет слагаемые.
///
/// Расхождений с IEEE-сравнением ровно две точки (§4.3), и обе здесь стоят.
/// **NaN**: `nan == nan` истинно, `nan <= nan` истинно, `nan /= nan` ложно - у
/// IEEE все три наоборот. **Знаковый ноль**: `-0.0 < 0.0` истинно, `-0.0 == 0.0`
/// ложно - у IEEE снова наоборот. Возьми эмиттер `fcmp` вместо ключа порядка -
/// и ответ стал бы 13032 вместо 16083.
///
/// Прочие разряды держат сам ключ, а не расхождение с IEEE: два отрицательных
/// (у них ключ убывает вместе с числом), два положительных, пара разных знаков
/// и бесконечность. Одинарная точность идёт своим набором: ключ у неё другой
/// ширины, и спутать её с двойной значило бы сравнивать не те биты.
///
/// **NaN добывается переполнением**: записать его в языке нечем - деления нет,
/// а имени `nan` лексер не знает. Наблюдается он только тем, что от знака не
/// зависит - оба NaN здесь сравниваются сами с собой, - и разряды эти
/// переживают вопрос 172 неизменными; сам знак меряет
/// [`a_computed_nan_stands_above_every_number`].
const ORDER: &str = "\
data Bool where
  True : Bool
  False : Bool

pick : Bool -> Int64 -> Int64 -> Int64
pick True yes no = yes
pick False yes no = no

weigh : Int64 -> Bool -> Int64 -> Int64
weigh acc verdict weight = addInt64 acc (pick verdict weight 0)

huge : Float64
huge = 1e300

infinite : Float64
infinite = mulFloat64 huge huge

undefined : Float64
undefined = subFloat64 infinite infinite

hugeSingle : Float32
hugeSingle = 1e30

infiniteSingle : Float32
infiniteSingle = mulFloat32 hugeSingle hugeSingle

undefinedSingle : Float32
undefinedSingle = subFloat32 infiniteSingle infiniteSingle

main : Int64
main =
  let a : Int64 = weigh 0 (eqFloat64 undefined undefined) 1
  let b : Int64 = weigh a (leFloat64 undefined undefined) 2
  let c : Int64 = weigh b (ltFloat64 undefined undefined) 4
  let d : Int64 = weigh c (neFloat64 undefined undefined) 8
  let e : Int64 = weigh d (ltFloat64 (-0.0) 0.0) 16
  let f : Int64 = weigh e (eqFloat64 (-0.0) 0.0) 32
  let g : Int64 = weigh f (ltFloat64 (-2.0) (-1.0)) 64
  let h : Int64 = weigh g (ltFloat64 1.0 2.0) 128
  let i : Int64 = weigh h (ltFloat64 infinite huge) 256
  let j : Int64 = weigh i (geFloat64 infinite 1.0) 512
  let k : Int64 = weigh j (ltFloat32 (-0.0) 0.0) 1024
  let l : Int64 = weigh k (eqFloat32 undefinedSingle undefinedSingle) 2048
  let m : Int64 = weigh l (gtFloat32 2.0 1.0) 4096
  weigh m (leFloat32 (-2.0) (-1.0)) 8192
";

/// Программа, наблюдающая **знак** вычисленного NaN: `clamp` от NaN.
///
/// Форма выбрана не минимальностью, а тем, что она встречается: `clamp x lo hi`
/// есть в каждой численной библиотеке, и написана она здесь дословно так, как
/// пишется - двумя сравнениями. Единственная особенность аргумента в том, что
/// он NaN, а NaN приходит переполнением: записать его в языке нечем - деления
/// нет, а имени `nan` лексер не знает.
///
/// До вопроса 172 эта программа отвечала **двумя разными числами** в
/// зависимости от того, чем и с каким ключом собрана (замер 2026-09-15 и
/// 2026-09-16): `-1.0` у машины, у C и у LLVM на `-O0`; `1.0` у LLVM на `-O1`
/// и выше и у минимальной LLVM 18. С gcc и clang та же развилка проходила
/// внутри одного бэкенда. Меряет её [`a_computed_nan_stands_above_every_number`].
const NAN_SIGN: &str = "\
data Bool where
  True : Bool
  False : Bool

pick : Bool -> Float64 -> Float64 -> Float64
pick True yes no = yes
pick False yes no = no

lo : Float64
lo = -1.0

hi : Float64
hi = 1.0

clamp : Float64 -> Float64
clamp x = pick (ltFloat64 x lo) lo (pick (ltFloat64 hi x) hi x)

huge : Float64
huge = 1e300

infinite : Float64
infinite = mulFloat64 huge huge

undefined : Float64
undefined = subFloat64 infinite infinite

main : Float64
main = clamp undefined
";

/// Уровни оптимизации, которые перебирают обе стороны.
///
/// Четыре, а не один: «не зависит от ключей сборки» есть утверждение, и
/// проверяется оно перебором. `-O0` стоит первым не для полноты - на нём
/// умирает половина оптимизаций, из-за которых контракция вообще возможна, и
/// совпадение с ним говорит, что ответ не приносит оптимизатор.
const LEVELS: [&str; 4] = ["-O0", "-O1", "-O2", "-O3"];

/// Ключ, которым в цель добавляется FMA.
///
/// Без него наблюдать нечего: у обобщённого `x86-64` инструкции слияния нет
/// вовсе, и контракция физически невозможна - зелёный прогон тогда доказывал бы
/// свойство **цели**, а не свойство нашего IR. Отсюда весь перебор идёт дважды:
/// с умолчальной целью и с этой.
const FMA_LLC: &str = "-mattr=+fma";

/// Он же для C.
const FMA_CC: &str = "-mfma";

/// Есть ли смысл спрашивать про FMA на этом хосте.
///
/// Ключи выше - x86-овые; на прочих архитектурах их отвергнет сам инструмент.
/// Половину матрицы это снимает, вторая (умолчальная цель, четыре уровня) идёт
/// везде.
const fn fused_available() -> bool {
    cfg!(target_arch = "x86_64")
}

/// Конвейер названного уровня с дописанными ключами `llc`.
///
/// `opt` на `-O0` не зовётся вовсе - тем же порядком, каким его не зовёт
/// [`Pipeline::plain`].
fn pipeline(level: &str, extra: &[&str]) -> Pipeline {
    let mut stages = vec![Stage::new("llvm-as", &[], "bc")];
    if level != "-O0" {
        stages.push(Stage::new("opt", &[level], "opt.bc"));
    }
    let mut keys = vec![level, "-filetype=obj", "-relocation-model=pic"];
    keys.extend_from_slice(extra);
    stages.push(Stage::new("llc", &keys, "o"));
    Pipeline { stages }
}

/// Ответ LLVM-пути: сборка, прогон, печать.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
fn through_llvm(stem: &str, source: &str, tools: &Toolchain, pipeline: &Pipeline) -> String {
    let artefacts = harness::llvm_text(stem, source).unwrap();
    harness::llvm_built(stem, &artefacts, tools, pipeline)
        .0
        .trim_end_matches('\n')
        .to_owned()
}

/// Ответ C-пути с дописанными ключами компилятора.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
fn through_c(stem: &str, source: &str, extra: &[&str]) -> String {
    let text = harness::text(source).unwrap();
    harness::built_with(stem, &text, extra)
        .0
        .trim_end_matches('\n')
        .to_owned()
}

/// Ответ машины: свидетель, с которым сверяются оба бэкенда.
fn by_machine(source: &str) -> String {
    harness::printed(source)
}

/// Контракции нет ни на одном уровне и ни на одном бэкенде.
///
/// Свидетель - машина, а не записанное руками число: то же правило, что в
/// `agreement.rs` и `llvm.rs`.
#[test]
fn contraction_does_not_happen_at_any_level_on_either_backend() {
    let expected = by_machine(CONTRACTION);
    assert_eq!(expected, "0.0", "свидетель сменил ответ: программа не та");

    let mut targets: Vec<Vec<&str>> = vec![Vec::new()];
    if fused_available() {
        targets.push(vec![FMA_CC]);
    }
    for level in LEVELS {
        for target in &targets {
            let mut keys = vec![level];
            keys.extend_from_slice(target);
            let stem = format!("contraction.c{}{}", level, target.join(""));
            let printed = through_c(&stem, CONTRACTION, &keys);
            assert_eq!(printed, expected, "C-бэкенд при {keys:?} посчитал не то");
        }
    }

    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let mut targets: Vec<Vec<&str>> = vec![Vec::new()];
    if fused_available() {
        targets.push(vec![FMA_LLC]);
    }
    for level in LEVELS {
        for target in &targets {
            let stem = format!("contraction.ll{}{}", level, target.join(""));
            let printed = through_llvm(&stem, CONTRACTION, &tools, &pipeline(level, target));
            assert_eq!(
                printed, expected,
                "LLVM при {level} {target:?} посчитал не то"
            );
        }
    }
    // Минимальная версия читает тот же IR и считает то же: правило
    // консервативного подмножества у плавающего проверяется прогоном, как и у
    // целого. Шестнадцатеричная запись констант, `bitcast` и ключ порядка -
    // формы древние, но «древние» устанавливается прогоном, а не памятью.
    let oldest = through_llvm(
        "contraction.min",
        CONTRACTION,
        &minimum,
        &pipeline("-O2", &[]),
    );
    assert_eq!(
        oldest, expected,
        "минимальная LLVM посчитала не то: плавающее вышло за консервативное подмножество"
    );
    eprintln!(
        "контракции нет: {expected} на {} уровнях, обоих бэкендах, включая минимальную LLVM",
        LEVELS.len()
    );
}

/// Мутант плана: разрешить контракцию - ответ обязан разойтись.
///
/// Разрешается она по-разному на двух сторонах, и разница эта - содержание
/// трека. У LLVM разрешает **флаг на инструкции** (`contract`), правится
/// порождённый IR. У C разрешает **ключ трансляционной единицы**
/// (`-ffp-contract=fast`), правится командная строка - самого текста программы
/// правка не касается вовсе.
///
/// Обе стороны идут с той же целью, что честный прогон: разойтись они обязаны
/// от разрешения, а не от появившейся в цели инструкции.
#[test]
fn allowing_contraction_moves_the_answer() {
    if !fused_available() {
        eprintln!("FMA в цели нет: мутант не проверялся");
        return;
    }
    let honest = by_machine(CONTRACTION);

    let fast = through_c(
        "contraction.mutant",
        CONTRACTION,
        &["-O2", FMA_CC, "-ffp-contract=fast"],
    );
    assert_ne!(
        fast, honest,
        "C с `-ffp-contract=fast` ответил то же: свидетель не о контракции"
    );
    eprintln!("мутант C `-ffp-contract=fast`: {fast} вместо {honest}");

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("contraction", CONTRACTION)
        .unwrap_or_else(|error| panic!("эмиссия отказала: {error}"));
    let mutant = contracted(&artefacts.ll);
    let printed = harness::llvm_printed(
        "contraction.contract",
        &mutant,
        &artefacts.support,
        &tools,
        &pipeline("-O2", &[FMA_LLC]),
    )
    .printed;
    assert_ne!(
        printed, honest,
        "IR с `contract` ответил то же: свидетель не о контракции"
    );
    eprintln!("мутант IR `contract`: {printed} вместо {honest}");
}

/// Граница обещания: `llc -fp-contract=fast` сильнее отсутствия флага.
///
/// Постановка трека говорила «не зависит от того, чем и с какими ключами собран
/// артефакт». Замер говорит точнее: в LLVM контракцию **разрешает** флаг
/// инструкции, а не запрещает, - и ключ конвейера, разрешающий её глобально,
/// перебивает отсутствие флага у всех инструкций разом.
///
/// Практического отличия от C это не отменяет, а сужает: у C опасность в
/// **умолчании** (clang для C берёт `on`, gcc под `-std=gnuNN` тоже), у нас - в
/// ключе, который надо написать руками и который пишет наш же конвейер. Но
/// «не зависит» - неправда, и здесь она закреплена прогоном, чтобы не
/// восстановиться молча.
#[test]
fn the_promise_stops_at_a_pipeline_key_that_allows_fusion() {
    if !fused_available() {
        eprintln!("FMA в цели нет: граница не проверялась");
        return;
    }
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let honest = by_machine(CONTRACTION);
    let loosened = through_llvm(
        "contraction.loose",
        CONTRACTION,
        &tools,
        &pipeline("-O2", &[FMA_LLC, "-fp-contract=fast"]),
    );
    assert_ne!(
        loosened, honest,
        "`-fp-contract=fast` ничего не изменил: граница обещания описана неверно"
    );
    eprintln!("граница обещания: `llc -fp-contract=fast` даёт {loosened} вместо {honest}");
}

/// Порядок у плавающих - `totalOrder`, и три вычислителя на нём сходятся.
#[test]
fn the_total_order_agrees_across_three_evaluators() {
    let expected = by_machine(ORDER);
    assert_eq!(
        expected, "16083",
        "свидетель сменил ответ: разряды разъехались с таблицей в доке"
    );
    for level in LEVELS {
        let printed = through_c(&format!("order.c{level}"), ORDER, &[level]);
        assert_eq!(printed, expected, "C-бэкенд при {level} посчитал не то");
    }
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    for level in LEVELS {
        let printed = through_llvm(
            &format!("order.ll{level}"),
            ORDER,
            &tools,
            &pipeline(level, &[]),
        );
        assert_eq!(printed, expected, "LLVM при {level} посчитал не то");
    }
    let oldest = through_llvm("order.min", ORDER, &minimum, &pipeline("-O2", &[]));
    assert_eq!(
        oldest, expected,
        "минимальная LLVM посчитала не то: ключ порядка вышел за консервативное подмножество"
    );
    eprintln!("totalOrder: {expected} у машины, C и LLVM (включая минимальную)");
}

/// Мутанты ключа порядка: правка формулы обязана сдвинуть ответ.
///
/// Три правки - три разных способа испортить ключ, и ни одна не подменяется
/// другой.
///
/// - **`ashr` в `lshr`.** Маска у отрицательного перестаёт быть сплошной, и
///   порядок отрицательных ломается - ровно то, чем наивный «биты как целое»
///   отличается от `totalOrder`.
/// - **Беззнаковый предикат в знаковый.** Ключ построен под беззнаковое
///   сравнение: у неотрицательного значения старший разряд выставлен, и
///   знаковый предикат читает его как минус.
/// - **`xor` в `or`.** Отрицательное перестаёт инвертироваться.
#[test]
fn breaking_the_order_key_changes_the_answer() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let honest = by_machine(ORDER);
    let artefacts = harness::llvm_text("order", ORDER)
        .unwrap_or_else(|error| panic!("эмиссия отказала: {error}"));
    let mutants = [
        (
            "shift",
            "маска сдвигом без знака",
            replaced(&artefacts.ll, "= ashr ", "= lshr "),
        ),
        (
            "signed",
            "знаковый предикат по ключу",
            replaced(&artefacts.ll, "icmp ult ", "icmp slt "),
        ),
        (
            "mask",
            "маска приписыванием, а не инверсией",
            replaced(&artefacts.ll, "= xor ", "= or "),
        ),
    ];
    for (stem, why, mutant) in mutants {
        let printed = harness::llvm_printed(
            &format!("order.{stem}"),
            &mutant,
            &artefacts.support,
            &tools,
            &pipeline("-O2", &[]),
        )
        .printed;
        assert_ne!(
            printed, honest,
            "{why}: ответ не изменился, и проверка не различает"
        );
        eprintln!("мутант «{why}»: {printed} вместо {honest}");
    }
}

/// Вычисленный NaN стоит выше всякого числа, и это не зависит от сборки.
///
/// Знак и полезную нагрузку NaN, порождённого недопустимой операцией, IEEE-754
/// **не специфицирует**: железо x86 отдаёт `0xFFF8000000000000` (знак стоит),
/// свёртка констант LLVM и `clang` - `0x7FF8000000000000` (знака нет). Пока NaN
/// печатается как `NaN`, разница не видна; `totalOrder` §4.3 упорядочивал NaN
/// **знаком**, и разница становилась ответом программы.
///
/// Вопрос 172 закрыт вариантом (в): порядок остаётся `totalOrder`, но берётся
/// от значения, в котором всякий NaN заменён каноническим тихим. NaN
/// становится **одним** элементом порядка выше `+inf`, и `clamp` от него
/// отвечает верхней границей - одинаково у машины, у обоих бэкендов, у обоих
/// сишных компиляторов и на всяком уровне оптимизации.
///
/// # Что было до этого
///
/// Четырнадцать точек давали **два** ответа, ровно поровну (замер 2026-09-15 и
/// 2026-09-16). `-1.0` - машина, gcc на четырёх уровнях, clang на `-O0`, LLVM
/// на `-O0`. `1.0` - clang и LLVM на `-O1`, `-O2`, `-O3` и минимальная LLVM 18.
/// То есть ответ зависел и от уровня оптимизации, и от того, какой сишный
/// компилятор нашёлся у сборки.
///
/// # Второй сишный компилятор здесь не для полноты
///
/// Прежняя запись вопроса говорила «C-бэкенд отвечает одно на всех четырёх
/// уровнях». Верно это было про gcc; clang на `-O1` и выше отвечал другое, и
/// найдено это замером 2026-09-16. Поэтому clang стоит в матрице: обещание
/// §4.3 не должно держаться на том, чем собрали.
///
/// # Мутант возвращает дыру
///
/// Канонизация узнаёт NaN сравнением модуля с `+inf`; подмени порог на
/// наибольшее целое - и не узнает ни одного, а прочие шесть инструкций ключа
/// останутся на месте. Тогда уровень оптимизации снова меняет ответ, и мутант
/// это показывает числом: без него у LLVM один ответ на четырёх уровнях, с ним
/// два.
#[test]
fn a_computed_nan_stands_above_every_number() {
    let expected = by_machine(NAN_SIGN);
    assert_eq!(
        expected, "1.0",
        "свидетель сменил ответ: `clamp` от NaN больше не берёт верхнюю границу"
    );
    let mut seen = vec![("машина".to_owned(), expected.clone())];
    for level in LEVELS {
        seen.push((
            format!("C {level}"),
            through_c(&format!("nansign.c{level}"), NAN_SIGN, &[level]),
        ));
    }
    if let Some(clang) = harness::clang() {
        let text = harness::text(NAN_SIGN).unwrap_or_else(|why| panic!("эмиссия отказала: {why}"));
        for level in LEVELS {
            let printed = harness::built_by(
                &format!("nansign.clang{level}"),
                &text,
                &clang,
                &[level, "-Wno-unknown-warning-option"],
            )
            .0;
            seen.push((
                format!("clang {level}"),
                printed.trim_end_matches('\n').to_owned(),
            ));
        }
    }
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        eprintln!("канонический NaN без LLVM: {}", row(&seen));
        assert!(
            seen.iter().all(|(_, answer)| *answer == expected),
            "стороны разошлись на вычисленном NaN ({})",
            row(&seen)
        );
        return;
    };
    for level in LEVELS {
        seen.push((
            format!("LLVM {level}"),
            through_llvm(
                &format!("nansign.ll{level}"),
                NAN_SIGN,
                &tools,
                &pipeline(level, &[]),
            ),
        ));
    }
    seen.push((
        "LLVM 18".to_owned(),
        through_llvm("nansign.min", NAN_SIGN, &minimum, &pipeline("-O2", &[])),
    ));
    eprintln!("канонический NaN: {}", row(&seen));
    assert!(
        seen.iter().all(|(_, answer)| *answer == expected),
        "стороны разошлись на вычисленном NaN: канонизация ключа не держит ({})",
        row(&seen)
    );

    // Мутант: порог узнавания NaN поднят до наибольшего целого, и узнавать
    // становится нечего. Модуль ключа больше него быть не может по построению,
    // поэтому канонизация выключается целиком, а всё прочее остаётся.
    let artefacts = harness::llvm_text("nansign", NAN_SIGN)
        .unwrap_or_else(|error| panic!("эмиссия отказала: {error}"));
    let mutant = replaced(
        &artefacts.ll,
        ", 9218868437227405312",
        ", 9223372036854775807",
    );
    let mut blind = Vec::new();
    for level in LEVELS {
        blind.push(
            harness::llvm_printed(
                &format!("nansign.blind{level}"),
                &mutant,
                &artefacts.support,
                &tools,
                &pipeline(level, &[]),
            )
            .printed
            .trim_end_matches('\n')
            .to_owned(),
        );
    }
    assert!(
        blind.iter().any(|answer| answer != &blind[0]),
        "мутант «NaN не узнаётся» ответил одно и то же на четырёх уровнях \
         ({blind:?}): свидетель не о канонизации"
    );
    eprintln!("мутант «NaN не узнаётся»: {blind:?} вместо {expected} на всех уровнях");
}

/// Отладчик показывает плавающее числом, а не битами.
///
/// Долг, оставленный треком E явно: тип DWARF плавающему он не выдавал вовсе.
/// Выдаёт его этот - `DW_ATE_float`, - и утверждение это наблюдаемо, потому что
/// кодировкой отладчик решает, **как читать биты**. Спутай её со знаковым целым
/// - и `21.5` покажется числом `4626322717216342016`.
///
/// Мутант ровно на это: `DW_ATE_float` в `DW_ATE_signed`, ни одной инструкции
/// не тронуто, программа печатает то же. Различает только сеанс.
#[test]
fn the_debugger_reads_a_float_as_a_number() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let (_, honest) = harness::llvm_located(DEBUG_FIXTURE, DEBUG);
    assert!(
        honest.ll.contains("DW_ATE_float"),
        "плавающее приехало в DWARF без своей кодировки"
    );

    let shown = at_the_clause("float.dwarf", &honest, &tools);
    assert!(
        shown.contains("x = 21.5"),
        "отладчик не показал плавающее числом:\n{shown}"
    );

    let mutant = Artefacts {
        ll: replaced(&honest.ll, "DW_ATE_float", "DW_ATE_signed"),
        support: honest.support.clone(),
    };
    let broken = at_the_clause("float.dwarf.mutant", &mutant, &tools);
    // Сеанс мутанта обязан **состояться**: молчащий gdb прошёл бы проверку
    // «не показал 21.5» ничего не доказав, и различал бы тест сломанное
    // окружение, а не сломанную кодировку.
    let read = broken
        .lines()
        .find(|line| line.trim_start().starts_with("x = "))
        .unwrap_or_else(|| panic!("сеанс мутанта не дошёл до `info args`:\n{broken}"));
    assert_ne!(
        read.trim(),
        "x = 21.5",
        "кодировка знакового целого показала то же: свидетель не о кодировке"
    );
    eprintln!(
        "кодировка DWARF различает: `DW_ATE_signed` даёт `{}`",
        read.trim()
    );
}

/// Фикстура отладочного свидетеля: одно определение, один параметр.
const DEBUG: &str = "\
scale : Float64 -> Float64
scale x = mulFloat64 x 2.0

main : Float64
main = scale 21.5
";

/// Имя, под которым фикстура ложится на диск: его называет DWARF, по нему же
/// ставится точка останова.
const DEBUG_FIXTURE: &str = "float-session";

/// Клауза, на которой ставится останов. Номер ищется в тексте, а не помнится.
const DEBUG_STOP: &str = "scale x = mulFloat64 x 2.0";

/// Сеанс `gdb --batch` на клаузе [`DEBUG_STOP`]. Отдаёт вывод целиком.
///
/// Конвейер отладочный - `llc -O0` без `opt`, - и это не выбор, а свойство:
/// значение переменной наблюдаемо ровно пока она лежит в кадре.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn at_the_clause(stem: &str, artefacts: &Artefacts, tools: &Toolchain) -> String {
    let at = DEBUG
        .lines()
        .position(|line| line == DEBUG_STOP)
        .unwrap_or_else(|| panic!("в фикстуре нет клаузы `{DEBUG_STOP}`"))
        + 1;
    let binary = harness::llvm_binary(stem, artefacts, tools, &pipeline("-O0", &[]));
    let done = Command::new("gdb")
        .arg("--batch")
        .arg("-ex")
        .arg(format!("break {DEBUG_FIXTURE}.adamas:{at}"))
        .arg("-ex")
        .arg("run")
        .arg("-ex")
        .arg("info args")
        .arg("-ex")
        .arg("continue")
        .arg(&binary)
        .output()
        .unwrap_or_else(|why| panic!("gdb не запустился ({why}); в dev-shell он есть"));
    format!(
        "{}{}",
        String::from_utf8_lossy(&done.stdout),
        String::from_utf8_lossy(&done.stderr)
    )
}

/// Строка «кто что ответил» для печати и для текста отказа.
fn row(seen: &[(String, String)]) -> String {
    seen.iter()
        .map(|(who, answer)| format!("{who} {answer}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Текст с разрешённой контракцией: `contract` на всех плавающих инструкциях.
fn contracted(text: &str) -> String {
    let mut out = text.to_owned();
    let mut touched = 0;
    for opcode in ["fadd", "fsub", "fmul"] {
        let from = format!("= {opcode} ");
        let to = format!("= {opcode} contract ");
        touched += out.matches(&from).count();
        out = out.replace(&from, &to);
    }
    assert!(
        touched >= 3,
        "мутант не применился: плавающих инструкций в IR {touched}"
    );
    out
}

/// Текст со всеми вхождениями подстроки, заменёнными на другую.
///
/// Не нашедшаяся подстрока роняет тест наравне с правкой, ничего не изменившей:
/// мутант, который не применился, доказывает не больше, чем мутант, который не
/// убил.
fn replaced(text: &str, from: &str, to: &str) -> String {
    assert!(
        text.contains(from),
        "мутант не применился: `{from}` в порождённом IR не встречается"
    );
    text.replace(from, to)
}

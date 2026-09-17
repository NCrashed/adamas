//! Побитовые операции, сдвиги и деление (§4.3, трек A волны 4 Фазы 7).
//!
//! Корпус (`bitwise` в `agreement.rs` и `llvm.rs`) отвечает за то, что все три
//! вычислителя считают эти операции одинаково - на восьми целых типах, на обеих
//! знаковостях и на обеих версиях LLVM. Здесь стоит то, чего корпус не
//! различает по построению.
//!
//! **Три точки, и каждая - расхождение вычислителей, а не украшение.** Ни у
//! одной из трёх нет поведения, общего Rust'у, C и LLVM: сдвиг на ширину типа
//! в Rust паникует, в C неопределён, в LLVM даёт `poison`; деление на ноль в
//! Rust паникует, а в C и LLVM неопределено; `MIN / -1` в Rust заворачивается
//! по `wrapping_div`, в C и LLVM неопределён, а `idiv` на x86 отвечает на него
//! **сигналом**. Ответ поэтому назначается языком, и здесь проверяется, что
//! назначенный доехал до обоих бэкендов.
//!
//! # Свидетель на побитовых легко подделать, и значения подобраны против этого
//!
//! `and` с маской из одних единиц, `shl` на ноль, `xor` с нулём - все дают
//! исходное значение, и тест на них зелен при любой поломке. Значения здесь
//! взяты так, чтобы перепутанная операция меняла ответ: `0xF0F0` против
//! `0xBEEF` разводит все три битовые (`0xB0E0`, `0xFEFF`, `0x4E1F`), а оба
//! свидетеля знаковости отрицательны по построению - на неотрицательных
//! `ashr` и `lshr` неразличимы.

mod harness;

use std::process::Command;

use adamas_codegen::llvm::Pipeline;

/// Сдвиг влево счётчиком, равным ширине типа.
///
/// Счётчик приезжает параметром, поэтому сам эмиттер печатает его ограждение
/// целиком; свернуть его вправе только `opt`, и это отдельное наблюдение ниже.
const OVERSHOT: &str = "\
step : UInt32 -> UInt32 -> UInt32
step word count = shlUInt32 word count

main : UInt32
main = step 48879 32
";

/// Правый сдвиг отрицательного: `ashr` против `lshr`.
const SIGNED_SHIFT: &str = "\
step : Int32 -> Int32 -> Int32
step word count = shrInt32 word count

main : Int32
main = step (-268435456) 4
";

/// Единственное переполнение знакового деления.
const OVERFLOW: &str = "\
divide : Int32 -> Int32 -> Int32
divide x y = divInt32 x y

main : Int32
main = divide (-2147483648) (-1)
";

/// Нулевой делитель.
const ZERO: &str = "\
divide : Int64 -> Int64 -> Int64
divide x y = divInt64 x y

main : Int64
main = divide 7 0
";

/// Операция без ограждений: мера цены отсчитывается от неё.
const UNGUARDED: &str = "\
step : UInt32 -> UInt32 -> UInt32
step word count = andUInt32 word count

main : UInt32
main = step 48879 32
";

/// Сдвиг счётчиком **в пределах** ширины: ограждению тут сворачиваться.
const WRITTEN_SHIFT: &str = "\
step : UInt32 -> UInt32 -> UInt32
step word count = shlUInt32 word count

main : UInt32
main = step 48879 5
";

/// Деление написанным ненулевым делителем: ограждению тут сворачиваться.
const WRITTEN_DIV: &str = "\
divide : Int32 -> Int32 -> Int32
divide x y = divInt32 x y

main : Int32
main = divide 100 7
";

/// Строка `.ll`, чей хвост совпал с образцом, - заменена целиком.
///
/// Имена регистров у порождённого IR предсказуемы, но сверяться с ними
/// дословно значило бы ронять свидетеля от всякой правки нумерации. Образец
/// поэтому - хвост инструкции, а голова (`%tN = `) сохраняется.
fn rewritten(text: &str, tail: &str, replacement: &str) -> String {
    let mut found = false;
    let out = text
        .lines()
        .map(|line| {
            if line.trim_end().ends_with(tail) {
                found = true;
                let head = line.split_once('=').map_or("", |(head, _)| head);
                format!("{head}= {replacement}")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        found,
        "в порождённом IR нет строки, кончающейся на `{tail}`"
    );
    out
}

/// Тот же `.ll` без проверки нулевого делителя: наивный эмиттер.
fn without_zero_check(text: &str) -> String {
    let mut found = false;
    let out = text
        .lines()
        .map(|line| {
            let trimmed = line.trim();
            if trimmed.starts_with("br i1 ") && trimmed.contains(".zero, label %") {
                found = true;
                let good = trimmed.rsplit("label %").next().unwrap_or_default();
                format!("  br label %{good}")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        found,
        "в порождённом IR нет ветви обрыва по нулевому делителю"
    );
    out
}

/// Сколько инструкций в теле названной функции порождённого `.ll`.
///
/// Считается **до** `opt`: вопрос здесь - что печатает эмиттер, а не что умеет
/// оптимизатор. Метки, объявления и пустые строки не в счёт.
fn body_size(ll: &str, function: &str) -> usize {
    ll.lines()
        .skip_while(|line| !line.starts_with("define internal tailcc") || !line.contains(function))
        .skip(1)
        .take_while(|line| !line.starts_with('}'))
        .filter(|line| {
            let line = line.trim();
            !line.is_empty() && !line.ends_with(':') && !line.starts_with(';')
        })
        .count()
}

/// Правый сдвиг отрицательного доливает знак, а не ноль.
///
/// Мутант - одна замена в порождённом `.ll`: `ashr` на `lshr`. Она законна по
/// типам, проходит verifier и меняет **только** ответ, поэтому иначе как
/// числом её не поймать. Значение отрицательно по построению: на
/// неотрицательном оба сдвига дают одно и то же, и мутант выжил бы.
#[test]
fn a_right_shift_on_a_negative_tells_the_signedness() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("shift-signed", SIGNED_SHIFT)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert!(
        artefacts.ll.contains("ashr"),
        "знаковый сдвиг напечатан не арифметическим"
    );
    let pipeline = Pipeline::optimised();
    let honest = harness::llvm_printed(
        "shift.signed",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(honest.printed, "-16777216", "знаковый сдвиг посчитал не то");
    assert_eq!(
        harness::machine_printed(SIGNED_SHIFT),
        Ok("-16777216".to_owned()),
        "машина посчитала не то же"
    );

    let mutant = artefacts.ll.replace("ashr", "lshr");
    let printed = harness::llvm_printed(
        "shift.logical",
        &mutant,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        printed.printed, "251658240",
        "логический сдвиг дал тот же ответ, что арифметический: свидетель не различает"
    );
}

/// Сдвиг на ширину типа насыщает, а не берёт счётчик по модулю ширины.
///
/// Мутант - второй **обсуждавшийся вариант**, а не поломка: счётчик
/// маскируется по `w-1`, ровно как делает железо x86 и `wrapping_shl` Rust'а.
/// Наблюдаемое - расхождение в ответе: насыщение даёт ноль, маскирование
/// возвращает исходное значение, потому что сдвиг на целую ширину при нём не
/// теряет ни бита.
#[test]
fn a_shift_past_the_width_does_not_take_the_count_modulo_the_width() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("shift-overshot", OVERSHOT)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let pipeline = Pipeline::optimised();
    let honest = harness::llvm_printed(
        "shift.saturating",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(honest.printed, "0", "сдвиг на ширину не насытился");
    assert_eq!(
        harness::machine_printed(OVERSHOT),
        Ok("0".to_owned()),
        "машина насыщения не делает"
    );

    let masked = rewritten(&artefacts.ll, ", i32 31, i32 %v1", "and i32 %v1, 31");
    let masked = rewritten(&masked, ", i32 0, i32 %t2", "or i32 %t2, 0");
    let printed = harness::llvm_printed(
        "shift.masking",
        &masked,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        printed.printed, "48879",
        "маскирование счётчика дало то же, что насыщение: свидетель не различает"
    );
}

/// `MIN / -1` заворачивается, а не обрывает прогон сигналом.
///
/// Мутант - **наивный эмиттер**: `sdiv` без подмены делителя. Он законен по
/// типам и проходит verifier, а на x86 разворачивается в `idiv`, который на
/// этой паре отвечает `SIGFPE`. Конвейер здесь без `opt` нарочно: с ним
/// операнды сворачиваются в константы, `sdiv` становится `poison`, и наблюдать
/// было бы нечего - вопрос же именно про инструкцию.
#[test]
fn the_only_overflow_of_division_wraps_instead_of_trapping() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("div-overflow", OVERFLOW)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let pipeline = Pipeline::plain();
    let honest = harness::llvm_printed(
        "div.wrapping",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        honest.printed, "-2147483648",
        "переполнение деления не завернулось"
    );
    assert_eq!(
        harness::machine_printed(OVERFLOW),
        Ok("-2147483648".to_owned()),
        "машина завернула переполнение иначе"
    );
    let printed = harness::c_printed("div-wrapping-c", OVERFLOW);
    assert_eq!(
        printed.printed, "-2147483648",
        "C-сторона завернула переполнение иначе: {}",
        printed.reason
    );

    let naive = rewritten(&artefacts.ll, ", i32 1, i32 %v1", "or i32 %v1, 0");
    let naive = rewritten(&naive, ", i32 %t4, i32 %t3", "or i32 %t3, 0");
    let trapped = harness::llvm_printed("div.naive", &naive, &artefacts.support, &tools, &pipeline);
    assert_eq!(
        trapped.printed, "прогон оборвался",
        "наивный `sdiv` ответил вместо того, чтобы упасть: свидетель не различает"
    );
}

/// Нулевой делитель обрывает прогон, и одинаково у обоих бэкендов.
///
/// Форма границы та же, что у номера дорожки вне ширины (§4.9) и у выхода за
/// длину массива (§4.11): у машины операция не сводится вовсе, у обоих
/// бэкендов прогон обрывается **одним и тем же текстом**. Сходятся все трое в
/// том, что ответа не даёт никто.
///
/// Проверяется текст, а не сам факт обрыва: он один на два эмиттера по
/// построению ([`adamas_codegen::ir::DIVISION_BY_ZERO`]), и свидетель стережёт
/// как раз то, что построение не разошлось с прогоном.
#[test]
fn a_zero_divisor_stops_all_three_evaluators() {
    let machine = harness::printed(ZERO);
    assert!(
        machine.contains("divInt64"),
        "машина свела деление на ноль до значения: {machine}"
    );

    let printed = harness::c_printed("div-zero-c", ZERO);
    assert_eq!(
        printed.printed, "прогон оборвался",
        "C-сторона ответила на деление на ноль"
    );
    assert!(
        printed
            .reason
            .contains(adamas_codegen::ir::DIVISION_BY_ZERO),
        "C-сторона оборвалась не тем: {}",
        printed.reason
    );

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("div-zero", ZERO)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let binary = harness::llvm_binary("div.zero", &artefacts, &tools, &Pipeline::optimised());
    let run = Command::new(&binary)
        .output()
        .unwrap_or_else(|error| panic!("прогон не запустился: {error}"));
    assert!(
        !run.status.success(),
        "LLVM ответила на деление на ноль: `{}`",
        String::from_utf8_lossy(&run.stdout)
    );
    let said = String::from_utf8_lossy(&run.stderr);
    assert!(
        said.contains(adamas_codegen::ir::DIVISION_BY_ZERO),
        "оборвалось не тем и не там: {said}"
    );
}

/// Безопасное лицо деления §4.3 пишется на самом языке и стоит одной строки.
///
/// Это и есть довод, по которому нулевой делитель отдан обрыву, а не
/// умолчанию: §4.3 назначает наружным лицом `divMod`/`quotRem`, отвечающие
/// `Option`, и **цена у этой обёртки одна и та же при любом выборе внутри**.
/// Разойтись варианты могут только там, где обёртку обошли, - и там обрыв
/// говорит, а умолчание молчит.
#[test]
fn the_total_face_of_division_is_one_line_of_the_language() {
    const SAFE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Maybe (a : Type) where
  Nothing : Maybe a
  Just : a -> Maybe a

chosen : Bool -> Int64 -> Int64 -> Maybe Int64
chosen True x y = Nothing
chosen False x y = Just (divInt64 x y)

quotient : Int64 -> Int64 -> Maybe Int64
quotient x y = chosen (eqInt64 y 0) x y

orElse : Int64 -> Maybe Int64 -> Int64
orElse fallback Nothing = fallback
orElse fallback (Just value) = value

main : Int64
main = addInt64 (orElse (-1) (quotient 100 0)) (orElse (-1) (quotient 100 8))
";
    // 12 + (-1) = 11: обе ветви наблюдаемы, и перепутай их обёртка - ответ
    // стал бы 24 либо -2.
    assert_eq!(harness::machine_printed(SAFE), Ok("11".to_owned()));
    let printed = harness::c_printed("div-total-c", SAFE);
    assert_eq!(printed.printed, "11", "C-сторона: {}", printed.reason);

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("div-total", SAFE)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let run = harness::llvm_printed(
        "div.total",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &Pipeline::optimised(),
    );
    assert_eq!(run.printed, "11");
    assert_eq!(run.live, Some(0), "обёртка оставила блоки живыми");
}

/// Чего стоят ограждения, и почему цена эта нулевая у написанного операнда.
///
/// Мерится **выход эмиттера**, а не выход оптимизатора: вопрос здесь - что
/// печатается, и он задаётся до `opt` (тот же довод, что у свидетеля
/// векторности в `simd.rs`). Ограждение сдвига - три инструкции сверх самого
/// сдвига, ограждение деления - две сверх самого деления плюс ветвь обрыва.
///
/// Написанный операнд - обычный случай разбора заголовка, и на нём цена
/// **ноль**: `opt` сворачивает и сравнение, и `select`, и ветвь. Это второе
/// утверждение здесь и меряется отдельно, машинными инструкциями.
#[test]
fn the_guards_cost_three_instructions_and_nothing_at_all_when_written() {
    // Мера отсчитывается от операции **без** ограждений - побитового И: у неё
    // в теле ровно инструкция и возврат.
    let plain = harness::llvm_text("and-cost", UNGUARDED)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert_eq!(body_size(&plain.ll, "@fn_1"), 2, "у `and` появилось лишнее");

    // Сдвиг: `icmp`, зажим счётчика `select`, сам сдвиг, насыщающий `select`,
    // возврат - то есть **три** инструкции сверх непокрытой формы.
    let shift = harness::llvm_text("shift-cost", OVERSHOT)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert_eq!(
        body_size(&shift.ll, "@fn_1"),
        5,
        "ограждение сдвига стоит не то, что записано"
    );

    // Деление знакового: `icmp` и `br` нулевого делителя, `call` и
    // `unreachable` в ветви обрыва, `icmp` и `select` подмены делителя, сам
    // `sdiv`, `sub` и `select` заворачивания, возврат - **восемь** сверх
    // непокрытой формы, и половина их принадлежит второму ограждению.
    let division = harness::llvm_text("div-cost", ZERO)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    assert_eq!(
        body_size(&division.ll, "@fn_1"),
        10,
        "ограждение деления стоит не то, что записано"
    );

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();

    // Написанный операнд: обе формы обязаны дать **одно** число машинных
    // инструкций, то есть ограждение обязано исчезнуть целиком. Операнд взят
    // **в пределах** - счётчик пять, делитель семь, - и это не выбор
    // удобного случая, а требование к самой мере: у наивной формы за
    // пределами поведения нет вовсе (`shl` на ширину есть `poison`), и
    // сравнивать число инструкций было бы не с чем.
    let written = harness::llvm_text("shift-written", WRITTEN_SHIFT)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let naive = rewritten(&written.ll, ", i32 31, i32 %v1", "or i32 %v1, 0");
    let naive = rewritten(&naive, ", i32 0, i32 %t2", "or i32 %t2, 0");
    let honest = harness::llvm_object("shift.cost.honest", &written, &tools, &pipeline);
    let mut stripped = written.clone();
    stripped.ll = naive;
    let stripped = harness::llvm_object("shift.cost.naive", &stripped, &tools, &pipeline);
    assert_eq!(
        harness::instructions(&tools, &honest),
        harness::instructions(&tools, &stripped),
        "ограждение сдвига не свернулось на написанном счётчике"
    );

    let written = harness::llvm_text("div-written", WRITTEN_DIV)
        .unwrap_or_else(|error| panic!("не понизилось: {error}"));
    let naive = without_zero_check(&written.ll);
    let naive = rewritten(&naive, ", i32 1, i32 %v1", "or i32 %v1, 0");
    let naive = rewritten(&naive, ", i32 %t4, i32 %t3", "or i32 %t3, 0");
    let honest = harness::llvm_object("div.cost.honest", &written, &tools, &pipeline);
    let mut stripped = written.clone();
    stripped.ll = naive;
    let stripped = harness::llvm_object("div.cost.naive", &stripped, &tools, &pipeline);
    assert_eq!(
        harness::instructions(&tools, &honest),
        harness::instructions(&tools, &stripped),
        "ограждение деления не свернулось на написанном делителе"
    );
}

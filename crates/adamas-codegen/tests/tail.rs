//! Хвостовой вызов не растит стек - свойством бэкенда, а не ключей сборки.
//!
//! Обещание §3.4 (инлайнинг хвостово-резумптивных хендлеров) и правило чужого
//! кадра §5.3 держатся на том, что хвостовой вызов замещает кадр вызывающего.
//! До этого трека держались они на **ключах**: `-O2` умеет оптимизировать
//! хвостовой вызов сам, `-O0` не умеет вовсе (`docs/phase7-plan.md`, трек D
//! волны 1). Здесь гарантия переезжает в само IR - `tailcc` на определениях и
//! `musttail` на инструкции, - и свидетель ниже мерит именно переезд.
//!
//! # Свидетель подобран замером, а не рассуждением
//!
//! Очевидный свидетель не свидетельствует. Самохвостовая рекурсия
//! (`workload-scalar`) на `-O2` завершается **и без** `musttail`: `opt`
//! превращает её в цикл проходом `tailrecurse`. Тест на ней был бы зелёным и
//! пустым.
//!
//! Дальше померено (2026-09-15, LLVM 21.1.8, синтетический IR той же формы,
//! что печатает эмиттер; глубина 10⁷ во всех строках):
//!
//! | форма | без гарантии, `-O0` | без гарантии, `-O2` |
//! |---|---|---|
//! | самохвостовая рекурсия | падает | **проходит** |
//! | взаимная рекурсия, кольцо 2 | падает | **проходит** |
//! | кольцо 8, 12, 16, 24, 32 | падает | **проходит** |
//! | кольцо 2, широкая арность, тела мелкие | падает | **проходит** |
//! | кольцо 2, широкая арность, тела крупные | падает | падает |
//!
//! Механизмов, спасающих программу на `-O2`, ровно два, и оба видны в дампе.
//! Первый - **инлайнинг**: кольцо любой длины сворачивается в одну функцию, и
//! дальше её берёт `tailrecurse`; кольцо из 32 функций схлопнулось до двух.
//! Второй - **sibling call optimization** в `llc`: остаток кольца
//! превращается в `jmp fn_17 # TAILCALL`.
//!
//! Оба обходятся, и каждая часть свидетеля закрывает **один** из них.
//!
//! *Широкая арность закрывает `llc`.* Оптимизация хвостового вызова, которую
//! `llc` делает сам, требует, чтобы кадру вызываемого хватило места
//! вызывающего. `narrow` двух параметров зовёт `wide` шестнадцати: десять
//! аргументов уезжают на стек, а входного стека у `narrow` нет вовсе -
//! оптимизация отказывает, и в машинном коде на этой дуге стоит `callq fn_2`
//! против `jmp fn_2 # TAILCALL` у честного варианта (проверено `objdump`
//! обеих сборок). Обратная дуга, `wide` в `narrow`, сужается и оптимизируется
//! - её и хватает, чтобы ровно половина витков росла стеком.
//!
//! *Крупное тело со второй точкой вызова закрывает инлайнинг.* Одна точка
//! вызова у внутренней функции даёт инлайнеру бонус, перебивающий любой
//! размер; отсюда `wide`, позванная **обеими** ветвями `narrow`. Размер тела
//! мерился: свёртка по 14 параметрам (три операции на параметр) кольцо
//! сохраняет, по 12 - уже нет. Свёртка **нелинейная** (`acc·acc·K + p`) не
//! случайно: линейную цепочку `InstCombine` складывает в одно умножение, и
//! никакого размера у тела не остаётся.
//!
//! # Свидетель живёт здесь, а не в корпусе
//!
//! Тот же довод, по которому в `llvm.rs` живёт `VERDICTS`, плюс один сильнее:
//! глубина 10⁷ - не программа для `adamas eval`. Поэтому свидетель считается
//! **дважды**: на [`SHALLOW`] его ответ сверяют все три вычислителя (без этого
//! «завершилось» покрывало бы и программу, которая не крутилась), а на
//! [`DEPTH`] наблюдается только то, ради чего трек и написан, - что прогон
//! доходит до конца.

mod harness;

use adamas_codegen::llvm::Pipeline;

/// Глубина, названная планом: 10⁷ хвостовых вызовов.
const DEPTH: u64 = 10_000_000;

/// Глубина, на которой ответ ещё считает машина.
///
/// Тысяча, а не десяток: виток свидетеля проходит через **обе** функции, и
/// короткая гонка не отличила бы «свернулось» от «не крутилось».
const SHALLOW: u64 = 1_000;

/// Свидетель: взаимная рекурсия между узкой и широкой функцией.
///
/// Обе дуги хвостовые, ни одна не ведёт в себя. Что стоит за каждой чертой
/// формы - в шапке файла; здесь коротко: `wide` шестнадцати параметров, чтобы
/// её кадр не помещался в кадр `narrow`, позвана из **обеих** ветвей `narrow`,
/// чтобы инлайнер не съел кольцо, и сворачивает свои параметры нелинейно,
/// чтобы тело не сократилось до нескольких инструкций.
///
/// Ответ - число, а не «посчиталось»: свёртка по счётчику и по накопителю
/// нелинейна, и сбитый на один виток счёт даёт другое число.
const WITNESS: &str = "\
data Bool where
  True : Bool
  False : Bool

mutual
  narrow : UInt64 -> UInt64 -> UInt64
  narrow 0 acc = wide 0 acc acc acc acc acc acc acc acc acc acc acc acc acc acc acc
  narrow n acc = wide (subUInt64 n 1) acc n acc n acc n acc n acc n acc n acc n acc

  wide : UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64 -> UInt64
  wide 0 acc p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 = acc
  wide k acc p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 =
    let x1 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 acc acc) 6364136223846793005) p1
    let x2 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x1 x1) 6364136223846793005) p2
    let x3 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x2 x2) 6364136223846793005) p3
    let x4 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x3 x3) 6364136223846793005) p4
    let x5 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x4 x4) 6364136223846793005) p5
    let x6 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x5 x5) 6364136223846793005) p6
    let x7 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x6 x6) 6364136223846793005) p7
    let x8 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x7 x7) 6364136223846793005) p8
    let x9 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x8 x8) 6364136223846793005) p9
    let x10 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x9 x9) 6364136223846793005) p10
    let x11 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x10 x10) 6364136223846793005) p11
    let x12 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x11 x11) 6364136223846793005) p12
    let x13 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x12 x12) 6364136223846793005) p13
    let x14 : UInt64 = addUInt64 (mulUInt64 (mulUInt64 x13 x13) 6364136223846793005) p14
    narrow (subUInt64 k 1) x14

main : UInt64
main = narrow DEPTH 1
";

/// Свидетель на названной глубине.
fn witness(depth: u64) -> String {
    WITNESS.replace("DEPTH", &depth.to_string())
}

/// Конвейеры, которыми собирается артефакт: `-O2` и без оптимизации.
///
/// Гарантия обязана держаться на **обоих**. Проверять её одним `-O2` значило
/// бы проверять оптимизатор: он и без нас превращает часть хвостовых вызовов в
/// переходы, а `-O0` не превращает ни одного.
fn pipelines() -> [(&'static str, Pipeline); 2] {
    [("-O2", Pipeline::optimised()), ("-O0", Pipeline::plain())]
}

/// Свидетель считает то же, что машина: он не «просто завершается».
///
/// Без этого теста «прогон дошёл до конца» покрывало бы и программу, чей цикл
/// свернулся на первом витке. Глубина здесь [`SHALLOW`] - её берёт и
/// интерпретатор, и C-бэкенд, у которого хвостовых вызовов нет.
#[test]
fn the_witness_answers_what_the_machine_answers() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = witness(SHALLOW);
    let (printed, _) = harness::llvm_agreed(
        "tail-witness",
        &source,
        &tools,
        &Pipeline::optimised(),
        "tail.shallow",
    )
    .unwrap_or_else(|error| panic!("свидетель не собрался: {error}"));
    harness::agreed("tail-shallow", &source)
        .unwrap_or_else(|error| panic!("C-бэкенд отказал на свидетеле: {error}"));
    eprintln!("на глубине {SHALLOW} все трое отвечают {printed}");
}

/// Готовность трека: 10⁷ хвостовых вызовов доходят до конца.
///
/// Критерий бинарный и наблюдаемый - завершился прогон или переполнил стек, -
/// и проверяется он на **всех** осях, которыми собирается артефакт: два уровня
/// оптимизации на двух поддерживаемых версиях LLVM. Гарантия, работающая
/// только на одной из четырёх, гарантией не является.
#[test]
fn ten_million_tail_calls_finish_at_every_optimisation_level() {
    let Some((current, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let source = witness(DEPTH);
    let artefacts = harness::llvm_text("tail-witness", &source)
        .unwrap_or_else(|error| panic!("свидетель не собрался: {error}"));

    let mut answers = Vec::new();
    for (tag, version, tools) in [
        ("new", "штатная", &current),
        ("old", "минимальная", &minimum),
    ] {
        for (level, pipeline) in pipelines() {
            // Своё имя артефактам каждой оси: общее означало бы, что вторая
            // проверка мерит объектник первой.
            let stem = format!("tail.deep.{tag}.{level}");
            let printed =
                harness::llvm_printed(&stem, &artefacts.ll, &artefacts.support, tools, &pipeline)
                    .printed;
            assert!(
                printed.parse::<u64>().is_ok(),
                "{version} цепочка, {level}: 10⁷ хвостовых вызовов не дошли до конца ({printed})"
            );
            eprintln!("{version} цепочка, {level}: {printed}");
            answers.push(printed);
        }
    }
    // Четыре сборки одной программы обязаны сойтись в числе: разойдись они -
    // «завершилось» означало бы, что где-то посчиталось не то.
    assert!(
        answers.windows(2).all(|pair| pair[0] == pair[1]),
        "четыре сборки свидетеля разошлись ответом: {answers:?}"
    );
}

/// Мутанты: снятая гарантия обязана уронить свидетеля.
///
/// Правок две, и они разной силы - потому что разной силы и то, что снимается.
///
/// *Снята приставка `musttail`, соглашение осталось.* Падает на `-O0` и
/// **проходит** на `-O2`: соглашение `tailcc` позволяет `llc` оптимизировать
/// хвостовой вызов самому, но делает он это только с оптимизацией. Ровно тот
/// случай, ради которого трек и написан: гарантия, работающая только на `-O2`,
/// гарантией не является. Утверждается здесь поэтому падение на `-O0`, а
/// поведение на `-O2` печатается: оно наблюдение, а не обещание.
///
/// *Снято и соглашение* - вызов такой, каким его печатал эмиттер до трека.
/// Падает на **обоих** уровнях, и это доказывает, что `-O2` сам по себе
/// свидетеля не спасает: спасает его гарантия.
///
/// Не найдись правка в тексте - тест падает наравне с правкой, ничего не
/// изменившей: мутант, который не применился, доказывает не больше, чем
/// мутант, который не убил.
#[test]
fn taking_the_guarantee_off_overflows_the_stack() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let source = witness(DEPTH);
    let artefacts = harness::llvm_text("tail-witness", &source)
        .unwrap_or_else(|error| panic!("свидетель не собрался: {error}"));

    let marker = without(&artefacts.ll, "musttail ");
    let convention = without(&marker, "tailcc ");

    for (stem, why, mutant, everywhere) in [
        (
            "marker",
            "снята приставка `musttail`",
            marker.clone(),
            false,
        ),
        (
            "convention",
            "снята и приставка, и соглашение",
            convention,
            true,
        ),
    ] {
        for (level, pipeline) in pipelines() {
            let printed = harness::llvm_printed(
                &format!("tail.mutant.{stem}.{level}"),
                &mutant,
                &artefacts.support,
                &tools,
                &pipeline,
            )
            .printed;
            let finished = printed.parse::<u64>().is_ok();
            eprintln!("мутант «{why}», {level}: {printed}");
            if everywhere || level == "-O0" {
                assert!(
                    !finished,
                    "мутант «{why}» дошёл до конца на {level}: свидетель не о том"
                );
            }
        }
    }
}

/// Плотный агрегат ответом снимает `musttail`, и порог у этого мерян.
///
/// Свидетель написан по дефекту, найденному капстоуном (`eval/packets`), а не
/// по замыслу. Целое шире трёх слов возвращается через скрытый указатель, и
/// хвостовой вызов в чужой `sret` писать не вправе; `llc -O0` отвечает на такую
/// пару не отказом разбора, а `LLVM ERROR: failed to perform tail call
/// elimination on a call site marked musttail` и роняет **сборку целиком**.
/// Штатный конвейер её проходит - `opt` поднимает поля агрегата в регистры
/// раньше, чем дело доходит до легализации, - поэтому ловится дефект только
/// вторым конвейером.
///
/// Порог измерен, а не предположен: запись из **трёх** полей (`i192`)
/// проходила обе цепочки, из **четырёх** (`i256`) роняла вторую. Ловит это
/// ответ, а не аргумент - тот же четырёхполевой агрегат **параметром** при
/// скалярном ответе проходит; проверено тем же прогоном. Сам порог при этом
/// принадлежит ABI хоста, а порождённый `.ll` обязан оставаться переносимым,
/// поэтому приставка снимается у всякого агрегатного ответа, а не у широкого.
///
/// Цена решения названа там же, где оно принято (`emit_llvm::tail`): у такой
/// функции обещание §3.4 и §5.3 держится на `tailrecurse` и sibling call, то
/// есть с `-O2`, а не безусловно.
#[test]
fn a_dense_aggregate_answer_drops_the_prefix() {
    const WIDE: &str = "\
data Bool where
  True : Bool
  False : Bool

type Tally = { a : UInt64, b : UInt64, c : UInt64, d : UInt64 }

step : UInt64 -> Tally -> Tally
step 0 t = t
step k t =
  step (subUInt64 k 1) { a = addUInt64 t.a k, b = xorUInt64 t.b k, c = mulUInt64 t.c 3,
                         d = t.d }

main : UInt64
main =
  let t : Tally = step 5 { a = 0, b = 0, c = 1, d = 2 }
  addUInt64 t.a (addUInt64 t.b (addUInt64 t.c t.d))
";
    // Тот же агрегат в **параметре** при скалярном ответе: приставка остаётся,
    // и вторая цепочка её принимает. Без этой половины «снимаем у агрегата»
    // читалось бы как «агрегат с `musttail` несовместим вовсе».
    const NARROW: &str = "\
data Bool where
  True : Bool
  False : Bool

type Tally = { a : UInt64, b : UInt64, c : UInt64, d : UInt64 }

step : UInt64 -> Tally -> UInt64
step 0 t = addUInt64 t.a (addUInt64 t.b (addUInt64 t.c t.d))
step k t =
  step (subUInt64 k 1) { a = addUInt64 t.a k, b = xorUInt64 t.b k, c = mulUInt64 t.c 3,
                         d = t.d }

main : UInt64
main = step 5 { a = 0, b = 0, c = 1, d = 2 }
";
    let wide = harness::llvm_text("tail-wide", WIDE)
        .unwrap_or_else(|error| panic!("широкий ответ не понизился: {error}"));
    assert!(
        !wide.ll.contains("musttail"),
        "приставка осталась у агрегатного ответа: `llc -O0` уронит сборку"
    );
    let narrow = harness::llvm_text("tail-narrow", NARROW)
        .unwrap_or_else(|error| panic!("узкий ответ не понизился: {error}"));
    assert!(
        narrow.ll.contains("musttail"),
        "приставка снята и там, где она законна: агрегат в параметре её не трогает"
    );

    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    for (name, source) in [("tail-wide", WIDE), ("tail-narrow", NARROW)] {
        for (level, pipeline) in [
            ("-O2", Pipeline::optimised()),
            ("-O0", Pipeline::plain()),
        ] {
            let printed = harness::llvm_agreed(
                name,
                source,
                &tools,
                &pipeline,
                &format!("{name}{level}"),
            )
            .unwrap_or_else(|error| panic!("{name} на {level}: {error}"))
            .0;
            assert_eq!(printed, "261", "{name} на {level} посчитал не то");
        }
    }
}

/// Текст без названной подстроки. Не найденная подстрока роняет тест.
fn without(text: &str, marker: &str) -> String {
    assert!(
        text.contains(marker),
        "мутант не применился: `{marker}` в порождённом IR не встречается"
    );
    text.replace(marker, "")
}

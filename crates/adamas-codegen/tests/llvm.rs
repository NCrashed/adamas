//! Договор третьего вычислителя: LLVM отвечает то же, что `adamas eval` и C.
//!
//! Жанр тот же, что у `agreement.rs`, и это не совпадение, а требование плана
//! (`docs/phase7-plan.md`, трек A волны 1): «третий вычислитель входит в тот же
//! договор, что связывает первые два». Свидетель - **интерпретатор**: своё
//! ожидание, записанное руками, не показывает ничего.
//!
//! # Почему рядом, а не внутри `agreement.rs`
//!
//! Три довода, и все три - про то, что иначе мера считалась бы по другому
//! корпусу, не сказав об этом.
//!
//! *Знаменатели разные.* `agreement.rs` требует, чтобы **всякая** программа из
//! `TAKEN` собралась; скалярный фрагмент LLVM берёт из корпуса единицы, и
//! слить два списка в один значило бы либо усечь первый, либо объявить второй
//! невыполненным.
//!
//! *Внешние инструменты.* Путь LLVM зовёт `llvm-as`, `opt` и `llc` -
//! процессами, а не библиотекой. Не окажись их, и договор C, у которого их
//! нет, стал бы пропускаемым заодно.
//!
//! *Вторая цепочка.* Правило консервативного подмножества проверяется
//! **прогоном на минимальной версии**, то есть тем же `.ll`, прошедшим второй
//! конвейер. У C-договора такой оси нет вовсе.
//!
//! Договор при этом один: обе стороны сверяются с машиной, и здесь стоят обе -
//! [`harness::agreed`] считает программу C-бэкендом, [`harness::llvm_agreed`]
//! LLVM-ом, и оба сверяют свой ответ с `adamas eval`. Разойдись любые два - и
//! падает этот тест, а не глаз читателя.
//!
//! # Чем инструменты берутся
//!
//! Каталогами из `ADAMAS_LLVM_BIN` и `ADAMAS_LLVM_MIN_BIN`; обе выставляет
//! dev-shell (`flake.nix`). Их отсутствие - **отказ**, а не пропуск: молчаливо
//! зелёный тест здесь был бы обманчивым свидетелем. Единственное объявленное
//! исключение - `ADAMAS_LLVM=absent`, и стоит оно в одном месте
//! (`.github/workflows/ci.yml`, нога macOS), где LLVM в образе раннера нет.
//! Само правило живёт в [`harness::llvm_toolchains`] - одной записью на всех
//! свидетелей LLVM-пути, потому что вторая разъехалась бы с первой молча.

mod harness;

use std::path::PathBuf;

use adamas_codegen::llvm::{MINIMUM_MAJOR, MINIMUM_TOOLS_VARIABLE, Pipeline};

/// Программы корпуса, которые скалярный фрагмент обязан взять.
///
/// Список короткий по построению: фрагмент берёт плоское целое, арифметику,
/// сравнение, прямой вызов, `let` и разбор по нульарному конструктору - и
/// ответ программы обязан быть плоским целым. Всё прочее отвергается названной
/// причиной, и причины эти печатаются мерой ниже.
///
/// Сокращать нельзя, пополнять - можно и нужно, когда фрагмент растёт: ровно то
/// же правило, что у `agreement.rs`.
const TAKEN: [&str; 2] = ["workload-scalar", "workload-scalar-affine"];

/// Углы фрагмента, которых корпус не покрывает ни одной фикстурой.
///
/// Написано здесь, а не в корпусе, по тому же доводу, по которому там стоят
/// `CAPTURES` и `TOWER` (`agreement.rs`): показывает не форму языка, а границу
/// эмиттера. Корпус LLVM-фрагмент трогает двумя программами, и обе - `UInt64`
/// со сложением, вычитанием, умножением и одним `eqUInt64`. Всё остальное,
/// что срез умеет, оставалось бы непроверенным.
///
/// Что здесь наблюдается и почему именно так.
///
/// *Знаковость сравнения.* `ltInt8 (-1) 0` против `ltUInt8 255 0` - **одни и
/// те же биты**, и вердикты разные: `slt` против `ult`. Спутай их эмиттер, и
/// два разряда суммы поменяются местами.
///
/// *Строгое против нестрогого.* `lt` и `le` расходятся ровно на равных, `gt` и
/// `ge` - тоже; шесть предикатов покрыты все.
///
/// *Ширина типа.* `addUInt8 200 100`, `mulInt16 300 300`, `subUInt32 0 1` -
/// заворачивание по ширине, а не по слову. Эмитируй эмиттер `i64` вместо `i8`,
/// и ответ разошёлся бы.
///
/// *Порядок операндов.* `subInt64 3 10` некоммутативно.
///
/// *Разбор внутри разбора.* `pair` связывает два вердикта в одном теле, и
/// внешняя ветвь **заканчивается** не тем блоком, которым началась. Ошибись
/// эмиттер предшественником `phi` - и `.ll` не прошёл бы verifier.
///
/// Веса разрядов различны, поэтому перевёрнутый вердикт меняет сумму, а не
/// переставляет слагаемые: наблюдаемое здесь - число, а не «посчиталось».
const VERDICTS: &str = "\
data Bool where
  True : Bool
  False : Bool

pick : Bool -> Int64 -> Int64 -> Int64
pick True yes no = yes
pick False yes no = no

weigh : Int64 -> Bool -> Int64 -> Int64
weigh acc verdict weight = addInt64 acc (pick verdict weight 0)

pair : Bool -> Bool -> Int64
pair True True = 3
pair True False = 2
pair False True = 1
pair False False = 0

main : Int64
main =
  let a : Int64 = weigh 0 (ltInt8 (-1) 0) 1
  let b : Int64 = weigh a (ltUInt8 255 0) 2
  let c : Int64 = weigh b (ltInt64 7 7) 4
  let d : Int64 = weigh c (leInt64 7 7) 8
  let e : Int64 = weigh d (gtInt64 7 3) 16
  let f : Int64 = weigh e (geInt64 3 7) 32
  let g : Int64 = weigh f (neInt64 3 7) 64
  let h : Int64 = weigh g (eqUInt8 (addUInt8 200 100) 44) 128
  let i : Int64 = weigh h (eqInt16 (mulInt16 300 300) 24464) 256
  let j : Int64 = weigh i (eqUInt32 (subUInt32 0 1) 4294967295) 512
  let k : Int64 = weigh j (eqInt64 (subInt64 3 10) (-7)) 1024
  addInt64 k (mulInt64 (pair (ltInt64 1 2) (ltInt64 2 1)) 2048)
";

/// Мера среза: что эмиттер берёт и чем отвергает остальное.
///
/// Инструментов не спрашивает вовсе - тут только эмиссия, - и потому идёт
/// **везде**, включая машину без LLVM. Без этого объявленное отсутствие
/// (`ADAMAS_LLVM=absent`) гасило бы заодно и список [`TAKEN`]: усохни он там,
/// прогон остался бы зелёным и пустым.
///
/// Обе половины обязательны, как и в `agreement.rs`. Без первой список молча
/// усох бы; без второй «не берётся» покрывало бы и тихое расхождение.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn the_scalar_fragment_takes_what_it_declares() {
    let mut fixtures: Vec<PathBuf> = std::fs::read_dir(harness::corpus())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    fixtures.sort();
    assert!(!fixtures.is_empty(), "корпус пуст");

    let mut taken = Vec::new();
    let mut refused = Vec::new();
    for path in &fixtures {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let source = std::fs::read_to_string(path).unwrap();
        match harness::llvm_text(&name, &source) {
            Ok(_) => taken.push(name),
            Err(error) => refused.push((name, error.to_string())),
        }
    }

    for name in TAKEN {
        assert!(
            taken.iter().any(|it| it == name),
            "{name} больше не берётся LLVM-эмиттером: {}",
            refused
                .iter()
                .find(|(it, _)| it == name)
                .map_or_else(|| "фикстуры нет вовсе".to_owned(), |(_, why)| why.clone())
        );
    }

    // Мера печатается прогоном, а не переписывается руками: тот же порядок,
    // что у `agreement.rs`. Видна она под `--nocapture`.
    eprintln!(
        "скалярный фрагмент: взято {} из {}, отвергнуто {}",
        taken.len(),
        fixtures.len(),
        refused.len()
    );
    for (name, why) in &refused {
        eprintln!("  отвергнуто {name}: {why}");
    }
}

/// Корпус целиком: ответ трёх вычислителей сходится.
///
/// Здесь путь идёт до конца - сборка, линковка, прогон, - и потому нужны
/// инструменты. Список берётся [`taken_sources`], а его полнота проверена
/// соседним тестом, которому инструменты не нужны.
#[test]
fn the_corpus_agrees_across_three_evaluators() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let major = tools
        .major()
        .unwrap_or_else(|error| panic!("штатная цепочка LLVM недоступна: {error}"));

    let pipeline = Pipeline::optimised();
    eprintln!("LLVM {major}:");
    for (name, source) in taken_sources() {
        let (printed, stderr) =
            harness::llvm_agreed(&name, &source, &tools, &pipeline, &format!("{name}.llvm"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        // Течь ловится тем же счётчиком, что у C-бэкенда: строку печатает
        // `main.c`, взятый обоими дословно.
        let (_, live) = harness::blocks(&name, &stderr);
        assert_eq!(live, 0, "{name}: прогон LLVM оставил блоки живыми");
        // Вторая сторона договора: тот же исходник, посчитанный C-бэкендом и
        // сверенный с машиной. Оба равны ответу машины - значит равны между
        // собой, и расхождение уронит один из двух.
        harness::agreed(&name, &source)
            .unwrap_or_else(|error| panic!("{name}: C-бэкенд отказал: {error}"));
        eprintln!("  сошлись на {name}: {printed}");
    }
}

/// Две нагрузки различаются ответом, а не только исходником.
///
/// `workload-scalar` и `workload-scalar-affine` отличаются **одной** строкой -
/// телом витка (`acc·acc·K + n` против `acc·K + n`). Совпади их ответы, и весь
/// корпус этого теста доказывал бы одно: что путь до печати работает. Разные
/// ответы означают, что через LLVM проехало содержание цикла.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn the_two_workloads_do_not_answer_the_same() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let answers: Vec<String> = TAKEN
        .iter()
        .map(|name| {
            let source =
                std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
            harness::llvm_agreed(name, &source, &tools, &pipeline, &format!("{name}.pair"))
                .unwrap_or_else(|error| panic!("{name}: {error}"))
                .0
        })
        .collect();
    assert_ne!(
        answers[0], answers[1],
        "две нагрузки ответили одинаково: тело витка через LLVM не доехало"
    );
    // И ни один из ответов не «ноль по построению»: нулём отвечает и цикл,
    // который не крутился ни разу.
    for (name, answer) in TAKEN.iter().zip(&answers) {
        assert_ne!(answer, "0", "{name}: ответ ноль - крутиться было незачем");
    }
}

/// Минимальная поддерживаемая версия читает наш IR и считает то же.
///
/// Это и есть проверка правила «консервативное подмножество IR» - прогоном, а
/// не грепом по формам. Замеры 2026-09-08 показали, что матрица чтения `.ll`
/// строго треугольная и ломает её один необязательный флаг; греп по формам
/// перестал бы ловить на первом же новом.
///
/// Тест печатает **обе** версии. Совпади они - треугольник этим прогоном не
/// проверен, и сказать об этом обязан он сам, а не читатель логов.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_minimum_llvm_reads_the_same_ir() {
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let current = tools
        .major()
        .unwrap_or_else(|error| panic!("штатная цепочка LLVM недоступна: {error}"));
    let oldest = minimum.major().unwrap_or_else(|error| {
        panic!("минимальная цепочка LLVM недоступна (`{MINIMUM_TOOLS_VARIABLE}`): {error}")
    });
    assert!(
        oldest <= MINIMUM_MAJOR,
        "минимальной названа {oldest}, а объявлено {MINIMUM_MAJOR}: правило проверяется не тем"
    );
    if current == oldest {
        eprintln!(
            "обе цепочки {current}: треугольник чтения этим прогоном не проверен, \
             проверена только сборка"
        );
    } else {
        eprintln!("штатная LLVM {current}, минимальная {oldest}");
    }

    let pipeline = Pipeline::optimised();
    for (name, source) in taken_sources() {
        let new = harness::llvm_agreed(&name, &source, &tools, &pipeline, &format!("{name}.new"))
            .unwrap_or_else(|error| panic!("{name}: {error}"))
            .0;
        let old = harness::llvm_agreed(&name, &source, &minimum, &pipeline, &format!("{name}.old"))
            .unwrap_or_else(|error| panic!("{name} на LLVM {oldest}: {error}"))
            .0;
        assert_eq!(
            new, old,
            "{name}: LLVM {oldest} посчитала не то, что {current}"
        );
    }
}

/// Программы, на которых меряются оси среза: корпусные плюс углы фрагмента.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отсутствие фикстуры означает сломанный корпус"
)]
fn taken_sources() -> Vec<(String, String)> {
    let mut all: Vec<(String, String)> = TAKEN
        .iter()
        .map(|name| {
            let path = harness::corpus().join(format!("{name}.adamas"));
            ((*name).to_owned(), std::fs::read_to_string(path).unwrap())
        })
        .collect();
    all.push(("verdicts".to_owned(), VERDICTS.to_owned()));
    all
}

/// Ответ не приносит `opt`: без оптимизации он тот же.
///
/// Без этого свидетеля «через LLVM» читалось бы как «через `opt -O2`», и
/// сломанный эмиттер, чей IR оптимизатор случайно вычистил, прошёл бы.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_answer_does_not_come_from_the_optimiser() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    for (name, source) in taken_sources() {
        let fast = harness::llvm_agreed(
            &name,
            &source,
            &tools,
            &Pipeline::optimised(),
            &format!("{name}.fast"),
        )
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .0;
        let slow = harness::llvm_agreed(
            &name,
            &source,
            &tools,
            &Pipeline::plain(),
            &format!("{name}.slow"),
        )
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .0;
        assert_eq!(fast, slow, "{name}: `opt -O2` меняет ответ");
    }
}

/// Мутанты: правка порождённого IR обязана менять напечатанное.
///
/// «Собралось и напечатало число» ловит меньше, чем кажется: то же число
/// печатается и при половине сломанных путей. Здесь ломается **порождённый
/// `.ll`** - по одной правке на путь, - и каждая обязана сдвинуть ответ.
/// Правка, не нашедшаяся в тексте, роняет тест наравне с правкой, ничего не
/// изменившей: мутант, который не применился, доказывает не больше, чем
/// мутант, который не убил.
///
/// Три правки - три разных пути, и подобраны так, чтобы ни одна не подменялась
/// другой.
///
/// - **Ветви разбора.** `switch` уводит теги в чужие блоки: `mix 1000` уходит
///   в ветвь «счётчик кончился» на первом же витке.
/// - **Порядок аргументов вызова.** `main` зовёт `mix` с переставленными
///   аргументами; типы у них одинаковые, поэтому verifier молчит, а цикл
///   получает нулевой счётчик.
/// - **Код операции.** Сложение накопителя становится вычитанием: цепочка
///   считается другая, а число витков то же.
///
/// Все три завершаются - это проверено прогоном, а не рассуждением, - но
/// предел по времени в [`harness::llvm_printed`] стоит всё равно: соседняя
/// правка того же жанра (`sub` счётчика в `add`) цикл не завершает вовсе, и
/// повесить прогон дешевле, чем кажется.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn a_broken_emitter_changes_the_printed_answer() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let name = "workload-scalar";
    let source = std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
    let pipeline = Pipeline::optimised();
    let honest = harness::llvm_agreed(name, &source, &tools, &pipeline, "mutant.honest")
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .0;
    let artefacts = harness::llvm_text(name, &source).unwrap();

    let mutants = [
        (
            "branch",
            "перепутанные ветви разбора",
            swapped(
                &artefacts.ll,
                "i16 0, label %m0.a0 i16 1, label %m0.a1",
                "i16 0, label %m0.a1 i16 1, label %m0.a0",
            ),
        ),
        (
            "argument",
            "переставленные аргументы вызова",
            swapped(
                &artefacts.ll,
                "call tailcc i64 @fn_1(i64 %t0, i64 0)",
                "call tailcc i64 @fn_1(i64 0, i64 %t0)",
            ),
        ),
        (
            "opcode",
            "вычитание вместо сложения накопителя",
            swapped(&artefacts.ll, "%t7 = add i64 %t6", "%t7 = sub i64 %t6"),
        ),
    ];

    for (stem, why, mutant) in mutants {
        let printed = harness::llvm_printed(
            &format!("mutant.{stem}"),
            &mutant,
            &artefacts.support,
            &tools,
            &pipeline,
        );
        assert_ne!(
            printed, honest,
            "{why}: ответ не изменился, и проверка не различает"
        );
        eprintln!("мутант «{why}»: {printed} вместо {honest}");
    }
}

/// Текст с единственной заменой. Не найденная подстрока роняет тест.
fn swapped(text: &str, from: &str, to: &str) -> String {
    assert_eq!(
        text.matches(from).count(),
        1,
        "мутант не применился: `{from}` встречается в порождённом IR не один раз"
    );
    text.replace(from, to)
}

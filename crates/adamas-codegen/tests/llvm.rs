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
//! Каталогами из `ADAMAS_LLVM_BIN` и `ADAMAS_LLVM_MIN_BIN`, плюс путь к clang в
//! `ADAMAS_CLANG` для рантайма в `.bc`; все три выставляет dev-shell
//! (`flake.nix`). Их отсутствие - **отказ**, а не пропуск: молчаливо зелёный
//! тест здесь был бы обманчивым свидетелем. Единственное объявленное исключение
//! называется `ADAMAS_LLVM=absent` и стоит в одном месте
//! (`.github/workflows/ci.yml`, нога macOS), где LLVM в образе раннера нет;
//! второго исключения под clang не заводится, потому что гасит он то же самое.
//! Само правило живёт в [`harness::llvm_toolchains`] - одной записью на всех
//! свидетелей LLVM-пути, потому что вторая разъехалась бы с первой молча.

mod harness;

use std::path::PathBuf;

use adamas_codegen::llvm::{MINIMUM_MAJOR, MINIMUM_TOOLS_VARIABLE, Pipeline};

/// Программы корпуса, которые срез обязан взять.
///
/// Стен у списка больше **нет**: после треков A и C волны 3 в нём весь корпус
/// за вычетом одной программы, и та отвергается границей языка, а не эмиттером
/// (`function`: ответ программы есть функция, печатать её нечем). Причина
/// остатка печатается мерой ниже и сверяется ею же.
///
/// Сокращать нельзя, пополнять - можно и нужно, когда фрагмент растёт: ровно то
/// же правило, что у `agreement.rs`.
///
/// Двадцать одна из них - **сумма двух треков**, и слагаемые не складываются
/// поодиночке: объектный слой (A′) без плавающего давал девятнадцать,
/// плавающее (F) без объектного - две. `literal-default` и `primitives`
/// отвечают записью с плавающим полем и требуют обоих сразу; это и есть
/// довод, по которому список считается прогоном, а не разностью.
///
/// Четырнадцать добавил трек G - вторая форма понижения. Это ровно те
/// эффектные фикстуры корпуса, которым замыкания не нужны; мера предсказана
/// обходом узлов до реализации и прогоном подтверждена числом в число.
/// Мультишотных среди них две - `effects` и `multi-over-oneshot`, - и они же
/// критерий трека.
///
/// Ещё две добавил трек H - вектор (§4.9). Обе живут в регистре целиком, и
/// оттого достались LLVM-пути даром: объектного слоя вектору не нужно, а до
/// массива он не доходит.
///
/// Двадцать шесть добавил трек I волны 2: питомник и минимальный срез слоя
/// замыканий. Взяты они вместе не по удобству - тело `withNursery` есть
/// нульместное замыкание, и без этого среза все одиннадцать питомничных
/// упираются во второй блокиратор.
///
/// Шесть добавил трек B волны 3 - массивы (§4.11). Из десяти
/// отвергнутых массивом это те, чья ячейка плоская примитивом; у остальных
/// четырёх ячейка - **плотный агрегат**, и отказ у них теперь этот, то есть
/// трек C. `array-generic` и `flat-under-a-parameter` взяты потому, что
/// специализация (`mono`) обращает рантаймовый шаг дескриптора в константу; без
/// неё они остались бы за дескриптором укладки.
///
/// Тринадцать последних добавил трек C волны 3 - плотные агрегаты (§4.11) и
/// регионы (§3.6). Четыре из них те самые `array-*` с агрегатной ячейкой;
/// четыре - стратегии размещения (`region-strategies`,
/// `region-strategy-handled`, `region-strategy-in-io`, `functor-strategy`), и
/// это все региональные отказы, какие были. Оставшиеся три агрегатных -
/// `flat`, `flat-primitives`, `flat-sealed-member` - под снятым отказом
/// показали **дескриптор укладки**, то есть словарь `Flat a` значением; взят
/// и он.
///
/// Две последние добавил трек B волны 4 - разделяемая область (§3.6, §5.2).
/// `shared-strategies` досталась даром: операция у неё одна новая
/// (`sharedNew`), а прочие шесть те же, что у обычной области - §3.6 объявляет
/// `SharedAllocStrategy when AllocStrategy`, то есть те же члены, и расходятся
/// стратегии в `new`. `shared-workers` даром **не** досталась: захват области
/// замыканием (`spawn (worker r)`) отвергался представлением, и без него
/// разделяемая арена до воркера не доходит вовсе (см. `Repr::pointer`).
///
/// Сверяется список с прогоном **в обе стороны**: названное обязано браться, а
/// взятое - быть названным. Вторая половина стоит здесь потому, что на
/// C-стороне её отсутствие уже стоило четырёх молча потерянных имён
/// (`agreement.rs`, шапка `TAKEN`); печать списка её не заменяет - глазами её
/// никто не сверял.
const TAKEN: [&str; 107] = [
    "abortive-cleanup",
    "abortive-except",
    "alias-computation",
    "arithmetic",
    "array-aggregate",
    "array-flat",
    "array-generic",
    "array-length-word",
    "array-nested",
    "array-parametric",
    "array-tagged",
    "await-twice",
    "await-value",
    "beta-redex",
    "bitwise",
    "bitwise-widths",
    "cancel",
    "cancel-bystander",
    "case-family",
    "case-over-a-computation",
    "class-multiplicity",
    "classes",
    "comparisons",
    "countdown",
    "decidable",
    "effect-multiplicity",
    "effects",
    "erasure",
    "execution-positions",
    "existential",
    "fibers",
    "field-effect",
    "flat",
    "flat-across-a-suspension",
    "flat-fields",
    "flat-primitives",
    "flat-sealed-member",
    "flat-under-a-parameter",
    "functor",
    "functor-strategy",
    "general-frames",
    "general-order",
    "instance-context-effect",
    "interpreter",
    "label-argument",
    "label-names-its-binder",
    "lists",
    "literal-default",
    "mask",
    "module-effect",
    "module-family",
    "module-resource",
    "module-scope",
    "multi-over-oneshot",
    "mutual-family",
    "mutual-polymorphic-recursion",
    "mutual-sibling-grounded",
    "nested-case-on-a-field",
    "nested-functor",
    "nested-rowed-signature",
    "nursery",
    "nursery-abort",
    "nursery-abort-order",
    "operation-higher-order",
    "operation-lambda",
    "operation-value",
    "operators",
    "packets",
    "polymorphic-recursion",
    "prelude",
    "primitives",
    "records",
    "region-allocates-and-reads",
    "region-bound-in-the-argument",
    "region-holds-flat-payload",
    "region-strategies",
    "region-strategy-handled",
    "region-strategy-in-io",
    "resource",
    "resource-cleanup",
    "rose",
    "rows",
    "sealed-effect",
    "sequences",
    "shadowed-name",
    "shared-strategies",
    "shared-workers",
    "signature-effect",
    "signature-effect-parameterized",
    "simd-lanes",
    "simd-wrapping",
    "soa-record",
    "spawn-local",
    "state",
    "state-resource",
    "task",
    "task-handoff",
    "task-typed",
    "truncation",
    "unwind-inner-handler",
    "unwind-live-outer",
    "workload-column",
    "workload-vector",
    "workload-fbip",
    "workload-scalar",
    "workload-scalar-affine",
    "workload-symbolic",
];

/// Две нагрузки, отличающиеся **одной** строкой тела витка.
///
/// Стоят отдельно от [`TAKEN`], потому что о них утверждается своё: их ответы
/// обязаны **различаться**. Порядок здесь значим, порядок в [`TAKEN`] - нет.
const WORKLOADS: [&str; 2] = ["workload-scalar", "workload-scalar-affine"];

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

/// Ещё один угол, которого корпус не покрывает: **указательный** массив.
///
/// У массива два представления (§4.11, [`Elems`](adamas_codegen::ir::Elems)), и
/// различает их наличие `Flat` у элемента. Все семь корпусных `array-*` -
/// плоские либо плотные; указательного нет ни одного, потому что семейство с
/// одними `Flat`-полями укладывается плотно само (§10 вопрос 157). Значит три
/// точки входа рантайма - `adamas_array_fill`, `adamas_array_put`,
/// `adamas_array_take` - на LLVM-пути не исполнялись бы ни разу, а печатались
/// бы. Рекурсивное семейство плоским не бывает, и `Cell` здесь именно поэтому
/// рекурсивен - тот же ход, что у `adamas-codegen/tests/array.rs`.
///
/// Наблюдаемое - число, и зависит оно от номера ячейки: `7 + 8 + 90`.
/// Множитель у последней затем, чтобы перепутанный номер менял сумму, а не
/// переставлял слагаемые.
const POINTER_ARRAY: &str = "\
data Cell where
  Leaf : Cell
  MkCell : Int64 -> Cell -> Cell

peel : Cell -> Int64
peel Leaf = 0
peel (MkCell n rest) = n

built : Array 3 Cell
built =
  arraySet (arraySet (arrayNew 3 (MkCell 7 Leaf)) 1 (MkCell 8 Leaf)) 2
    (MkCell 9 Leaf)

read : Array 3 Cell -> Int64
read xs =
  addInt64 (peel (arrayIndex xs 0))
    (addInt64 (peel (arrayIndex xs 1)) (mulInt64 (peel (arrayIndex xs 2)) 10))

main : Int64
main = read built
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

    // Взятое обязано быть названо: иначе список усыхает молча, а мера считается
    // по меньшему корпусу. Печать ниже этого не ловит - её никто не сверяет.
    for name in &taken {
        assert!(
            TAKEN.contains(&name.as_str()),
            "{name} берётся LLVM-эмиттером, но в TAKEN не назван: список усох молча"
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
    // Взятое печатается **списком**, а не только числом: список [`TAKEN`]
    // пополняется руками, и сверять его глазами с числом нечем.
    for name in &taken {
        eprintln!("  взято {name}");
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
    let answers: Vec<String> = WORKLOADS
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
    for (name, answer) in WORKLOADS.iter().zip(&answers) {
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

/// Разбор **не** проверяет треугольник у интринсиков, и это измерено.
///
/// Свидетель выше гоняет `.ll` минимальной цепочкой до конца - объектник,
/// линковка, прогон, - и правило «консервативное подмножество IR» держится
/// ровно на этом «до конца». Здесь стоит причина, по которой короче нельзя.
///
/// Всякое имя с приставкой `llvm.`, которого версия не знает, её разбор
/// принимает как **обычную внешнюю функцию**: ни `llvm-as`, ни `opt`, ни `llc`
/// не возражают, и промах вылезает неопределённой ссылкой у компоновщика. То
/// есть проверка «прочиталось - значит совместимо» на интринсиках слепа, а на
/// необязательных флагах (`getelementptr inbounds nuw`) - нет: флаг ломает
/// разбор сразу.
///
/// Измерено это на `llvm.coro.*` - семействе, которое план Фазы 7 предлагал
/// треку G. Из тридцати шести имён, известных двадцать первой версии,
/// восемнадцатая не знает четырёх (`coro.begin.custom.abi`,
/// `coro.await.suspend.void`, `coro.await.suspend.bool`,
/// `coro.await.suspend.handle`), и все четыре её разбор принимает. Отсюда цена
/// варианта `llvm.coro.*`, названная числом, а не ощущением, - и отсюда же
/// решение трека G взять модель кадра C-бэкенда (см. шапку `emit_llvm.rs`).
///
/// Различитель известного от неизвестного - **заведомо неверная арность**:
/// известный интринсик ломает verifier, неизвестный проходит как внешняя
/// функция. Обнаружь минимальная версия эти имена - тест упадёт, и это
/// правильно: замер устарел, и решение стоит перемерить.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_reader_of_the_minimum_llvm_is_blind_to_an_unknown_intrinsic() {
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    // Имя из `llvm.coro.*`, появившееся после восемнадцатой (LLVM 19).
    let name = "llvm.coro.await.suspend.void";
    let text = format!(
        "declare void @{name}()\ndefine void @t() {{\n  call void @{name}()\n  ret void\n}}\n"
    );
    let source = harness::scratch().join("coro.probe.ll");
    std::fs::write(&source, &text).unwrap();

    let known = |chain: &adamas_codegen::llvm::Toolchain| {
        std::process::Command::new(chain.tool("llvm-as"))
            .arg(&source)
            .arg("-o")
            .arg(source.with_extension("bc"))
            .output()
            .unwrap()
            .status
            .success()
    };
    assert!(
        !known(&tools),
        "штатная цепочка приняла `{name}` с неверной арностью: различитель сломан"
    );
    assert!(
        known(&minimum),
        "минимальная цепочка знает `{name}`: замер устарел, развилку `llvm.coro.*` стоит перемерить"
    );
    eprintln!(
        "`{name}`: штатная цепочка знает, минимальная принимает как внешнюю функцию - \
         разбором этого не поймать"
    );
}

/// Программы, на которых меряются оси среза: корпусные плюс [`VERDICTS`] с
/// [`POINTER_ARRAY`].
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
    all.push(("pointer-array".to_owned(), POINTER_ARRAY.to_owned()));
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
        )
        .printed;
        assert_ne!(
            printed, honest,
            "{why}: ответ не изменился, и проверка не различает"
        );
        eprintln!("мутант «{why}»: {printed} вместо {honest}");
    }
}

/// Мутанты **объектного слоя**: сломанная правка обязана быть наблюдаема.
///
/// Сосед выше ломает скалярный путь и мерит ответом. Здесь мера шире, и это
/// требование самого слоя: половина его правок ответа не меняет вовсе. Ячейка,
/// не возвращённая куче, печатает то же число; переиспользование, подменённое
/// аллокацией, - тоже. Различает их счётчик блоков, который печатает `main.c`
/// (выдано и живо), и потому мутант здесь сверяется с **тройкой**.
///
/// Четыре правки - четыре разных пути объектного слоя.
///
/// - **Слоты конструктора.** `MkAnswer` кладёт `Int64` рядом с `UInt8`
///   (`flat-fields`, фикстура заведена ровно под это); перепутанные смещения
///   меняют оба напечатанных числа, потому что ширины у слотов разные.
/// - **Тег конструктора.** `Cons` строится тегом `Nil`; свёртка `total`
///   видит пустой список на первом же элементе.
/// - **Возврат ячейки.** Из ветви уникального убран `adamas_free`: ответ тот
///   же, живых блоков - ячейка на элемент.
/// - **Переиспользование.** `adamas_reuse` придержанной ячейки заменён на
///   `adamas_alloc`: ответ тот же, выдано больше, а придержанное некому вернуть.
///
/// Последние две - и есть свидетель того, что «собралось и напечатало» ловит
/// меньше, чем кажется: обе печатают **честное** число.
#[test]
fn a_broken_object_layer_is_observable() {
    observable(&object_mutants());
}

/// Мутанты **массива** (§4.11): перепутанный номер ячейки обязан быть виден.
///
/// Ловушка названа в шапке самой фикстуры (`eval/array-flat.adamas`): у массива
/// из трёх одинаковых чисел чтение по номеру неотличимо от чтения первой
/// ячейки, и свидетель показывал бы ноль. Ячейки поэтому различны, а у
/// последней ещё и множитель - так наблюдаем и номер, и порядок.
///
/// Четыре правки - четыре разных места массива.
///
/// - **Номер ячейки.** Чтения первой и второй переставлены: `7 + 9 + 80`
///   вместо `7 + 8 + 90`. Веса разные, поэтому перестановка меняет сумму, а не
///   переставляет слагаемые.
/// - **Запись ячейки.** `store` восьмёрки снят: ячейка остаётся заполненной
///   начальным значением, и сумма падает на единицу.
/// - **Шаг укладки.** Плоская колонка объявлена указательной (`stride` 0):
///   рантайм обрывает прогон на заполнении. Это и есть свидетель того, что шаг
///   доезжает до рантайма, а не остаётся числом в тексте.
/// - **Отданный массив.** Дроп массива после владеющего чтения снят: ответ тот
///   же, живых блоков - один. Правка эта ответом не ловится вовсе, и стоит она
///   здесь ровно поэтому.
#[test]
fn a_broken_array_is_observable() {
    observable(&array_mutants());
}

/// Правки массива: фикстура, имя, причина, что на что, чем ловится.
fn array_mutants() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    Verdict,
); 4] {
    [
        (
            "array-flat",
            "array.index",
            "перепутанный номер ячейки",
            "  %t2 = call ptr @adamas_array_at(ptr %v0, i64 1)\n  \
             %t3 = load i64, ptr %t2\n  \
             %t4 = call ptr @adamas_array_at(ptr %v0, i64 2)\n",
            "  %t2 = call ptr @adamas_array_at(ptr %v0, i64 2)\n  \
             %t3 = load i64, ptr %t2\n  \
             %t4 = call ptr @adamas_array_at(ptr %v0, i64 1)\n",
            Verdict::Answer,
        ),
        (
            "array-flat",
            "array.store",
            "потерянная запись ячейки",
            "  store i64 8, ptr %t2\n",
            "",
            Verdict::Answer,
        ),
        (
            "workload-column",
            "array.stride",
            "плоская колонка объявлена указательной",
            "call ptr @adamas_array_alloc(i64 %t0, i64 4)",
            "call ptr @adamas_array_alloc(i64 %t0, i64 0)",
            Verdict::Answer,
        ),
        (
            "array-flat",
            "array.drop",
            "неотданный массив после владеющего чтения",
            "  call void @adamas_drop(ptr %v0, ptr @adamas_release_extern)\n  \
             %t6 = mul i64 %t5, 10\n",
            "  %t6 = mul i64 %t5, 10\n",
            Verdict::Leak,
        ),
    ]
}

/// Мутанты **плотного агрегата** (§4.11) и дескриптора укладки.
///
/// Агрегат отличается от объекта кучи ровно тем, что заголовка у него нет:
/// поле адресуется смещением, тег лежит первыми байтами укладки, а не в
/// заголовке. Значит и ломаться он умеет по-своему, и все четыре правки ниже -
/// про смещение либо про тег, а не про общий объектный путь.
///
/// - **Смещение поля.** `(arrayIndex ps.pos 0).z` читается с чужого смещения:
///   `.y` вместо `.z`, то есть 2.0 вместо 3.0. У `Vec3` три поля одной ширины,
///   и различить их можно только смещением - ровно то, что проверяется.
/// - **Тег варианта при сборке.** `Some 700` собирается тегом `None`: ячейка
///   становится пустой, и сумма падает на семьсот. Наблюдаемо это потому, что
///   у фикстуры значения ячеек различны.
/// - **Смещение payload'а при разборе.** Поле варианта `Some` читается с
///   нулевого смещения, то есть поверх тега и дыры выравнивания. `Option Int64`
///   занимает шестнадцать байт именно из-за этой дыры (§4.11), и мутант
///   показывает, что дыра не декорация.
/// - **Половины дескриптора укладки.** `layout @Vec3` есть 12/4; переставь
///   половины слова - и получится 4/12. Обе половины живут в одном регистре
///   (см. [`slot`](adamas_codegen) в `emit_llvm.rs`), и перепутать их местами -
///   единственный способ ошибиться в дескрипторе, который не ломает сборку.
#[test]
fn a_broken_dense_aggregate_is_observable() {
    observable(&packed_mutants());
}

/// Правки плотного агрегата: фикстура, имя, причина, что на что, чем ловится.
fn packed_mutants() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    Verdict,
); 4] {
    [
        (
            "soa-record",
            "packed.offset",
            "поле агрегата прочитано с чужого смещения",
            "  %t9 = getelementptr i8, ptr %f0, i64 8\n",
            "  %t9 = getelementptr i8, ptr %f0, i64 4\n",
            Verdict::Answer,
        ),
        (
            "array-tagged",
            "packed.tag",
            "вариант собран чужим тегом",
            "  store i8 1, ptr %f2, align 1\n",
            "  store i8 0, ptr %f2, align 1\n",
            Verdict::Answer,
        ),
        (
            "array-tagged",
            "packed.payload",
            "payload варианта прочитан поверх тега",
            "  %t14 = getelementptr i8, ptr %f1, i64 8\n",
            "  %t14 = getelementptr i8, ptr %f1, i64 0\n",
            Verdict::Answer,
        ),
        (
            "flat-primitives",
            "packed.descriptor",
            "половины дескриптора укладки переставлены",
            "  %t0 = trunc i64 17179869196 to i32\n  \
             %t1 = lshr i64 17179869196, 32\n  \
             %t2 = trunc i64 %t1 to i32\n",
            "  %t1 = lshr i64 17179869196, 32\n  \
             %t0 = trunc i64 %t1 to i32\n  \
             %t2 = trunc i64 17179869196 to i32\n",
            Verdict::Answer,
        ),
    ]
}

/// Мутанты **региона** (§3.6): три правки, и третью ловит только счётчик.
///
/// - **LIFO подменён возвратом ячейки.** `StackAlloc.free` зовёт
///   `adamas_region_recycle` вместо `adamas_region_pop`, то есть становится
///   `Pool`. Различает их сама фикстура - у `StackAlloc` хендлы 16 и 16, у
///   `Pool` 0 и 0, - и это единственная строка, которой три стратегии §3.6
///   расходятся.
/// - **Размер нагрузки подменён её границей.** `regionAlloc` агрегата в
///   двенадцать байт при границе четыре зовётся с переставленными числами.
///   Ловушка названа в шапке фикстуры дословно: «подмена размера нагрузки её
///   границей проходила корпус целиком, пока хендл не печатался».
/// - **Чтение заимствует область вместо владения.** Перед последним
///   `adamas_region_read` встаёт лишний `adamas_dup`: рантайм отдаёт ссылку,
///   которую никто не брал, и блок области остаётся живым. Ответ при этом
///   **честный** - двадцать, 0.25, 2.0 и хендл 32, - и поймать эту правку
///   нечем, кроме счётчика живых блоков. Ради неё мутант здесь и стоит:
///   программа, печатающая верное число, ещё не значит, что область отдана.
#[test]
fn a_broken_region_is_observable() {
    observable(&region_mutants());
}

/// Правки региона: фикстура, имя, причина, что на что, чем ловится.
fn region_mutants() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    Verdict,
); 3] {
    [
        (
            "region-strategies",
            "region.pop",
            "LIFO подменён возвратом ячейки",
            "@adamas_region_pop(ptr %v0, i64 %v1)",
            "@adamas_region_recycle(ptr %v0, i64 %v1)",
            Verdict::Answer,
        ),
        (
            "region-holds-flat-payload",
            "region.stride",
            "размер нагрузки подменён её границей",
            "@adamas_region_alloc(ptr %t7, ptr %f3, i64 12, i64 4)",
            "@adamas_region_alloc(ptr %t7, ptr %f3, i64 4, i64 12)",
            Verdict::Answer,
        ),
        (
            "region-holds-flat-payload",
            "region.borrow",
            "чтение заимствует область вместо владения",
            "  call void @adamas_region_read(ptr %t14, i64 %t6, ptr %f8, i64 4, \
             ptr @adamas_release_extern)\n",
            "  %tleak = call ptr @adamas_dup(ptr %t14)\n  \
             call void @adamas_region_read(ptr %t14, i64 %t6, ptr %f8, i64 4, \
             ptr @adamas_release_extern)\n",
            Verdict::Leak,
        ),
    ]
}

/// Прогоняет список правок: каждая обязана изменить то, чем её ловят.
///
/// Общая двум свидетелям - объектного слоя и массива (§4.11), - потому что
/// вопрос у них один: правка, которую не ловит **ни** ответ, **ни** счётчик,
/// ничего и не проверяет. Вторая копия этого цикла разъехалась бы с первой
/// молча: тройка сверяется в трёх местах.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn observable(
    mutants: &[(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        Verdict,
    )],
) {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();

    for &(name, stem, why, from, to, verdict) in mutants {
        let source =
            std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
        let (honest, stderr) =
            harness::llvm_agreed(name, &source, &tools, &pipeline, &format!("{stem}.honest"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (allocated, live) = harness::blocks(name, &stderr);
        assert_eq!(live, 0, "{name}: честный прогон оставил блоки живыми");

        let artefacts = harness::llvm_text(name, &source).unwrap();
        let mutant = swapped(&artefacts.ll, from, to);
        let broken = harness::llvm_printed(
            &format!("{stem}.broken"),
            &mutant,
            &artefacts.support,
            &tools,
            &pipeline,
        );
        let differs = match verdict {
            Verdict::Answer => broken.printed != honest,
            Verdict::Leak => broken.live.is_none_or(|it| it != 0),
            Verdict::Allocations => broken.allocated.is_none_or(|it| it != allocated),
        };
        // Утечка обязана быть **невидимой ответом**: в этом весь её смысл.
        // Совпади она с расхождением ответа - и счётчик живых блоков перестал
        // бы быть единственным, что её ловит, а свидетель доказывал бы меньше,
        // чем читается.
        if matches!(verdict, Verdict::Leak) {
            assert_eq!(
                broken.printed, honest,
                "{why}: ответ разошёлся, то есть утечку ловит не только счётчик"
            );
        }
        assert!(
            differs,
            "{why}: наблюдаемое не изменилось - ответ `{}`, выдано {:?}, живо {:?}; \
             честные были `{honest}`, {allocated} и {live}",
            broken.printed, broken.allocated, broken.live
        );
        eprintln!(
            "мутант «{why}»: ответ `{}`, выдано {:?}, живо {:?} (честные `{honest}`, {allocated}, {live})",
            broken.printed, broken.allocated, broken.live
        );
    }
}

/// Чем мутант обязан отличиться. Не украшение: правка, которую ловит только
/// счётчик, ответом не ловится вовсе, и наоборот.
#[derive(Clone, Copy)]
enum Verdict {
    /// Напечатанным ответом.
    Answer,
    /// Живыми блоками в конце прогона.
    Leak,
    /// Числом выданных блоков.
    Allocations,
}

/// Правки объектного слоя: фикстура, имя, причина, что на что, чем ловится.
fn object_mutants() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    Verdict,
); 4] {
    [
        (
            "flat-fields",
            "slots",
            "перепутанные слоты конструктора",
            "  %t17 = getelementptr i8, ptr %t16, i64 8\n  \
             store i64 %t11, ptr %t17\n  \
             %t18 = getelementptr i8, ptr %t16, i64 16\n",
            "  %t17 = getelementptr i8, ptr %t16, i64 16\n  \
             store i64 %t11, ptr %t17\n  \
             %t18 = getelementptr i8, ptr %t16, i64 8\n",
            Verdict::Answer,
        ),
        (
            "workload-fbip",
            "tag",
            "перепутанный тег конструктора",
            "%t5 = call ptr @adamas_alloc(i16 1, i64 2) ; Cons",
            "%t5 = call ptr @adamas_alloc(i16 0, i64 2) ; Cons",
            Verdict::Answer,
        ),
        (
            "workload-fbip",
            "free",
            "невозвращённая ячейка разобранного",
            "s1.unique:\n  call void @adamas_free(ptr %v0)\n",
            "s1.unique:\n",
            Verdict::Leak,
        ),
        (
            "workload-fbip",
            "reuse",
            "аллокация вместо переиспользования",
            "%t10 = call ptr @adamas_reuse(ptr %t8, i16 1, i64 2) ; Cons",
            "%t10 = call ptr @adamas_alloc(i16 1, i64 2) ; Cons",
            Verdict::Allocations,
        ),
    ]
}

/// Потерянный `dup` наблюдаем: RC-трафик на объектах не декорация.
///
/// Мутант тут один на весь корпус, потому что вопрос один: **бежит** ли счёт
/// ссылок, или он только напечатан. Убираются все строки с `adamas_dup` разом -
/// значение вызова эмиттер и так не читает, поэтому IR остаётся законным, - и
/// программа, которой `dup` был нужен, обязана это заметить: ответом,
/// оборвавшимся прогоном либо счётчиком блоков.
///
/// Утверждается **существование**, а не поголовность: на нагрузке, где всякое
/// разобранное уникально, `dup` стоит в ветви разделённого и не бежит ни разу,
/// и требовать от неё расхождения значило бы требовать неверного. Список
/// заметивших печатается прогоном - усохни он, и это будет видно.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn a_lost_dup_is_observable_on_the_object_path() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let mut noticed = Vec::new();
    let mut indifferent = Vec::new();

    for name in TAKEN {
        let source =
            std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
        let artefacts = harness::llvm_text(name, &source).unwrap();
        if !artefacts.ll.contains("@adamas_dup(") {
            continue;
        }
        let (honest, stderr) =
            harness::llvm_agreed(name, &source, &tools, &pipeline, &format!("{name}.kept"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (allocated, live) = harness::blocks(name, &stderr);

        let kept: Vec<&str> = artefacts
            .ll
            .lines()
            .filter(|line| !line.contains("@adamas_dup("))
            .collect();
        let mutant = kept.join("\n");
        let broken = harness::llvm_printed(
            &format!("{name}.nodup"),
            &mutant,
            &artefacts.support,
            &tools,
            &pipeline,
        );
        if broken.printed == honest
            && broken.allocated == Some(allocated)
            && broken.live == Some(live)
        {
            indifferent.push(name);
        } else {
            noticed.push(format!(
                "{name}: `{}` вместо `{honest}`, выдано {:?} против {allocated}, живо {:?} против {live}",
                broken.printed, broken.allocated, broken.live
            ));
        }
    }

    for line in &noticed {
        eprintln!("потерянный dup заметили - {line}");
    }
    eprintln!("не заметили: {}", indifferent.join(", "));
    assert!(
        !noticed.is_empty(),
        "потерянный `dup` не заметил никто: счёт ссылок на объектах не бежит вовсе"
    );
}

/// Точки входа рантайма, которые эмиттер зовёт на объектном пути.
const RUNTIME_CALLS: [&str; 8] = [
    "adamas_con0",
    "adamas_alloc",
    "adamas_reuse",
    "adamas_free",
    "adamas_tag",
    "adamas_is_unique",
    "adamas_dup",
    "adamas_drop",
];

/// Рантайм битовым кодом: `opt` начинает видеть сквозь него (трек A′, вторая
/// половина; шов оставлен треком A, `docs/phase7-plan.md`).
///
/// Это то, без чего трек C не запускается: пока рантайм приезжает готовым
/// объектником, `adamas_dup` для оптимизатора непрозрачен, и «схлопнуть пару
/// `dup`/`drop`» не к чему применить. Проверяется **разницей**, а не наличием
/// стадии, - четвёртое правило фазы.
///
/// Утверждений три, и каждое своё.
///
/// *Ответ не меняется.* Инлайнинг рантайма - оптимизация, а не другое
/// вычисление; разойдись здесь ответ, и разошёлся бы договор трёх
/// вычислителей.
///
/// *Вызовов становится меньше, а `adamas_dup` не остаётся вовсе.* Второе
/// сильнее первого и названо отдельно: `adamas_dup` - самая маленькая функция
/// рантайма, и не инлайнься она, инлайнинга нет вовсе.
///
/// Считается это по коду, **достижимому** из [`ENTRY`], а не по модулю целиком
/// ([`harness::reachable_calls`]). Причина измерена треком B волны 3: модуль
/// после `llvm-link` несёт рантайм весь, и холодная половина, в которую
/// инлайнер намеренно ничего не вносит, делала счётчик красным на программе,
/// которая этой половины не зовёт ни разу.
///
/// *Счётчик блоков тот же.* Переиспользование ячейки обязано пережить
/// инлайнинг: `adamas_reuse` внутри цикла - то, на чём трек B меряет
/// уникальность, и растворись оно тут в `malloc`, мерить было бы нечего.
/// Метаданных трек B в итоге не поставил ни одного - почему, сказано в
/// `tests/alias.rs`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_runtime_in_bitcode_lets_the_optimiser_see_through_it() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let plain = Pipeline::optimised();
    let whole = Pipeline::whole_program(&runtime);

    for name in ["workload-fbip", "workload-symbolic", "workload-scalar"] {
        let source =
            std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
        let (apart, apart_err) =
            harness::llvm_agreed(name, &source, &tools, &plain, &format!("{name}.apart"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (together, together_err) =
            harness::llvm_agreed(name, &source, &tools, &whole, &format!("{name}.together"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(
            apart, together,
            "{name}: `llvm-link` с рантаймом изменил ответ"
        );
        assert_eq!(
            harness::blocks(name, &apart_err),
            harness::blocks(name, &together_err),
            "{name}: счётчик блоков разошёлся - переиспользование не пережило инлайнинг"
        );

        // Промежуточные файлы конвейер оставляет намеренно: считать вызовы
        // после `opt` больше негде, а до `llc` они ещё видны.
        let directory = harness::scratch();
        let before = harness::reachable_calls(
            &tools,
            &directory.join(format!("{name}.apart.opt.bc")),
            &RUNTIME_CALLS,
            ENTRY,
        );
        let after = harness::reachable_calls(
            &tools,
            &directory.join(format!("{name}.together.opt.bc")),
            &RUNTIME_CALLS,
            ENTRY,
        );
        let (was, now): (usize, usize) = (before.iter().sum(), after.iter().sum());
        eprintln!("{name}: вызовов рантайма после `-O2` было {was}, стало {now}");
        for (call, (had, has)) in RUNTIME_CALLS.iter().zip(before.iter().zip(&after)) {
            eprintln!("  @{call}: {had} -> {has}");
        }
        assert!(
            now < was,
            "{name}: рантайм приложен, а вызовов столько же ({was}) - `opt` его не видит"
        );
        let dup = RUNTIME_CALLS.iter().position(|it| *it == "adamas_dup");
        assert_eq!(
            dup.map(|at| after[at]),
            Some(0),
            "{name}: `adamas_dup` не заинлайнился, а он самый маленький в рантайме"
        );
    }
}

/// Точка входа, от которой считается достижимое: всё, что программа зовёт.
const ENTRY: &str = "adamas_entry";

/// Указательный массив идёт **указательным** путём, а не плоским.
///
/// Без этого [`POINTER_ARRAY`] был бы обманчивым свидетелем своего жанра:
/// договор трёх вычислителей он прошёл бы и в том случае, если понижение
/// втихую уложило бы `Cell` плоско, - ответ у обоих путей один по построению.
/// Различает их **какие точки входа зовутся**, и этих трёх плоский путь не
/// зовёт ни одной.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn a_pointer_array_takes_the_pointer_path() {
    let artefacts = harness::llvm_text("pointer-array", POINTER_ARRAY).unwrap();
    for entry in [
        "@adamas_array_fill(",
        "@adamas_array_put(",
        "@adamas_array_take(",
    ] {
        assert!(
            artefacts
                .ll
                .lines()
                .any(|line| line.contains("call ") && line.contains(entry)),
            "`{entry}` не зовётся: указательный массив уехал плоским путём"
        );
    }
    // И обратно: плоских обращений у него нет ни одного. По **вызову**, а не по
    // имени: объявления печатаются все семь разом, и по имени плоский путь
    // «находился» бы у любой программы с массивом.
    assert!(
        !artefacts
            .ll
            .lines()
            .any(|line| line.contains("call ") && line.contains("@adamas_array_at(")),
        "указательный массив спрашивает адрес плоской ячейки"
    );
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

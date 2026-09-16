//! Уникальность и алиасинг: что факт даёт, чего не даёт метаданное (трек B).
//!
//! Постановка трека (`docs/phase7-plan.md`, пункт B) требовала программы, где
//! FBIP-переиспользование случается **только** при выставленных метаданных, и
//! разница видна счётчиком аллокаций. Такой программы нет, и это здесь не
//! рассуждение, а два замера.
//!
//! *Счётчик метаданным не двигается.* Число выданных блоков - наблюдаемое
//! состояние, которое рантайм пишет на пути аллокации
//! (`adamas_block_alloc`), а решение «переписать или выдать» принимает `rc == 0`
//! в рантайме. Оптимизатор, меняющий это число, был бы неисправен; метаданные -
//! обещания оптимизатору. Наблюдаемую разницу даёт только **ложный** факт, и она
//! не счётчик, а обрыв прогона:
//! [`a_false_claim_of_uniqueness_is_observable`].
//!
//! *Метаданные не двигают и кода.* `noalias` на параметрах, `align 8` на слоте,
//! `inbounds` у `getelementptr` - каждое законно на своём месте и каждое даёт
//! **ноль** инструкций разницы ([`alias_metadata_earns_nothing`]). Поэтому
//! эмиттер их не ставит: правило фазы - «оптимизацию показывать разницей, а не
//! наличием», и метаданное без разницы есть гипотеза.
//!
//! *А одно из них - прямая UB.* `dereferenceable` на параметре представления
//! `Boxed` неверен, потому что нульарный конструктор непосредствен и по адресу
//! `1` читать нечего; программа падает
//! ([`dereferenceable_on_a_boxed_parameter_is_a_fault`]). Это и есть довод,
//! почему уникальность берётся у **производства**, а не там, где удобно.
//!
//! Что даёт число - сам факт: [`the_fact_pays_in_calls_and_not_in_blocks`].

mod harness;

use adamas_codegen::ir::{Program, Unique};
use adamas_codegen::llvm::{Pipeline, Toolchain};

/// Программы корпуса, на которых меряется вывод уникальности.
///
/// Те же, что берёт LLVM-путь (`tests/llvm.rs`, `TAKEN`). Список здесь свой,
/// потому что утверждение другое: там - «отвечает то же», здесь - «стоит
/// столько же и считает столько же».
const TAKEN: [&str; 21] = [
    "arithmetic",
    "case-family",
    "case-over-a-computation",
    "countdown",
    "erasure",
    "flat-fields",
    "lists",
    "literal-default",
    "module-scope",
    "mutual-family",
    "nested-case-on-a-field",
    "nested-functor",
    "operators",
    "primitives",
    "records",
    "resource-cleanup",
    "rose",
    "workload-fbip",
    "workload-scalar",
    "workload-scalar-affine",
    "workload-symbolic",
];

/// Исходник фикстуры корпуса.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
fn source(name: &str) -> String {
    std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap()
}

/// Ответ, выданное и живое у названного текста `.ll`.
fn ran(
    stem: &str,
    text: &str,
    support: &str,
    tools: &Toolchain,
    pipeline: &Pipeline,
) -> (String, Option<usize>, Option<usize>) {
    let out = harness::llvm_printed(stem, text, support, tools, pipeline);
    (out.printed, out.allocated, out.live)
}

/// Вывод уникальности платит вызовами рантайма, а не блоками.
///
/// Обе стороны замера выходят из **одной** точки - представления после вставки
/// RC ([`harness::llvm_program`]), - и различает их ровно
/// [`adamas_codegen::unique::infer`].
///
/// Утверждений три, и они разной природы.
///
/// *Ответ, выданное и живое совпадают на каждой программе.* Это проверка
/// **законности**: факт, объявленный неверно, освободил бы чужую ячейку, и
/// разошлось бы одно из трёх. Мутант ниже показывает, что разошлось бы
/// действительно.
///
/// *Вызовов `adamas_is_unique` становится меньше хоть где-то.* Иначе проход -
/// украшение, и тест обязан это назвать, а не промолчать.
///
/// *Счётчик блоков не меняется нигде.* Это и есть расхождение с постановкой
/// трека, закреплённое прогоном: она требовала разницы именно здесь.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_fact_pays_in_calls_and_not_in_blocks() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let mut saved = 0usize;
    let mut where_saved = Vec::new();

    for name in TAKEN {
        let text = source(name);
        let program = harness::llvm_program(name, &text).unwrap();
        let plain = adamas_codegen::emit_llvm::emit(&program).unwrap();
        let told =
            adamas_codegen::emit_llvm::emit(&adamas_codegen::unique::infer(program)).unwrap();

        let asked = plain.ll.matches("@adamas_is_unique(").count();
        let still = told.ll.matches("@adamas_is_unique(").count();
        assert!(
            still <= asked,
            "{name}: вопросов о уникальности стало больше - {asked} против {still}"
        );
        if still < asked {
            saved += asked - still;
            where_saved.push(format!("{name}: {asked} -> {still}"));
        }

        let before = ran(
            &format!("{name}.untold"),
            &plain.ll,
            &plain.support,
            &tools,
            &pipeline,
        );
        let after = ran(
            &format!("{name}.told"),
            &told.ll,
            &told.support,
            &tools,
            &pipeline,
        );
        assert_eq!(
            before, after,
            "{name}: вывод уникальности изменил наблюдаемое - значит факт неверен"
        );
        assert_eq!(after.2, Some(0), "{name}: прогон оставил блоки живыми");

        let was = spent(&tools, &format!("{name}.untold"));
        let then = spent(&tools, &format!("{name}.told"));
        if was != then {
            where_saved.push(format!(
                "{name}: вызовов {} -> {}, инструкций {} -> {}",
                was.0, then.0, was.1, then.1
            ));
            assert!(
                then.0 <= was.0 && then.1 <= was.1,
                "{name}: факт добавил работы - вызовов {} -> {}, инструкций {} -> {}",
                was.0,
                then.0,
                was.1,
                then.1
            );
        }
    }

    for line in &where_saved {
        eprintln!("вывод уникальности - {line}");
    }
    assert!(
        saved > 0,
        "вывод уникальности не снял ни одного вопроса: факт не читает никто"
    );
}

/// Точки входа рантайма на объектном пути: те же, что считает `tests/llvm.rs`.
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

/// Во что обошлась сборка: вызовов рантайма после `-O2` и инструкций.
///
/// Читается по промежуточным файлам, которые конвейер оставляет намеренно:
/// после `llc` вызовов уже не сосчитать, а до него не сосчитать инструкций.
fn spent(tools: &Toolchain, stem: &str) -> (usize, usize) {
    let dir = harness::scratch();
    let calls: usize = harness::calls(tools, &dir.join(format!("{stem}.opt.bc")), &RUNTIME_CALLS)
        .iter()
        .sum();
    let object = dir.join(format!("{stem}.o"));
    (calls, harness::instructions(tools, &object))
}

/// Ложно объявленная уникальность наблюдаема прогоном.
///
/// Мутант объявляет [`Unique::Certain`] у **каждого** указательного параметра,
/// не спрашивая вывода. Часть таких параметров разделена, и статическая ветвь
/// уникального забирает их ячейку: программа обязана заметить это ответом,
/// обрывом, течью либо числом выданных блоков.
///
/// Утверждается существование, а не поголовность: на программе, где всякое
/// разобранное и правда уникально, ложное объявление совпадает с истинным.
/// Список заметивших печатается прогоном.
///
/// Этот же мутант отвечает на постановку трека. Наблюдаемая разница «от
/// выставленного факта» есть ровно там, где факт **ложен**, - и это обрыв, а не
/// счётчик. Где он верен, рантайм принимает то же решение и без него.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn a_false_claim_of_uniqueness_is_observable() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let pipeline = Pipeline::optimised();
    let mut noticed = Vec::new();
    let mut indifferent = Vec::new();

    for name in TAKEN {
        let text = source(name);
        let program = harness::llvm_program(name, &text).unwrap();
        let honest =
            adamas_codegen::emit_llvm::emit(&adamas_codegen::unique::infer(program.clone()))
                .unwrap();
        let lying = adamas_codegen::emit_llvm::emit(&everything_certain(program)).unwrap();
        if lying.ll == honest.ll {
            continue;
        }

        let truth = ran(
            &format!("{name}.honest"),
            &honest.ll,
            &honest.support,
            &tools,
            &pipeline,
        );
        let lie = ran(
            &format!("{name}.lying"),
            &lying.ll,
            &lying.support,
            &tools,
            &pipeline,
        );
        if truth == lie {
            indifferent.push(name);
        } else {
            noticed.push(format!(
                "{name}: `{}`/{:?}/{:?} вместо `{}`/{:?}/{:?}",
                lie.0, lie.1, lie.2, truth.0, truth.1, truth.2
            ));
        }
    }

    for line in &noticed {
        eprintln!("ложную уникальность заметили - {line}");
    }
    eprintln!("не заметили: {}", indifferent.join(", "));
    assert!(
        !noticed.is_empty(),
        "ложное `Certain` не заметил никто: статическая ветвь ничего не решает"
    );
}

/// Объявляет уникальным каждый указательный параметр - **не спрашивая вывода**.
fn everything_certain(mut program: Program) -> Program {
    for function in &mut program.functions {
        for binding in &mut function.parameters {
            if binding.fact.present && binding.fact.repr.pointer() {
                binding.fact.unique = Unique::Certain;
            }
        }
    }
    program
}

/// Метаданные алиасинга не стоят своего места: разница в коде - ноль.
///
/// Мерится **дизассемблером**, а не текстом IR: `noalias` виден в тексте
/// всегда, и вопрос ровно в том, доехал ли он до инструкций. Прогон идёт
/// сквозной (`llvm-link` с рантаймом): без него `adamas_alloc` непрозрачен, и
/// «ничего не дало» означало бы только, что смотреть было не на что.
///
/// Три правки, и все три законны на своём месте.
///
/// - `noalias` у каждого указательного параметра. Законность спорна в общем
///   случае и потому здесь взята **максимально щедро**: если и щедрая ничего не
///   даёт, аккуратная тем более.
/// - `align 8` на чтении и записи слота. Законно безусловно: слот лежит по
///   смещению `8 + 8i` от блока `malloc`, выровненного по 16 (`adamas.h`).
/// - `inbounds` у `getelementptr`. Законно: слот внутри блока. Восемнадцатая
///   версия его читает - в отличие от `nuw` (трек A′).
///
/// Тест **упадёт**, если какая-нибудь из них начнёт давать разницу, и это
/// нужное падение: тогда её надо ставить, и мера тому будет здесь.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn alias_metadata_earns_nothing() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let pipeline = Pipeline::whole_program(&runtime);

    for name in ["workload-fbip", "workload-symbolic", "resource-cleanup"] {
        let text = source(name);
        let artefacts = harness::llvm_text(name, &text).unwrap();
        let untouched =
            harness::llvm_object(&format!("{name}.bare"), &artefacts, &tools, &pipeline);
        let base = harness::instructions(&tools, &untouched);

        for (what, marked) in [
            ("noalias", noalias(&artefacts.ll)),
            ("align 8", aligned(&artefacts.ll)),
            ("inbounds", inbounds(&artefacts.ll)),
        ] {
            assert_ne!(
                marked, artefacts.ll,
                "{name}: правка `{what}` не применилась"
            );
            let with = adamas_codegen::emit_llvm::Artefacts {
                ll: marked,
                support: artefacts.support.clone(),
            };
            let stem = format!("{name}.{}", what.replace(' ', ""));
            let object = harness::llvm_object(&stem, &with, &tools, &pipeline);
            let count = harness::instructions(&tools, &object);
            eprintln!("{name}: `{what}` - инструкций {base} против {count}");
            assert_eq!(
                count, base,
                "{name}: `{what}` изменило код - метаданное перестало быть даровым, \
                 и его надо ставить"
            );
        }
    }
}

/// `noalias` у каждого указательного параметра порождённой функции.
fn noalias(text: &str) -> String {
    text.lines()
        .map(|line| {
            if line.starts_with("define internal") {
                line.replace("(ptr %v", "(ptr noalias %v")
                    .replace(", ptr %v", ", ptr noalias %v")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `align 8` на чтении и записи слота объекта.
fn aligned(text: &str) -> String {
    text.lines()
        .map(|line| {
            let slot =
                line.contains(", ptr %t") && (line.contains("load ") || line.contains("store "));
            if slot && !line.contains("align") {
                format!("{line}, align 8")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `inbounds` у каждого `getelementptr`.
fn inbounds(text: &str) -> String {
    text.replace("getelementptr i8", "getelementptr inbounds i8")
}

/// Приговор перемерен там, где у алиасинга **есть предмет**: на памяти.
///
/// Трёх нагрузок соседнего свидетеля для этого мало, и это не придирка. FBIP
/// ходит по списку ячеек, символьная строит дерево, `resource-cleanup`
/// разбирает объект - у всех трёх обращения идут через точки входа рантайма, и
/// ни одна не делает в витке ни `load`, ни `store` по своему адресу. Колонное
/// ядро (§4.11) делает оба, и оно единственное такое в корпусе; приговор волны
/// 1 снимался без него, потому что массивов LLVM-путь тогда не брал.
///
/// Правки здесь **свои**, а не соседские, и различие не косметическое.
///
/// - `align 4`, а не `align 8`. Ячейка `Array n Float32` лежит по смещению
///   `24 + 4i` от блока: восьми байт ей никто не обещал, и соседская правка
///   была бы здесь не строгой, а **неверной**.
/// - `!tbaa` на чтении и записи ячейки - то, чего у соседа нет вовсе. Узлы
///   взяты те же, что печатает clang для рантайма (`Simple C/C++ TBAA`,
///   `float` под `omnipotent char`): `llvm-link` сводит одинаковые узлы в один,
///   и тег про `float` встаёт в то же дерево, где лежат теги про `long` полей
///   заголовка массива. Законно это потому, что ячейка плоского массива держит
///   только элементы, а `count` и `stride` - только слова.
/// - `inbounds` **не проверяется, и это названный пропуск**: у колонного ядра в
///   порождённом IR нет ни одного `getelementptr` - адрес ячейки считает
///   `adamas_array_at`. Померено оно на варианте, где адрес считает сам IR
///   (отчёт трека B волны 3): те же 153 инструкции с `inbounds` и без.
///
/// Прогон 2026-09-16: **ноль** у всех трёх, то есть приговор волны 1
/// подтверждается и на памяти. Причина видна в оптимизированном IR: холодная
/// половина `adamas_array_writable` зовётся **из витка**, и для `opt` этот
/// вызов пишет куда угодно - ни `noalias`, ни тег типа его не ограничивают.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn alias_metadata_earns_nothing_on_memory_either() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let pipeline = Pipeline::whole_program(&runtime);

    let name = "workload-column";
    let text = source(name);
    let artefacts = harness::llvm_text(name, &text).unwrap();
    // По инструкции, а не по слову: слово `getelementptr` стоит и в шапке
    // порождённого текста, где оно описывает правило, а не адрес.
    assert!(
        !artefacts.ll.contains("= getelementptr"),
        "у колонного ядра появился `getelementptr`: `inbounds` стало что мерить, \
         и пропуск выше перестал быть названным"
    );
    let untouched = harness::llvm_object(&format!("{name}.bare"), &artefacts, &tools, &pipeline);
    let base = harness::instructions(&tools, &untouched);

    for (what, marked) in [
        ("noalias", noalias(&artefacts.ll)),
        ("align 4", cells_aligned(&artefacts.ll)),
        ("tbaa", cells_typed(&artefacts.ll)),
    ] {
        assert_ne!(
            marked, artefacts.ll,
            "{name}: правка `{what}` не применилась"
        );
        let with = adamas_codegen::emit_llvm::Artefacts {
            ll: marked,
            support: artefacts.support.clone(),
        };
        let stem = format!("{name}.{}", what.replace(' ', ""));
        let object = harness::llvm_object(&stem, &with, &tools, &pipeline);
        let count = harness::instructions(&tools, &object);
        eprintln!("{name}: `{what}` - инструкций {base} против {count}");
        assert_eq!(
            count, base,
            "{name}: `{what}` изменило код - метаданное перестало быть даровым на \
             памяти, и его надо ставить"
        );
    }

    // Положительный контроль: прежде чем поверить трём нулям, надо знать, что
    // счётчик вообще двигается на **этой** программе. Двигает его не
    // метаданное, а другая форма адресации ячейки - и это же есть названная
    // числом возможность, оставленная следующему треку.
    assert!(
        artefacts
            .ll
            .lines()
            .filter(|line| line.contains("call ptr @adamas_array_alloc("))
            .all(|line| line.trim_end().ends_with(", i64 4)")),
        "{name}: шаг колонки не четыре байта - контроль считает адрес не тем шагом"
    );
    let addressed = adamas_codegen::emit_llvm::Artefacts {
        ll: cells_addressed(&artefacts.ll),
        support: artefacts.support.clone(),
    };
    let object = harness::llvm_object(&format!("{name}.addressed"), &addressed, &tools, &pipeline);
    let count = harness::instructions(&tools, &object);
    eprintln!("{name}: контроль (адрес считает сам IR) - инструкций {base} против {count}");
    assert!(
        count < base,
        "{name}: контроль не изменил кода - значит и три нуля выше ничего не значат"
    );
    // И он обязан считать то же: форма другая, ответ тот же, блок тот же.
    let honest = ran(
        &format!("{name}.plain"),
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    let control = ran(
        &format!("{name}.control"),
        &addressed.ll,
        &addressed.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        honest, control,
        "{name}: контроль посчитал не то - сравнивать было бы нечего"
    );
}

/// Адрес ячейки, посчитанный **самим IR**: шаг константой, граница по месту.
///
/// Не кандидат на эмиссию, а мера возможности, и мера эта снята треком B волны
/// 3 Фазы 7 на колонке в 8 388 608 ячеек: **1.233 раза** (82.3 против 66.7 мс,
/// пять блоков чередованием, размах отношения 0.011). Разница вся в том, что
/// `adamas_array_at` непрозрачен для `opt`: за ним прячутся чтение `stride` из
/// заголовка, проверка `stride != 0` и умножение на рантаймовое число - по два
/// комплекта на виток, потому что обращений к ячейке в витке два.
///
/// Почему это не сделано здесь же: эмиттеру пришлось бы знать раскладку
/// заголовка массива (длина по смещению 8, нагрузка с 24) и текст обрыва по
/// выходу за длину - то есть завести вторую копию того и другого. У слота
/// объекта такая копия есть и стережётся `_Static_assert` в спутнике; у массива
/// её пришлось бы заводить, и это решение, а не следствие.
fn cells_addressed(text: &str) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut at = 0_u32;
    for line in text.lines() {
        let taken = line
            .trim_start()
            .strip_prefix('%')
            .and_then(|rest| rest.split_once(" = call ptr @adamas_array_at(ptr "))
            .and_then(|(name, rest)| {
                let (array, rest) = rest.split_once(", i64 ")?;
                Some((name, array, rest.strip_suffix(')')?))
            });
        let Some((name, array, index)) = taken else {
            out.push(line.to_owned());
            continue;
        };
        at += 1;
        out.push(format!("  %c{at}.p = getelementptr i8, ptr {array}, i64 8"));
        out.push(format!("  %c{at}.n = load i64, ptr %c{at}.p"));
        out.push(format!("  %c{at}.ok = icmp ult i64 {index}, %c{at}.n"));
        out.push(format!(
            "  br i1 %c{at}.ok, label %cell{at}.in, label %cell{at}.out"
        ));
        out.push(String::new());
        out.push(format!("cell{at}.out:"));
        out.push("  call void @adamas_fail(ptr @.str.tag)".to_owned());
        out.push("  unreachable".to_owned());
        out.push(String::new());
        out.push(format!("cell{at}.in:"));
        out.push(format!("  %c{at}.off = mul i64 {index}, 4"));
        out.push(format!(
            "  %c{at}.pay = getelementptr i8, ptr {array}, i64 24"
        ));
        out.push(format!(
            "  %{name} = getelementptr i8, ptr %c{at}.pay, i64 %c{at}.off"
        ));
    }
    out.join("\n")
}

/// Строки чтения и записи **ячейки массива**: плоское значение по указателю.
///
/// Узнаются по типу: слот объекта носит `i64` и `ptr`, ячейка - тип элемента.
fn cell(line: &str) -> bool {
    let trimmed = line.trim_start();
    (trimmed.contains("= load ") || trimmed.starts_with("store "))
        && trimmed.contains(", ptr %t")
        && !trimmed.contains(" i64 ")
        && !trimmed.contains(" ptr ")
}

/// `align 4` на ячейке колонки `Float32`.
fn cells_aligned(text: &str) -> String {
    text.lines()
        .map(|line| {
            if cell(line) && !line.contains("align") {
                format!("{line}, align 4")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Тег типа на ячейке: `float` против слов заголовка.
fn cells_typed(text: &str) -> String {
    let mut out: Vec<String> = text
        .lines()
        .map(|line| {
            if cell(line) {
                format!("{line}, !tbaa !9003")
            } else {
                line.to_owned()
            }
        })
        .collect();
    out.push(String::new());
    out.push("!9000 = !{!\"Simple C/C++ TBAA\"}".to_owned());
    out.push("!9001 = !{!\"omnipotent char\", !9000, i64 0}".to_owned());
    out.push("!9002 = !{!\"float\", !9001, i64 0}".to_owned());
    out.push("!9003 = !{!9002, !9002, i64 0}".to_owned());
    out.join("\n")
}

/// `dereferenceable` на параметре представления `Boxed` роняет прогон.
///
/// Довод законности `dereferenceable` и `align` записан в `adamas.h` прямо:
/// ставить их можно только там, где `adamas_is_imm` уже дал ложь. Параметр
/// [`Repr::Boxed`](adamas_codegen::ir::Repr) такой ветвью не является -
/// нульарный конструктор непосредствен, `Nil` приезжает значением `1`, - и
/// обещание «по этому адресу читаемо 24 байта» разрешает оптимизатору поднять
/// чтение тега **до** проверки на непосредственность.
///
/// Свидетель предъявляет это прогоном, а не рассуждением: тот же `.ll` с одним
/// дописанным словом печатает не ответ, а падает. Это и есть та программа,
/// которая упала бы, будь довод уникальности неверен, - здесь довод неверен
/// нарочно.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn dereferenceable_on_a_boxed_parameter_is_a_fault() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let pipeline = Pipeline::whole_program(&runtime);
    let name = "workload-fbip";
    let text = source(name);
    let artefacts = harness::llvm_text(name, &text).unwrap();

    let honest = ran(
        &format!("{name}.plainly"),
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_eq!(
        honest.2,
        Some(0),
        "{name}: честный прогон оставил блоки живыми"
    );

    let promised = artefacts
        .ll
        .replace("@fn_6(ptr %v0", "@fn_6(ptr dereferenceable(24) align 8 %v0");
    assert_ne!(promised, artefacts.ll, "{name}: обещание не дописалось");
    let broken = ran(
        &format!("{name}.promised"),
        &promised,
        &artefacts.support,
        &tools,
        &pipeline,
    );
    assert_ne!(
        broken.0, honest.0,
        "{name}: `dereferenceable` на `Boxed` прошёл незамеченным - \
         значит непосредственное значение сюда не доезжает, и довод надо перемерить"
    );
    eprintln!(
        "`dereferenceable(24)` на параметре `Boxed`: `{}` вместо `{}`",
        broken.0, honest.0
    );
}

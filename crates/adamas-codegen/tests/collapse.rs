//! Схлопывание пары `dup`/`drop` после инлайнинга (§9 Фаза 7, волна 1, трек C).
//!
//! Критерий трека — расхождение, а не наличие: пар `dup`/`drop` в горячей
//! функции после прохода обязано стать меньше, чем до него, **и** на той же
//! программе C-бэкенд обязан пару сохранить. Второе условие и есть смысл трека:
//! схлопнись пара и на C, её схлопнул бы [`perceus`](adamas_codegen::perceus), а
//! проход не показал бы ничего.
//!
//! # Почему на C-бэкенде та же пара остаётся
//!
//! Утверждение здесь двухэтажное, и этажи проверяются порознь.
//!
//! *Perceus её не видит — по построению.* Проход идёт по функциям поодиночке, а
//! пара разделена границей вызова. Меряется это **тем же** инструментом, что и
//! схлопывание: на выходе эмиттера (то есть на выходе Perceus, ещё до
//! инлайнинга) проход снимает **ноль** пар, а после `opt -O2` — одну. Оба
//! бэкенда читают один и тот же выход Perceus, поэтому число «ноль» относится к
//! обоим.
//!
//! *Цепочка C её тоже не снимает.* Проверяется дизассемблером на собранном
//! бинаре, четырьмя сборками — `-O1`, `-O2`, `-O2 -flto`, `-O3 -flto`, — и
//! рантайм в каждой собран **теми же ключами**. Оба условия нужны. Без уровней
//! сравнение отладочной сборки одной стороны с release другой — ровно тот жанр
//! стенда, который печатает перевёрнутое отношение в формате настоящего замера;
//! без рантайма в тех же ключах `-flto` не видел бы его вовсе, и «пара
//! осталась» ничего бы не значило.
//!
//! Что при этом измерено (2026-09-15, gcc 15.3): на `-O2 -flto` цепочка C
//! `adamas_dup` **инлайнит** — в витке остаётся `addl $0x1,(%rbx)`, — а
//! `adamas_drop` не инлайнит, он остаётся вызовом. То есть пара цела, и счётчик,
//! искавший её по имени вызова, ответил бы «пары нет».
//!
//! # Чем меряется «пар стало меньше»
//!
//! Двумя числами на двух срезах, и оба нужны.
//!
//! *Вызовы.* Сразу после инлайнинга (`opt -O2 -S`, рантайм ещё непрозрачен)
//! пара видна двумя вызовами — `@adamas_dup` и `@adamas_drop`. Это тот срез, на
//! котором работает сам проход.
//!
//! *Трафик счётчика.* После `llvm-link` с рантаймом и второй `opt` от пары
//! остаются чтения и записи `i32` по заголовку объекта. Ширина здесь и есть
//! признак: в заголовке (`adamas.h`) `rc` занимает 32 бита, `tag` и `flags` —
//! по 16, слот — 64, счётчики блоков — 64. То есть `load i32`/`store i32` в
//! горячей функции — счётчик ссылок и ничего больше.
//!
//! # Ошибка этого прохода ответом не видна
//!
//! Снятая лишняя пара и снятая **нужная** дают одно и то же напечатанное число.
//! Поэтому всякий свидетель здесь сверяет тройку — ответ, выдано, живо, — а у
//! прохода есть мутант ([`Between::Ignored`]), снимающий пару, которую снимать
//! нельзя. Он обязан ронять прогон, и роняет.

mod harness;

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use adamas_codegen::collapse::{Between, collapse, reckless, watched};
use adamas_codegen::llvm::{MINIMUM_TOOLS_VARIABLE, Pass, Pipeline, Toolchain};

/// Свидетель схлопывания: пара рождена инлайнингом и снимается.
///
/// Устроен так, чтобы каждая черта была нужна.
///
/// *`weigh` не называет аргумент вовсе.* Отсюда `drop` на входе в неё — самая
/// короткая форма «вызываемый отдаёт владение», без разбора и без ветвления.
///
/// *`xs` в витке употреблён дважды* — рекурсивным вызовом и `weigh`. Отсюда
/// `dup` у вызывающего. Обе половины законны порознь и избыточны вместе.
///
/// *Накопитель нелинеен по витку.* `acc·3 + weigh xs` цепочкой в тысячу витков
/// не сворачивается, и виток переживает оптимизацию: иначе «пар стало меньше»
/// читалось бы как «функции не стало».
const COLLAPSING: &str = "\
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

weigh : List -> Int64
weigh xs = 7

loop : Int64 -> List -> Int64 -> Int64
loop 0 xs acc = acc
loop n xs acc = loop (subInt64 n 1) xs (addInt64 (mulInt64 acc 3) (weigh xs))

main : Int64
main = loop 1000 (build 16 Nil) 0
";

/// Свидетель отказа: пара, которую снимать нельзя.
///
/// Отличается от соседа одним: `second` разбирает ячейку и **берёт** её
/// боксированное поле, поэтому дроп разобранного схлопнут (§5.1) и спрашивает
/// `adamas_is_unique`. Ответ на этот вопрос `dup` вызывающего и меняет: с ним
/// ячейка разделена, без него — уникальна и подлежит освобождению. Снять пару
/// здесь значит освободить список, которым виток ещё владеет.
const GUARDED: &str = "\
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

headOf : List -> Int64
headOf Nil = 0
headOf (Cons y ys) = y

second : List -> Int64
second Nil = 0
second (Cons x xs) = headOf xs

loop : Int64 -> List -> Int64 -> Int64
loop 0 xs acc = acc
loop n xs acc = loop (subInt64 n 1) xs (addInt64 (mulInt64 acc 3) (second xs))

main : Int64
main = loop 1000 (build 16 Nil) 0
";

/// Тот же свидетель на **разных** объектах: пара приходится на свою ячейку.
///
/// Нужен замеру времени, а не счёту пар. У [`COLLAPSING`] `dup` и `drop` всякий
/// виток бьют в одно и то же слово, всегда горячее; здесь виток идёт по списку,
/// и пара приходится на ту ячейку, которую разбор и без того читает.
const WALK: &str = "\
data Bool where
  True : Bool
  False : Bool

data List where
  Nil : List
  Cons : Int64 -> List -> List

build : Int64 -> List -> List
build 0 xs = xs
build n xs = build (subInt64 n 1) (Cons n xs)

weigh : List -> Int64
weigh xs = 7

walk : List -> Int64 -> Int64
walk Nil acc = acc
walk (Cons x xs) acc =
  let a : Int64 = addInt64 (weigh xs) (weigh xs)
  let b : Int64 = addInt64 (weigh xs) (weigh xs)
  walk xs (addInt64 acc (addInt64 x (addInt64 a b)))

main : Int64
main = walk (build 16 Nil) 0
";

/// Горячая функция: после инлайнинга программа целиком лежит в точке входа.
const HOT: &str = "adamas_entry";

/// Корпусные программы, на которых проход меряется сверх свидетелей.
///
/// Четыре из двадцати одной, и выбраны не наугад: три — нагрузки трека Z, на
/// которых A′ мерил инлайнинг рантайма, четвёртая — ближайшая к ним по форме
/// (разбор с полями в ветви). Остальной корпус проходит договором ниже.
const WORKLOADS: [&str; 4] = [
    "workload-fbip",
    "workload-symbolic",
    "workload-scalar",
    "rose",
];

/// Пара, рождённая инлайнингом, снимается на LLVM и остаётся на C.
///
/// Три утверждения, и порядок их не случаен: сперва «Perceus её не снял» —
/// иначе мерить было бы нечего, — потом «цепочка C её не снимает тоже», и
/// только потом «а LLVM-проход снимает».
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_pair_the_inliner_creates_is_taken_only_on_the_llvm_path() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };

    let artefacts = harness::llvm_text("collapsing", COLLAPSING).unwrap();

    // До инлайнинга снимать нечего, и это меряется **тем же** инструментом,
    // что и после: пара разделена границей вызова, а проход дальше своей
    // функции не смотрит. Perceus не смотрит тоже - он идёт по функциям
    // поодиночке, - и этот же выход эмиттера построен на его выходе.
    let (_, apart) = collapse(&artefacts.ll, Between::Watched);
    assert_eq!(
        apart.cancelled, 0,
        "пара нашлась до инлайнинга: свидетель не о том, что заявлено"
    );
    assert!(
        apart.dups > 0 && apart.drops > 0,
        "в порождённом IR нет ни `dup`, ни `drop`: мерить нечего"
    );

    // После инлайнинга - есть.
    let probe = harness::llvm_object(
        "collapsing.probe",
        &artefacts,
        &tools,
        &Pipeline::portable(None),
    );
    let before =
        std::fs::read_to_string(probe.with_file_name("collapsing.probe.inlined.ll")).unwrap();
    let (after, report) = collapse(&before, Between::Watched);

    let was = calls(hot(&before), "@adamas_dup(") + calls(hot(&before), "@adamas_drop(");
    let now = calls(hot(&after), "@adamas_dup(") + calls(hot(&after), "@adamas_drop(");
    eprintln!(
        "LLVM: до инлайнинга снято {} пар, после - {}; в `{HOT}` вызовов dup/drop \
         было {was}, стало {now}",
        apart.cancelled, report.cancelled
    );
    assert_eq!(report.cancelled, 1, "пара не снята: мерить нечего");
    assert_eq!(now, was - 2, "снялись не обе половины пары");
    assert_eq!(calls(hot(&after), "@adamas_dup("), 0, "`dup` остался");

    // Цепочка C: та же программа, четыре сборки. Рантайм собирается **теми же
    // ключами**, что и программа, - иначе межмодульная сборка была бы
    // вывеской: `-flto` не видит объектников, собранных без него, и «пара
    // осталась» ничего бы не значило.
    let text = harness::text(COLLAPSING).unwrap();
    let mut kept = Vec::new();
    for keys in [
        vec!["-O1"],
        vec!["-O2"],
        vec!["-O2", "-flto"],
        vec!["-O3", "-flto"],
    ] {
        let name = format!("collapsing.c{}", keys.join("").replace('-', ""));
        let binary = built_whole(&name, &text, &keys);
        let run = Command::new(&binary).output().unwrap();
        assert!(run.status.success(), "C {keys:?}: прогон оборвался");
        assert_eq!(
            String::from_utf8_lossy(&run.stdout).trim_end_matches('\n'),
            harness::printed(COLLAPSING),
            "C {keys:?}: посчиталось не то, что у машины"
        );
        let (dups, drops) = rc_traffic(&binary);
        eprintln!("C-бэкенд {keys:?}: в понижении взятий ссылки {dups}, отдач {drops}");
        kept.push((dups, drops));
    }
    assert!(
        kept.iter().all(|(dups, drops)| *dups > 0 && *drops > 0),
        "C-бэкенд снял пару сам: {kept:?} - тогда схлопывать было нечего и без него"
    );
}

/// Сколько пар проход находит на корпусе. Мера печатается, а не пишется руками.
///
/// Здесь не утверждение, а число: корпус собирался под другие вопросы, и пар,
/// разделённых границей вызова **в горячем витке**, в нём может не быть вовсе.
/// Утверждается ровно одно - что проход ничего не снимает **сверх** найденного,
/// то есть отказы не молчат.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_corpus_says_how_many_pairs_the_pass_finds() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let mut found = Vec::new();
    for name in taken() {
        let source =
            std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
        let artefacts = harness::llvm_text(&name, &source).unwrap();
        let probe = harness::llvm_object(
            &format!("{name}.count"),
            &artefacts,
            &tools,
            &Pipeline::portable(None),
        );
        let inlined =
            std::fs::read_to_string(probe.with_file_name(format!("{name}.count.inlined.ll")))
                .unwrap();
        let (_, report) = collapse(&inlined, Between::Watched);
        eprintln!(
            "{name}: dup {}, drop {}, снято {}, отказано {}",
            report.dups, report.drops, report.cancelled, report.refused
        );
        if report.cancelled > 0 {
            found.push(format!("{name} ({})", report.cancelled));
        }
    }
    eprintln!(
        "корпус: пары нашлись у {}",
        if found.is_empty() {
            "никого".to_owned()
        } else {
            found.join(", ")
        }
    );
}

/// Ответ и счётчик блоков проход не трогает - ни на свидетелях, ни на корпусе.
///
/// Требование сильнее «ответ тот же»: снятая **нужная** пара печатает тот же
/// ответ, и различает её счётчик живых блоков. Поэтому сверяется тройка.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_pass_keeps_the_answer_and_the_blocks() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let without = Pipeline::collapsing(&runtime, None);
    let with = Pipeline::collapsing(&runtime, Some(watched));

    let mut sources: Vec<(String, String)> = vec![
        ("collapsing".to_owned(), COLLAPSING.to_owned()),
        ("guarded".to_owned(), GUARDED.to_owned()),
    ];
    for name in taken() {
        let path = harness::corpus().join(format!("{name}.adamas"));
        sources.push((name, std::fs::read_to_string(path).unwrap()));
    }

    for (name, source) in sources {
        let (plain, plain_err) =
            harness::llvm_agreed(&name, &source, &tools, &without, &format!("{name}.plain"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        let (kept, kept_err) =
            harness::llvm_agreed(&name, &source, &tools, &with, &format!("{name}.kept"))
                .unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_eq!(plain, kept, "{name}: проход изменил ответ");
        assert_eq!(
            harness::blocks(&name, &plain_err),
            harness::blocks(&name, &kept_err),
            "{name}: проход сдвинул счётчик блоков"
        );
        let (_, live) = harness::blocks(&name, &kept_err);
        assert_eq!(live, 0, "{name}: после прохода остались живые блоки");
    }
}

/// Снятая пара исчезает и из трафика счётчика - то есть доезжает до кода.
///
/// Сосед выше мерит срез, на котором работает проход. Здесь мера дальняя: после
/// `llvm-link` и второй `opt` пара, если её не снять, превращается в чтение,
/// сложение, запись и развилку по `rc` **внутри витка**. Снятая - не
/// превращается ни во что.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_counter_traffic_shrinks_by_what_the_pass_took() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let without = Pipeline::collapsing(&runtime, None);
    let with = Pipeline::collapsing(&runtime, Some(watched));

    let mut moved = Vec::new();
    let mut sources: Vec<(String, String)> = vec![("collapsing".to_owned(), COLLAPSING.to_owned())];
    for name in WORKLOADS {
        let path = harness::corpus().join(format!("{name}.adamas"));
        sources.push((name.to_owned(), std::fs::read_to_string(path).unwrap()));
    }

    for (name, source) in sources {
        let artefacts = harness::llvm_text(&name, &source).unwrap();
        let plain = harness::llvm_object(&format!("{name}.t0"), &artefacts, &tools, &without);
        let kept = harness::llvm_object(&format!("{name}.t1"), &artefacts, &tools, &with);
        let was = traffic(&tools, &plain.with_file_name(format!("{name}.t0.opt.bc")));
        let now = traffic(&tools, &kept.with_file_name(format!("{name}.t1.opt.bc")));
        eprintln!(
            "{name}: в `{HOT}` счётчик читался {} раз и писался {}, стало {} и {}",
            was.0, was.1, now.0, now.1
        );
        if now < was {
            moved.push(name);
        }
    }
    assert!(
        !moved.is_empty(),
        "трафик счётчика не сдвинулся нигде: проход до кода не доезжает"
    );
    eprintln!("трафик счётчика убавился на: {}", moved.join(", "));
}

/// Мутант: проход без проверки середины снимает нужную пару и роняет прогон.
///
/// Здесь и проверяется, что осторожность прохода - не украшение. На [`GUARDED`]
/// между `dup` и `drop` стоит `adamas_is_unique`, ответ на который `dup` и
/// меняет; сняв пару, наивный проход отвечает «уникальна» о ячейке, которой
/// виток ещё владеет, и освобождает её.
///
/// Утверждений три. Осторожный проход пару **видит и отказывается** снимать
/// (иначе он был бы прав случайно); наивный её снимает; прогон наивной сборки
/// обязан разойтись с честной - ответом, счётчиком либо обрывом.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_pair_that_guards_uniqueness_is_refused_and_the_mutant_falls() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let artefacts = harness::llvm_text("guarded", GUARDED).unwrap();
    let probe = harness::llvm_object(
        "guarded.probe",
        &artefacts,
        &tools,
        &Pipeline::portable(None),
    );
    let inlined =
        std::fs::read_to_string(probe.with_file_name("guarded.probe.inlined.ll")).unwrap();

    let (_, careful) = collapse(&inlined, Between::Watched);
    let (_, naive) = collapse(&inlined, Between::Ignored);
    assert_eq!(careful.cancelled, 0, "осторожный проход снял нужную пару");
    assert!(
        careful.refused > 0,
        "осторожный проход пары не увидел вовсе: он прав случайно, а не по делу"
    );
    assert!(
        naive.cancelled > 0,
        "наивный проход пары не снял: мутанта нет"
    );
    let guard = between(&inlined, "@adamas_dup(", "@adamas_drop(");
    eprintln!(
        "между парой стоит: {guard}; осторожно снято {}, отказано {}; наивно снято {}",
        careful.cancelled, careful.refused, naive.cancelled
    );
    assert!(
        guard.contains("adamas_is_unique"),
        "между парой нет `adamas_is_unique`: мутант ломал бы не то"
    );

    // Прогон. Рантайм - объектником, чтобы мутант падал на своём, а не на
    // дублирующихся определениях.
    let honest = harness::llvm_printed(
        "guarded.honest",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &Pipeline::portable(Some(watched)),
    );
    let broken = harness::llvm_printed(
        "guarded.reckless",
        &artefacts.ll,
        &artefacts.support,
        &tools,
        &Pipeline::portable(Some(reckless)),
    );
    eprintln!(
        "честно: `{}`, выдано {:?}, живо {:?}",
        honest.printed, honest.allocated, honest.live
    );
    eprintln!(
        "мутант: `{}`, выдано {:?}, живо {:?}",
        broken.printed, broken.allocated, broken.live
    );
    assert_eq!(
        honest.printed,
        harness::printed(GUARDED),
        "честная сборка посчитала не то, что машина"
    );
    assert!(
        broken.printed != honest.printed
            || broken.allocated != honest.allocated
            || broken.live != honest.live,
        "мутант ничем не отличился: проверка не различает осторожный проход от наивного"
    );
}

/// Минимальная версия LLVM проходит тот же конвейер и снимает то же.
///
/// Правило консервативного подмножества приложено к тому, что трек добавил в
/// конвейер. Проход версии не знает - он не линкуется с LLVM, - но текст ему
/// приносит `opt`, и вот это уже версия. Проверяется прогоном, а не доводом.
///
/// Рантайм здесь объектником ([`Pipeline::portable`]), а не битовым кодом: `.bc`
/// собран clang'ом 21-й и восемнадцатой не читается вовсе. Треку этого
/// довольно, и это само по себе находка - см. шапку плана.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
#[test]
fn the_minimum_llvm_collapses_the_same_pair() {
    let Some((tools, minimum)) = harness::llvm_toolchains() else {
        return;
    };
    let current = tools.major().unwrap();
    let oldest = minimum.major().unwrap_or_else(|error| {
        panic!("минимальная цепочка (`{MINIMUM_TOOLS_VARIABLE}`): {error}")
    });
    eprintln!("штатная LLVM {current}, минимальная {oldest}");

    let mut answers = Vec::new();
    for (chain, version) in [(&tools, current), (&minimum, oldest)] {
        let artefacts = harness::llvm_text("collapsing", COLLAPSING).unwrap();
        let probe = harness::llvm_object(
            &format!("collapsing.v{version}"),
            &artefacts,
            chain,
            &Pipeline::portable(None),
        );
        let inlined = std::fs::read_to_string(
            probe.with_file_name(format!("collapsing.v{version}.inlined.ll")),
        )
        .unwrap();
        let (_, report) = collapse(&inlined, Between::Watched);
        eprintln!("LLVM {version}: снято пар {}", report.cancelled);
        assert_eq!(report.cancelled, 1, "LLVM {version}: пара не снялась");

        let (printed, stderr) = harness::llvm_built(
            &format!("collapsing.run{version}"),
            &artefacts,
            chain,
            &Pipeline::portable(Some(watched)),
        );
        let printed = printed.trim_end_matches('\n').to_owned();
        assert_eq!(
            harness::blocks("collapsing", &stderr).1,
            0,
            "LLVM {version}: остались живые блоки"
        );
        answers.push(printed);
    }
    assert_eq!(
        answers[0], answers[1],
        "минимальная LLVM со схлопыванием посчитала не то"
    );
    assert_eq!(
        answers[0],
        harness::printed(COLLAPSING),
        "со схлопыванием посчиталось не то, что у машины"
    );
}

/// Программы, которые LLVM-эмиттер берёт: список ведёт `tests/llvm.rs`.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
fn taken() -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(harness::corpus())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .map(|path| path.file_stem().unwrap().to_string_lossy().into_owned())
        .filter(|name| {
            let source =
                std::fs::read_to_string(harness::corpus().join(format!("{name}.adamas"))).unwrap();
            harness::llvm_text(name, &source).is_ok()
        })
        .collect();
    names.sort();
    names
}

/// Тело горячей функции в тексте `.ll`.
fn hot(text: &str) -> &str {
    let Some(at) = text.find(&format!("define i64 @{HOT}(")) else {
        return "";
    };
    let rest = &text[at..];
    let end = rest.find("\n}").map_or(rest.len(), |it| it + 2);
    &rest[..end]
}

/// Сколько раз текст зовёт названную точку входа.
fn calls(text: &str, needle: &str) -> usize {
    text.lines()
        .filter(|line| line.contains("call ") && line.contains(needle))
        .count()
}

/// Чтений и записей счётчика в горячей функции слинкованного модуля.
///
/// Ширина здесь и есть признак: `rc` в заголовке - единственное 32-битное поле
/// (`adamas.h`), tag и flags по 16, слоты и счётчики блоков по 64.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn traffic(tools: &Toolchain, bitcode: &Path) -> (usize, usize) {
    let text = bitcode.with_extension("shown.ll");
    let shown = Command::new(tools.tool("llvm-dis"))
        .arg(bitcode)
        .arg("-o")
        .arg(&text)
        .output()
        .unwrap();
    assert!(
        shown.status.success(),
        "`{}` не разобрался обратно",
        bitcode.display()
    );
    let read = std::fs::read_to_string(&text).unwrap();
    let body = hot(&read);
    let reads = body
        .lines()
        .filter(|line| line.contains(" = load i32, ptr "))
        .count();
    let writes = body
        .lines()
        .filter(|line| line.trim_start().starts_with("store i32 "))
        .count();
    (reads, writes)
}

/// Собирает порождённый C **вместе с исходниками рантайма**, одной командой.
///
/// Не [`harness::built_with`]: тот прикладывает объектники рантайма, собранные
/// однажды и без наших ключей, и `-flto` через них не проходит вовсе. Вопрос
/// трека - схлопывает ли пару цепочка C, когда ей дано всё, - и задать его
/// можно только сборкой, у которой рантайм в тех же ключах.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn built_whole(name: &str, text: &str, keys: &[&str]) -> std::path::PathBuf {
    let dir = harness::scratch();
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();
    let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let mut compile = Command::new(env!("ADAMAS_CC"));
    compile
        .args(["-std=c11", "-ffp-contract=off", "-w"])
        .args(keys)
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source);
    for unit in env!("ADAMAS_RUNTIME_UNITS").split(',') {
        compile.arg(sources.join(unit));
    }
    let made = compile.arg("-o").arg(&binary).output().unwrap();
    assert!(
        made.status.success(),
        "{name}: C с рантаймом не собрался:\n{}",
        String::from_utf8_lossy(&made.stderr)
    );
    binary
}

/// RC-трафик в **нашем** коде собранного бинаря: взятий ссылки и отдач.
///
/// Дизассемблером, а не по тексту C: вопрос здесь не «что написал эмиттер», а
/// «что осталось после компилятора».
///
/// Смотрятся функции понижения (`fn_*`) и `main`: при `-O1` виток лежит в
/// `fn_1`, при `-O2` gcc складывает программу целиком в `main`, и счётчик,
/// выбравший одно из двух, на другом уровне показал бы ноль. Тела рантайма не
/// в счёт - RC-трафик внутри `adamas_drop` есть сам `adamas_drop`.
///
/// Взятие ссылки считается **в двух формах**: вызовом `adamas_dup` и тем, во
/// что он превращается заинлайненным, - инкрементом слова по указателю. Без
/// второй формы межмодульная сборка ответила бы «пары нет», хотя пара есть:
/// измерено 2026-09-15, `-flto` над рантаймом инлайнит `adamas_dup` (`addl
/// $0x1,(%rbx)` в витке) и **не** инлайнит `adamas_drop` - тот остаётся
/// вызовом. То есть пара цела, а счётчик по имени её бы не нашёл.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn rc_traffic(binary: &Path) -> (usize, usize) {
    let shown = Command::new("objdump")
        .arg("-d")
        .arg("--no-show-raw-insn")
        .arg(binary)
        .output()
        .unwrap();
    assert!(
        shown.status.success(),
        "`objdump` отказал на `{}`",
        binary.display()
    );
    let text = String::from_utf8_lossy(&shown.stdout);
    let mut body = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        let opens = line.find('<').filter(|_| line.trim_end().ends_with(">:"));
        if let Some(at) = opens {
            let name = &line[at + 1..line.trim_end().len() - 2];
            inside = name == "main" || name.starts_with("fn_");
            continue;
        }
        if inside && !line.trim().is_empty() {
            body.push(line);
        }
    }
    let dups = body
        .iter()
        .filter(|line| {
            (line.contains("call") && line.contains("<adamas_dup"))
                || line.contains("addl   $0x1,(%")
        })
        .count();
    let drops = body
        .iter()
        .filter(|line| line.contains("call") && line.contains("<adamas_drop"))
        .count();
    (dups, drops)
}

/// Имена точек входа, встреченные между первым `from` и следующим `to`.
///
/// Нужно одному свидетелю - мутанту: «между парой стоит наблюдение счётчика»
/// иначе читалось бы с экрана, а не из прогона.
fn between(text: &str, from: &str, to: &str) -> String {
    let body = hot(text);
    let mut names = BTreeSet::new();
    let mut inside = false;
    for line in body.lines() {
        if !inside && line.contains(from) {
            inside = true;
            continue;
        }
        if inside {
            if line.contains(to) {
                break;
            }
            if let Some(at) = line.find("@adamas_") {
                let rest = &line[at + 1..];
                let end = rest.find('(').unwrap_or(rest.len());
                names.insert(rest[..end].to_owned());
            }
        }
    }
    names.into_iter().collect::<Vec<_>>().join(", ")
}

/// Чего пара стоит временем. Зовётся руками: величина требует тихой машины.
///
/// ```text
/// cargo test -p adamas-codegen --test collapse -- --ignored --nocapture
/// ```
///
/// Протокол — тот же, что у соседнего числа, с которым это сравнивается
/// (`benches/native.rs`, схлопывание пары у уникального родителя, 13%):
/// чередование внутри блока, оценка стороны — **пол** блока, тишайшие блоки
/// вперёд. Врозь эти две точки не разрешаются: разница мельче разброса
/// абсолютных чисел, а чередованию помеха — общий множитель, и он сокращается.
///
/// Обе стороны — один и тот же конвейер, отличающийся **одной** стадией. Это
/// условие годности замера, а не аккуратность: собери одну сторону иначе, и лог
/// напечатал бы отношение сборок в формате отношения проходов.
#[test]
#[ignore = "стенд времени: величина требует тихой машины"]
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn what_the_pair_costs_in_time() {
    let Some((tools, _)) = harness::llvm_toolchains() else {
        return;
    };
    let runtime = harness::runtime_bitcode(&tools);
    let cells = 8_000_000_u32;
    let big = WALK.replace("build 16 Nil", &format!("build {cells} Nil"));
    let artefacts = harness::llvm_text("big", &big).unwrap();
    let passes: [(&str, Option<Pass>); 2] = [("big.plain", None), ("big.kept", Some(watched))];
    let built: Vec<std::path::PathBuf> = passes
        .iter()
        .map(|(stem, pass)| {
            harness::llvm_binary(
                stem,
                &artefacts,
                &tools,
                &Pipeline::collapsing(&runtime, *pass),
            )
        })
        .collect();

    // Сколько пар проход снял: без этого числа «сколько стоит пара» не
    // посчитать, а посчитанное на глаз разъехалось бы с программой молча.
    let inlined = std::fs::read_to_string(harness::scratch().join("big.plain.inlined.ll")).unwrap();
    let (_, report) = collapse(&inlined, Between::Watched);
    let taken = f64::from(u32::try_from(report.cancelled).unwrap()) * f64::from(cells);
    eprintln!("снято пар на виток {}, витков {cells}", report.cancelled);
    assert!(report.cancelled > 0, "стенду нечего мерить: пар не снято");

    let mut blocks: Vec<(f64, f64)> = Vec::new();
    for block in 0..5 {
        let mut plain = f64::MAX;
        let mut kept = f64::MAX;
        for _ in 0..8 {
            plain = plain.min(least(&built[0]));
            kept = kept.min(least(&built[1]));
        }
        eprintln!(
            "блок {block}: без прохода {plain:.2} мс, с проходом {kept:.2} мс, \
             разность {:.2} ({:.1}%)",
            plain - kept,
            100.0 * (plain - kept) / plain
        );
        blocks.push((plain, kept));
    }
    blocks.sort_unstable_by(|left, right| left.0.total_cmp(&right.0));
    let quiet = &blocks[..4];
    let mut differences: Vec<f64> = quiet.iter().map(|(plain, kept)| plain - kept).collect();
    differences.sort_unstable_by(f64::total_cmp);
    let median = differences[differences.len() / 2];
    let spread = differences[differences.len() - 1] - differences[0];
    let floor = quiet[0].0;
    eprintln!(
        "по {} тишайшим блокам: разность {median:.2} мс из {floor:.2} - {:.1}%, \
         размах {spread:.2}, запас {:.1}x; пар снято {taken}, то есть {:.2} нс на пару",
        quiet.len(),
        100.0 * median / floor,
        median / spread.max(f64::EPSILON),
        median * 1e6 / taken
    );
    assert!(
        differences[0] > 0.0,
        "сборка со схлопыванием вышла не быстрее: тишайшие блоки дали {:.2} мс",
        differences[0]
    );
}

/// Пол прогона: одно измерение, наименьшее из которых и берётся блоком.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn least(binary: &Path) -> f64 {
    let started = std::time::Instant::now();
    let run = Command::new(binary).output().unwrap();
    let spent = started.elapsed();
    assert!(run.status.success(), "прогон оборвался");
    spent.as_secs_f64() * 1e3
}

//! Где ветвь переписывает разобранную ячейку - место, а не только вердикт
//! (§5.1, §7.2 FBIP hints).
//!
//! §5.1 обещает редактору три строки: «reuse applies to unique inputs»,
//! «reuse not applicable, allocations expected» и «this Node allocation is
//! reused». Третья указывает на **построение**, а вердикт `@fbip` до волны 3
//! Фазы 9 отвечал только отказом и только там, где атрибут написан. Здесь
//! проверяется вторая половина ответа: [`Signature::reuse`] знает места обеих -
//! и тех построений, что заняли слот, и того, что не смогло.
//!
//! # Свидетель - текст под подчёркиванием
//!
//! Номер строки подтвердил бы, что маршрут куда-то привёл. Кусок текста,
//! вырезанный по спану, подтверждает, что привёл он **туда**: у половины
//! заготовок здесь два построения на одной строке, и перепутанные кадры дают
//! соседнее выражение, чего номер строки не видит.

use std::path::{Path, PathBuf};

use adamas_core::fbip::Fault;
use adamas_core::sig::Signature;
use adamas_core::source::SourceFile;
use adamas_parser::parse;

/// Текст до сигнатуры. Отказ здесь - провал теста, а не проверяемый исход.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанную заготовку, и падать он должен громко"
)]
fn program(text: &str) -> Signature {
    let module = parse(text).expect("заготовка обязана разбираться");
    let (signature, _) =
        adamas_elab::elaborate(&module).expect("заготовка обязана элаборироваться");
    signature
}

/// Что стоит под подчёркиваниями переписанных ячеек.
fn rewritten<'a>(signature: &Signature, text: &'a str, name: &str) -> Vec<&'a str> {
    signature.reuse(name).map_or_else(Vec::new, |reuse| {
        reuse
            .rewrites
            .iter()
            .map(|spot| &text[spot.span.start()..spot.span.end()])
            .collect()
    })
}

/// Что стоит под подчёркиванием несостоявшегося reuse.
fn blocked<'a>(signature: &Signature, text: &'a str, name: &str) -> Option<&'a str> {
    let spot = &signature.reuse(name)?.blocked.as_ref()?.spot;
    Some(&text[spot.span.start()..spot.span.end()])
}

/// Заготовка: каждая форма ответа написана ровно один раз.
const SOURCES: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Tree
  Node : Tree -> Nat -> Tree -> Tree

data Pair where
  MkPair : Nat -> Nat -> Pair

choose : Tree -> Tree -> Tree
choose a b = a

plain : Nat -> Pair
plain n = MkPair n n

mirror : Tree -> Tree
mirror Leaf = Leaf
mirror (Node l x r) = Node r x l

nested : Tree -> Tree
nested Leaf = Leaf
nested (Node l x r) = choose (Node r x l) Leaf

twice : Tree -> Tree
twice Leaf = Leaf
twice (Node l x r) = choose (Node r x l) (Node l x r)

flat : Tree -> Pair
flat Leaf = MkPair Zero Zero
flat (Node l x r) = MkPair x x

mutual
  counting : Tree -> Nat
  counting Leaf = Zero
  counting (Node l x r) = x

  rotating : Tree -> Tree
  rotating Leaf = Leaf
  rotating (Node l x r) = Node r (counting l) l
";

/// Переписанная ячейка показывает **построение**, а не определение.
#[test]
fn a_rewrite_underlines_what_it_rewrites() {
    let signature = program(SOURCES);
    // **Вторая** ветвь: первая строит `Leaf`, у которого полей нет, и слота он
    // не занимает вовсе. Номер ветви в маршруте от этого значим - у заготовки с
    // двумя аллоцирующими ветвями перепутанный номер невиден.
    assert_eq!(rewritten(&signature, SOURCES, "mirror"), ["Node r x l"]);
    // Позиция аргумента: кадры спайна обязаны довести до **первого** аргумента
    // из двух, то есть пройти `Callee` и только потом `Argument`.
    assert_eq!(rewritten(&signature, SOURCES, "nested"), ["(Node r x l)"]);
    // Член группы `mutual`, и **второй**: маршрут начинается номером члена, и
    // без него подчёркивание встало бы в тело `counting`.
    assert_eq!(
        rewritten(&signature, SOURCES, "rotating"),
        ["Node r (counting l) l"]
    );
}

/// Тело без разбора в таблицу не попадает вовсе.
///
/// Существенно: «нет записи» и «запись пустая» читаются по-разному. `plain`
/// строит пару и ничего не разбирает - переписывать там нечего, и подсказка
/// «ячейка переписывается» над ней была бы ложью, а подсказка «не
/// переписывается» - обвинением на пустом месте.
#[test]
fn a_body_that_matches_nothing_has_no_answer() {
    let signature = program(SOURCES);
    assert!(
        signature.reuse("plain").is_none(),
        "`plain` ничего не разбирает"
    );
    assert!(
        signature.reuse("choose").is_none(),
        "`choose` ничего не разбирает"
    );
}

/// Слот один: второе построение той же формы показывается **своим** местом.
///
/// Обе половины ответа в одном теле, и они не совпадают: первое построение
/// ячейку переписывает, второе - нет. Свидетель с одним построением этого не
/// различает.
#[test]
fn the_second_structure_is_blocked_at_its_own_place() {
    let signature = program(SOURCES);
    assert_eq!(
        rewritten(&signature, SOURCES, "twice"),
        ["(Node r x l)"],
        "слот занимает первое построение"
    );
    assert_eq!(
        blocked(&signature, SOURCES, "twice"),
        Some("(Node l x r)"),
        "второму переписывать нечего, и место у него своё"
    );
    let fault = signature
        .reuse("twice")
        .and_then(|it| it.blocked.as_ref())
        .map(|it| &it.fault);
    assert!(
        matches!(fault, Some(Fault::Taken { .. })),
        "причина - занятый слот, а не несовпавшая форма: {fault:?}"
    );
}

/// Несовпавшая форма показывает то построение, которому слота не нашлось.
#[test]
fn a_mismatched_shape_underlines_the_structure_without_a_slot() {
    let signature = program(SOURCES);
    assert_eq!(
        blocked(&signature, SOURCES, "flat"),
        Some("MkPair Zero Zero"),
        "у ветви `Leaf` слота нет: полей у неё нуль, а у пары два"
    );
    assert!(
        rewritten(&signature, SOURCES, "flat").is_empty(),
        "ни одно построение слота не заняло"
    );
}

/// Атрибут и подсказка называют **одно** место, потому что считаются один раз.
///
/// Свидетель кросс-проверочный: слева - отказ элаборации по `@fbip`, справа -
/// то, что уйдёт в редактор над тем же телом без атрибута. Разойдись они, и
/// читатель получил бы от компилятора и от редактора два разных ответа про одну
/// строку.
#[test]
fn the_attribute_and_the_hint_name_the_same_place() {
    const WITHOUT: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Tree where
  Leaf : Tree
  Node : Tree -> Nat -> Tree -> Tree

data Pair where
  MkPair : Nat -> Nat -> Pair

flat : Tree -> Pair
flat Leaf = MkPair Zero Zero
flat (Node l x r) = MkPair x x
";
    let signature = program(WITHOUT);
    let spot = signature
        .reuse("flat")
        .and_then(|it| it.blocked.as_ref())
        .map_or_else(
            || panic!("`flat` обязана знать место несостоявшегося reuse"),
            |it| it.spot.span,
        );

    let with = WITHOUT.replace("flat : Tree -> Pair", "@fbip\nflat : Tree -> Pair");
    let module = parse(&with).unwrap_or_else(|error| panic!("заготовка разбирается: {error}"));
    let refusal = adamas_elab::elaborate(&module)
        .err()
        .unwrap_or_else(|| panic!("`@fbip` на `flat` обязан отвергаться"));

    // Спаны в двух текстах, и тексты различаются вставленной строкой атрибута.
    // Сверяется поэтому **кусок под подчёркиванием**, а не число.
    assert_eq!(
        &WITHOUT[spot.start()..spot.end()],
        &with[refusal.span().start()..refusal.span().end()],
        "атрибут и подсказка обязаны показывать одно построение"
    );
}

/// Корпус `tests/golden/eval/` - он же корень поиска подключаемых модулей.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Фикстура целиком - вместе с тем, что она подключает (§4.8).
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанный корпус, и падать он должен громко"
)]
fn analysed(path: &Path) -> adamas_elab::program::Program {
    let text = std::fs::read_to_string(path).expect("файл корпуса обязан читаться");
    let entry = SourceFile::new(path.display().to_string(), text);
    let sources = adamas_elab::program::Directory::new(corpus());
    let program = adamas_elab::program::analyze(entry, &sources);
    if let Some(located) = program.error() {
        panic!(
            "исходник обязан проходить проверку: {}",
            program.rendered(located)
        );
    }
    program
}

/// Фикстуры корпуса по алфавиту.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ означает сломанный корпус, и падать он должен громко"
)]
fn fixtures() -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = std::fs::read_dir(corpus())
        .expect("каталог корпуса обязан читаться")
        .map(|entry| entry.expect("запись каталога").path())
        .filter(|path| path.extension().is_some_and(|it| it == "adamas"))
        .collect();
    found.sort();
    found
}

/// Всякое место переиспользования на корпусе режется текстом **своего** файла.
///
/// Счёт снят прогоном 2026-09-23 на 127 фикстурах: 105 переписанных ячеек у 88
/// определений и 60 мест, где reuse не состоялся (несовпавшая форма 45, занятый
/// слот 15, живое разобранное 0). Числа сверяются нижней границей - корпус
/// растёт, - а проверяется, что всякое место режется и не пусто: спан, взятый по
/// чужому тексту, такой сверки не переживает.
#[test]
fn every_place_on_the_corpus_cuts_its_own_text() {
    let mut rewrites = 0_usize;
    let mut blocked = 0_usize;
    let mut elsewhere = 0_usize;
    for path in fixtures() {
        let program = analysed(&path);
        let Some(signature) = program.signature.as_ref() else {
            continue;
        };
        for name in signature.names() {
            let Some(reuse) = signature.reuse(&name) else {
                continue;
            };
            let spots = reuse
                .rewrites
                .iter()
                .chain(reuse.blocked.as_ref().map(|it| &it.spot));
            for spot in spots {
                let unit = program
                    .units
                    .iter()
                    .find(|unit| unit.path.as_deref() == spot.module.as_deref())
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: `{name}` указывает в модуль `{:?}`, которого в программе нет",
                            path.display(),
                            spot.module
                        )
                    });
                let cut = unit
                    .file
                    .text()
                    .get(spot.span.start()..spot.span.end())
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: `{name}` режет свой файл не по границе знака либо за его концом",
                            path.display()
                        )
                    });
                assert!(
                    !cut.trim().is_empty(),
                    "{}: `{name}` подчёркивает пустоту",
                    path.display()
                );
                elsewhere += usize::from(spot.module.is_some());
            }
            rewrites += reuse.rewrites.len();
            blocked += usize::from(reuse.blocked.is_some());
        }
    }
    assert!(
        rewrites >= 100,
        "переписанных ячеек {rewrites} - было 105, корпус не мог обеднеть"
    );
    assert!(
        blocked >= 55,
        "несостоявшихся {blocked} - было 60, корпус не мог обеднеть"
    );
    // Место из подключённого модуля - половина, ради которой [`Spot`] несёт
    // файл: спан без него нарисовался бы по чужому тексту. Без этой строки
    // забытый модуль виден только тем, что спан случайно вышел за конец файла.
    assert!(
        elsewhere > 0,
        "в корпусе обязана быть программа, чьё место переиспользования лежит не во входном файле"
    );
}

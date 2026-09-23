//! Где определение аллоцирует - место, а не только вердикт (§5.1, §7.2).
//!
//! §7.2 просит от редактора «подсветку мест, аллоцирующих в куче Perceus».
//! Вердикт [`adamas_core::alloc::blame`] отвечал одними именами, и поставить
//! подсказку было негде: спанов на узлах терма нет и не будет (48 байт на
//! узел). Место поэтому идёт **маршрутом** - тем же, каким ядро называет место
//! отказа, - и переводит его в спан элаборация.
//!
//! # Свидетель - текст под подчёркиванием, а не номер строки
//!
//! Номер строки подтверждает, что маршрут куда-то привёл. Кусок текста,
//! вырезанный из исходника по отданному спану, подтверждает, что привёл он
//! **туда**: перепутай кадры `Callee` и `Argument` - и под подчёркиванием
//! окажется соседнее выражение той же строки, чего номер не увидит.

use std::path::{Path, PathBuf};

use adamas_core::alloc;
use adamas_core::sig::{DefinitionKind, Signature};
use adamas_core::source::SourceFile;
use adamas_core::term::Name;
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

/// Что стоит под подчёркиванием у определения. `None` - места нет.
fn underlined<'a>(signature: &Signature, text: &'a str, name: &str) -> Option<&'a str> {
    let spot = signature.allocated_at(name)?;
    Some(&text[spot.span.start()..spot.span.end()])
}

/// Заготовка, в которой каждая форма источника написана ровно один раз.
const SOURCES: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

idPair : Pair -> Pair
idPair p = p

ignoring : (Nat -> Nat) -> Nat
ignoring f = Zero

joining : Nat -> Nat -> Nat
joining a b = a

wrap : Nat -> Pair
wrap n = MkPair n n

reach : Nat -> Pair
reach n = wrap n

deep : Nat -> Pair
deep n = idPair (MkPair n n)

tuck : Nat -> Pair
tuck n =
  let m : Nat = Succ n
  MkPair m m

pick : Nat -> Pair
pick Zero = MkPair Zero Zero
pick (Succ m) = MkPair m m

held : Nat
held = ignoring (\\m -> m)

bound : Nat
bound = ignoring (joining Zero)

calling : (Nat -> Nat) -> Nat
calling f = f Zero

mutual
  ping : Nat -> Pair
  ping Zero = MkPair Zero Zero
  ping (Succ m) = pong m

  pong : Nat -> Pair
  pong m = ping m
";

/// Каждая форма источника показывает **своё** выражение, а не объявление.
#[test]
fn every_source_underlines_what_allocates() {
    let signature = program(SOURCES);
    for (name, written) in [
        // Конструктор с рантайм-полем: подчёркивается применение целиком, а не
        // имя конструктора - чинить читателю именно его.
        ("wrap", "MkPair n n"),
        // Вызов аллоцирующего соседа: место у **вызывающего** - вызов, а не
        // тело вызываемого. На этом и стоит цепочка `Blame::through`.
        ("reach", "wrap n"),
        // Позиция аргумента: кадры спайна обязаны довести до аргумента, а не
        // остановиться на `idPair (…)`. Скобки входят в спан - их носит узел
        // дерева, и подчёркивание рисуется по нему.
        ("deep", "(MkPair n n)"),
        // Значение связывания `let`, а не тело блока, хотя оба аллоцируют.
        ("tuck", "Succ n"),
        // Ветвь разбора: первая из двух, и текст у неё свой.
        ("pick", "MkPair Zero Zero"),
        // Лямбда сверх параметров - только там, где она не ведущая: ведущие
        // снимаются вместе с параметрами определения.
        ("held", "(\\m -> m)"),
        // Частичное применение.
        ("bound", "(joining Zero)"),
        // Применение значения-функции - боксирование границы (§4.11).
        ("calling", "f Zero"),
        // Член группы `mutual`: маршрут начинается номером члена, и без него
        // подчёркивание встало бы на блок целиком.
        ("ping", "MkPair Zero Zero"),
        ("pong", "ping m"),
    ] {
        assert_eq!(
            underlined(&signature, SOURCES, name),
            Some(written),
            "`{name}` подчёркивает не то место"
        );
    }
}

/// Цепочка вины позиционируется по звеньям, а не по одному концу.
///
/// Это и есть ответ на «чем адресуется звено»: у каждого звена своё место в
/// **его собственном** теле, и собирается цепочка обращением к
/// [`Signature::allocated_at`] по имени звена.
#[test]
fn the_chain_is_positioned_link_by_link() {
    let signature = program(SOURCES);
    let name: Name = "pong".into();
    let blame = alloc::blame(&signature, &name).expect("`pong` аллоцирует через `ping`");

    assert_eq!(
        blame.through().iter().map(|it| &**it).collect::<Vec<_>>(),
        ["ping"],
        "путь идёт по графу вызовов до первого не-вызова"
    );
    assert_eq!(
        blame.source(),
        &alloc::Source::Construct("MkPair".into()),
        "конец пути - конструктор"
    );

    // Звено `pong` показывает вызов, звено `ping` - построение. Место конца
    // пути берётся у владельца, а не у того, кто до него дозвался.
    assert_eq!(underlined(&signature, SOURCES, &name), Some("ping m"));
    assert_eq!(
        underlined(&signature, SOURCES, blame.owner(&name)),
        Some("MkPair Zero Zero")
    );
}

/// Объявление звена знает та же таблица, что знает объявления вообще.
///
/// Переход к определению и подсказка - разные места, и берутся они разными
/// таблицами: [`Signature::origin`] отвечает про объявление, `allocated_at` -
/// про место внутри тела. Проверяется здесь то, что для звеньев цепочки первая
/// таблица полна **по построению**: в цепочку попадает только `Source::Call`, а
/// его записывают определению с телом, то есть с клаузами.
#[test]
fn every_link_of_a_chain_knows_where_it_is_declared() {
    let signature = program(SOURCES);
    let name: Name = "pong".into();
    let blame = alloc::blame(&signature, &name).expect("`pong` аллоцирует через `ping`");
    for link in blame.through() {
        assert!(
            signature.origin(link).is_some(),
            "звено `{link}` не знает, где объявлено"
        );
        assert!(
            signature.allocated_at(link).is_some(),
            "звено `{link}` не знает, где аллоцирует"
        );
    }
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

/// Всякое **написанное** определение, которое аллоцирует, знает своё место - и
/// место это режется текстом его собственного файла.
///
/// Обе половины существенны. Пробел в первой означал бы подсказку, которой на
/// части корпуса нет; ошибка во второй - спан, нарисованный по чужому тексту,
/// то есть подчёркивание случайной строки.
///
/// «Написанное» здесь - то, у которого есть клаузы, и спрашивается это у
/// [`Signature::origin`]: таблицы наполняет один и тот же проход элаборации.
/// Остаток назван и проверен отдельно
/// ([`only_a_record_nobody_wrote_has_no_place`]).
#[test]
fn the_corpus_knows_where_every_written_body_allocates() {
    let mut checked = 0_usize;
    for path in fixtures() {
        let program = analysed(&path);
        let Some(signature) = program.signature.as_ref() else {
            continue;
        };
        for name in allocating(signature) {
            if signature.origin(&name).is_none() {
                continue;
            }
            let spot = signature.allocated_at(&name).unwrap_or_else(|| {
                panic!(
                    "{}: `{name}` написана клаузами и аллоцирует, а места не знает",
                    path.display()
                )
            });
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
            checked += 1;
        }
    }
    // Число не сверяется - оно растёт с корпусом; проверяется, что проверять
    // было что: пустой обход зелен при любой поломке.
    assert!(
        checked > 500,
        "мест проверено {checked} - корпус обязан давать больше"
    );
}

/// Аллоцирующие определения с телом - те, у кого место вообще может быть.
fn allocating(signature: &Signature) -> Vec<Name> {
    let mut found: Vec<Name> = signature
        .names()
        .into_iter()
        .filter(|name| {
            signature.lookup(name).is_some_and(|definition| {
                definition.body.is_some()
                    && definition.allocates.is_some()
                    && matches!(definition.kind, DefinitionKind::Regular)
            })
        })
        .collect();
    found.sort();
    found
}

/// Без места остаётся только то, чьего тела автор не писал.
///
/// Граница названа, и она **измерена**, а не заявлена: 82 определения корпуса
/// аллоцируют, не имея места, и у всех 82 нет и клауз. Это значение модуля и
/// словарь инстанса - записи, которые собирает элаборация, и написанного
/// выражения за ними нет вовсе. Место у них было бы синтетическим, то есть
/// подсказка указывала бы в текст, которого автор не писал.
///
/// Свидетель обратной стороны: определение **с** клаузами в этот остаток
/// попасть не должно никогда - именно это и проверяет
/// [`the_corpus_knows_where_every_written_body_allocates`], и вместе они
/// закрывают обе стороны границы.
#[test]
fn only_a_record_nobody_wrote_has_no_place() {
    let mut without = 0_usize;
    for path in fixtures() {
        let program = analysed(&path);
        let Some(signature) = program.signature.as_ref() else {
            continue;
        };
        for name in allocating(signature) {
            if signature.allocated_at(&name).is_some() {
                continue;
            }
            assert!(
                signature.origin(&name).is_none(),
                "{}: `{name}` написана клаузами, а места не знает",
                path.display()
            );
            without += 1;
        }
    }
    assert!(
        without > 0,
        "остаток обязан быть непустым - иначе проверять нечего"
    );
}

/// Всякое звено цепочки вины знает, где аллоцирует.
///
/// Это и есть обещание треку C: цепочку показывают целиком, и каждое звено
/// адресуется своим местом. Звено без места оставило бы подсказку с дыркой
/// посередине.
#[test]
fn every_link_of_every_chain_on_the_corpus_knows_its_place() {
    let mut links = 0_usize;
    for path in fixtures() {
        let program = analysed(&path);
        let Some(signature) = program.signature.as_ref() else {
            continue;
        };
        for name in allocating(signature) {
            let Some(blame) = alloc::blame(signature, &name) else {
                continue;
            };
            for link in blame.through() {
                if signature.origin(link).is_none() {
                    // Звено, которого автор не писал, - то же значение модуля;
                    // граница у него общая с остатком выше.
                    continue;
                }
                assert!(
                    signature.allocated_at(link).is_some(),
                    "{}: звено `{link}` цепочки `{name}` не знает, где аллоцирует",
                    path.display()
                );
                links += 1;
            }
        }
    }
    assert!(links > 0, "цепочки со звеньями в корпусе обязаны быть");
}

/// Место, пришедшее из подключённого модуля, называет **его** файл и режется
/// **его** текстом.
///
/// Спан без файла здесь и ломается: цепочка пересекает границу файла на первом
/// же вызове в библиотеку, а смещения у `Span` - внутри одного текста.
/// Свидетель поэтому вырезает кусок из текста названного модуля и сверяет его
/// с написанным - подчёркивание, нарисованное по чужому файлу, такой сверки не
/// переживает.
#[test]
fn a_spot_in_an_imported_module_is_cut_from_that_modules_text() {
    let mut seen = 0_usize;
    for path in fixtures() {
        let program = analysed(&path);
        if program.units.len() < 2 {
            continue;
        }
        let Some(signature) = program.signature.as_ref() else {
            continue;
        };
        for name in signature.names() {
            let Some(spot) = signature.allocated_at(&name) else {
                continue;
            };
            let Some(module) = spot.module.as_deref() else {
                continue;
            };
            let unit = program
                .units
                .iter()
                .find(|unit| unit.path.as_deref() == Some(module))
                .unwrap_or_else(|| {
                    panic!(
                        "{}: `{name}` называет модуль `{module}`, которого в программе нет",
                        path.display()
                    )
                });
            let text = unit.file.text();
            let cut = text
                .get(spot.span.start()..spot.span.end())
                .unwrap_or_else(|| {
                    panic!(
                        "{}: `{name}` режет `{module}` не по границе знака либо за концом текста",
                        path.display()
                    )
                });
            assert!(
                !cut.trim().is_empty(),
                "{}: `{name}` в `{module}` подчёркивает пустоту",
                path.display()
            );
            seen += 1;
        }
    }
    assert!(
        seen > 0,
        "в корпусе обязана быть программа из нескольких файлов, чьё место лежит не во входном"
    );
}

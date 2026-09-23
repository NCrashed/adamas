//! Восстановление после отказа: несколько подчёркиваний вместо одного
//! (§10 вопрос 177).
//!
//! # Чем этот свидетель ломается
//!
//! Жанр подделки здесь назван в самом вопросе: **выдуманная вторая ошибка хуже
//! отсутствующей**. Свидетель, считающий одни диагностики, зелен и у
//! восстановления, которое после первого отказа сыплет каскадом следствий, -
//! поэтому каждый здесь спрашивает не число, а **что именно сказано**, и рядом
//! с файлом из независимых ошибок стоит файл, где вторая есть следствие первой.
//!
//! Подавление следствий ломается в обе стороны, и обе проверяются: слишком
//! узкое печатает выдуманное, слишком широкое глотает настоящее. Поэтому за
//! каждым «здесь молчит» стоит парный «а здесь говорит»: клаузы при сломанной
//! сигнатуре молчат, клаузы без сигнатуры - нет; обращение к необъявленному
//! имени молчит, независимый отказ ниже него - нет.

use adamas_core::source::SourceFile;
use adamas_elab::Severity;
use adamas_elab::program::{Memory, analyze as analyze_program};

/// `Nat` и `Bool` - база, на которой пишется всё остальное.
const BASE: &str = "\
data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

";

/// Заголовки **отказов** файла в порядке появления.
///
/// Оговорки отброшены нарочно: спрашивается здесь панель проблем, а не всё, что
/// компилятор счёл достойным упоминания.
fn refusals(text: &str) -> Vec<String> {
    adamas_elab::analyze(text)
        .diagnostics
        .into_iter()
        .filter(|it| it.severity == Severity::Error)
        .map(|it| it.headline)
        .collect()
}

/// Текст с базой впереди.
fn program(body: &str) -> String {
    format!("{BASE}{body}")
}

#[test]
fn three_unknown_names_give_three_refusals() {
    // Тот случай, которым вопрос 177 был заведён: читатель делает несколько
    // ошибок разом. Имена независимы - ни одно из трёх определений не зовёт
    // другого, - поэтому все три отказа настоящие.
    let text = program(
        "\
one : Nat
one = alpha

two : Nat
two = beta

three : Nat
three = gamma
",
    );
    assert_eq!(
        refusals(&text),
        [
            "имя `alpha` не найдено",
            "имя `beta` не найдено",
            "имя `gamma` не найдено",
        ]
    );
}

#[test]
fn three_bodies_of_the_wrong_type_give_three_refusals() {
    // Второй род отказа, и приходит он из **ядра**, а не из элаборации: имена
    // здесь все найдены, и остановка была бы в проверке типов. Граница
    // определения обязана держать оба рода, иначе панель полна только у
    // опечаток в именах.
    let text = program(
        "\
one : Nat
one = True

two : Nat
two = False

three : Nat
three = True
",
    );
    let found = refusals(&text);
    assert_eq!(found.len(), 3, "{found:#?}");
    assert!(
        found.iter().all(|it| it.contains("несовпадение типов")),
        "{found:#?}"
    );
}

#[test]
fn a_use_of_a_name_that_never_declared_is_not_a_second_refusal() {
    // `bad` не объявилось: его тип зовёт имя, которого нет. Всякое обращение к
    // `bad` ниже получило бы «имя `bad` не найдено» - отказ, которого в тексте
    // нет: имя написано, и написано верно. Ошибка одна, и сказать о ней надо
    // один раз.
    let text = program(
        "\
bad : Missing -> Nat
bad x = Zero

user : Nat
user = bad Zero
",
    );
    assert_eq!(refusals(&text), ["имя `Missing` не найдено"]);
}

#[test]
fn an_independent_refusal_below_a_broken_declaration_survives() {
    // Парный к предыдущему: подавление следствий обязано быть узким. Тот же
    // сломанный `bad`, но ниже - ошибка, к нему никак не относящаяся, и её
    // проглатывание было бы ровно тем молчанием, ради устранения которого
    // восстановление и заводилось.
    let text = program(
        "\
bad : Missing -> Nat
bad x = Zero

other : Nat
other = alpha
",
    );
    assert_eq!(
        refusals(&text),
        ["имя `Missing` не найдено", "имя `alpha` не найдено"]
    );
}

#[test]
fn clauses_of_a_broken_signature_do_not_say_it_is_missing() {
    // Сигнатура написана и отказала; клаузы за ней - не «сигнатуры нет».
    let text = program(
        "\
bad : Missing -> Nat
bad x = Zero
",
    );
    assert_eq!(refusals(&text), ["имя `Missing` не найдено"]);
}

#[test]
fn clauses_without_a_signature_still_say_so() {
    // Парный к предыдущему: сигнатуры действительно нет, и об этом говорится.
    // Без этой пары подавление «нет сигнатуры» было бы неотличимо от того,
    // чтобы выключить отказ вовсе.
    let text = program("lonely x = Zero\n");
    let found = refusals(&text);
    assert_eq!(found.len(), 1, "{found:#?}");
    assert!(found[0].contains("lonely"), "{found:#?}");
}

#[test]
fn a_module_body_refuses_once_for_the_whole_module() {
    // Граница определения проходит по **файлу**, а не по телу модуля: снаружи
    // модуль - одно имя, и объявленный наполовину он стал бы сигнатурой,
    // которой автор не писал. Решение записано, и свидетель здесь затем, чтобы
    // его нельзя было поменять молча.
    let text = program(
        "\
module M where
  a : Nat
  a = True

  b : Nat
  b = True
",
    );
    let found = refusals(&text);
    assert_eq!(found.len(), 1, "{found:#?}");
}

#[test]
fn an_accepted_program_stays_accepted() {
    // Восстановление не вправе находить отказы там, где их нет: проход теперь
    // доходит до конца файла всегда, и «дошёл» не значит «нашёл».
    let text = program(
        "\
one : Nat
one = Succ Zero

two : Nat
two = Succ one
",
    );
    assert_eq!(refusals(&text), [] as [String; 0]);
}

#[test]
fn an_imported_file_shows_each_of_its_refusals_at_its_own_unit() {
    // Отказы подключённого файла живут в **его** тексте: нарисованные по
    // исходнику входного, они подчеркнули бы случайную строку. Проверяется
    // поэтому не только их число, но и то, к какой единице они отнесены.
    let broken = format!(
        "{BASE}\
one : Nat
one = alpha

two : Nat
two = beta
"
    );
    let modules = Memory::new().with("Broken", &broken);
    let entry = "\
import Broken as B

main : B.Nat
main = B.Zero
";
    let program = analyze_program(SourceFile::new("вход", entry.to_owned()), &modules);
    let refused: Vec<&adamas_elab::program::Located> = program
        .diagnostics
        .iter()
        .filter(|it| it.diagnostic.severity == Severity::Error)
        .collect();
    let said: Vec<String> = refused
        .iter()
        .map(|it| it.diagnostic.headline.clone())
        .collect();
    assert_eq!(
        said,
        ["имя `alpha` не найдено", "имя `beta` не найдено"],
        "{said:#?}"
    );
    assert!(
        refused.iter().all(|it| it.unit != 0),
        "отказы чужого файла отнесены к входному"
    );
}

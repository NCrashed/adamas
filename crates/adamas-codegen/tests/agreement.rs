//! Договор третьего вычислителя: понижение отвечает то же, что `adamas eval`.
//!
//! Жанр не новый. Машину с ядром связывает
//! `the_machine_agrees_with_the_core_on_the_pure_fragment`, специализацию с
//! исполнением - `crates/adamas-interp/tests/monomorphisation.rs`; здесь третий
//! вычислитель входит в тот же договор. Свидетель - **интерпретатор**, а не
//! записанное руками ожидание: сверка своего вывода со своим же ожиданием не
//! показывает ничего.
//!
//! Проверяется не «C порождён», а прогон: текст компилируется настоящим
//! компилятором, линкуется с настоящим рантаймом и запускается.
//!
//! # Что берётся и что нет
//!
//! [`TAKEN`] - программы, которые срез обязан взять целиком. Остальным корпус
//! отвечает по факту: понижение либо отвергает их названной причиной, либо
//! берёт - и тогда ответ обязан сойтись наравне с прочими. Молчаливого
//! расхождения не бывает ни у кого.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{PRINT_DEPTH, Term};
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::mono;
use adamas_elab::{Owned, Warnings};

/// Программы корпуса, которые срез берёт.
///
/// Чистый фрагмент: семейства и конструкторы, функции и применение, разбор,
/// рекурсия, `let`. Всё, что здесь стоит, обязано собраться и ответить как
/// `adamas eval`; список сокращать нельзя, а пополнять - можно и нужно, когда
/// фрагмент растёт.
const TAKEN: [&str; 12] = [
    "arithmetic",
    "beta-redex",
    "case-family",
    "decidable",
    "erasure",
    "existential",
    "lists",
    "module-scope",
    "mutual-family",
    "operators",
    "rose",
    "truncation",
];

/// Замыкание над **несколькими** связываниями и порядок его среды.
///
/// Написано здесь, а не в корпусе, потому что показывает не форму языка, а
/// границу понижения: замыкание раскладывает захваченное по слотам, и порядок
/// слотов - его собственное решение. Корпус эту границу не покрывает ни одной
/// фикстурой - измерено мутантом: перестановка слотов проходила корпус целиком.
///
/// Ответ различает порядок по построению: `[3, 1, 0]` против `[1, 3, 0]`.
/// Сложение вместо списка не годилось бы - оно коммутативно, и перестановка на
/// нём ненаблюдаема.
const CAPTURES: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

runWith : (Nat -> List Nat) -> Nat -> List Nat
runWith f x = f x

main : List Nat
main =
  let first : Nat = Succ (Succ (Succ Zero))
  let second : Nat = Succ Zero
  runWith (\\n -> Cons first (Cons second (Cons n Nil))) Zero
";

/// Ответ **глубже среза**: обе печати обязаны оборваться одинаково.
///
/// Без этого свидетеля договор «то же, что интерпретатор» держался бы не
/// правилом, а тем, что ответы корпуса мельче двухсот уровней.
///
/// `times 16 16` даёт двести пятьдесят шесть `Succ` - глубину, на которой срез
/// заведомо срабатывает. Числом, а не двумя сотнями `Succ` в исходнике: писать
/// их руками значило бы вписать в тест ту самую глубину, которую он проверяет.
///
/// Совпадение здесь нетривиально, потому что глубину эти двое считают
/// по-разному: там терм со спайном применений, здесь значение со слотами.
/// Разойдись развёртка спайна на единицу - оборвётся на разном уровне.
const TOWER: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

plus : Nat -> Nat -> Nat
plus Zero m = m
plus (Succ k) m = Succ (plus k m)

times : Nat -> Nat -> Nat
times Zero m = Zero
times (Succ k) m = plus m (times k m)

main : Nat
main = times 16 16
";

/// Корпус `tests/golden/eval/`.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Место под порождённый C и его сборку.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("agreement");
    let _ = std::fs::create_dir_all(&dir);
    dir
}

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отвергнутый исходник означает сломанный корпус, и падать он должен громко"
)]
fn elaborated(source: &str) -> (Signature, Metas, Instances) {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect("исходник обязан проходить проверку");
    (signature, metas, instances)
}

/// Тело определения с подставленными аргументами уровня и row - ровно то, что
/// инстанцирует драйвер перед вычислением.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отсутствие определения означает сломанный корпус"
)]
fn body(signature: &Signature, name: &str) -> Term {
    let definition = signature.lookup(name).expect("определение объявлено");
    let body = definition.body.as_ref().expect("у определения есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

/// Что печатает `adamas eval`: значение по мнению машины со срезом по глубине.
///
/// Срез проверяется, а не предполагается: сойдись он с полной печатью не всегда,
/// «то же, что `adamas eval`» перестало бы быть правдой на глубоком ответе.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: непогашенная операция означает сломанный корпус"
)]
fn ran(signature: &Signature, term: &Term) -> String {
    let answer = adamas_interp::run(signature, term).expect("операция обязана встретить хендлер");
    // Со срезом, а не целиком: печать понижения режет на той же глубине, и
    // сравнивать надо то, что человек увидит от `adamas eval`.
    answer.printed(Some(PRINT_DEPTH)).to_string()
}

/// Объектные файлы рантайма: собираются однажды на весь прогон.
fn runtime() -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let dir = scratch();
        ["object.c", "evidence.c", "closure.c", "frame.c"]
            .iter()
            .map(|name| {
                let object = dir.join(format!("{name}.o"));
                let status = Command::new(env!("ADAMAS_CC"))
                    .args(["-std=c11", "-O1", "-c"])
                    .arg("-I")
                    .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                    .arg(sources.join(name))
                    .arg("-o")
                    .arg(&object)
                    .status();
                assert!(
                    status.is_ok_and(|status| status.success()),
                    "рантайм не собрался: {name}"
                );
                object
            })
            .collect()
    })
}

/// Собирает порождённый C и запускает его. Отдаёт stdout и stderr.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn built(name: &str, text: &str) -> (String, String) {
    let dir = scratch();
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();

    let mut compile = Command::new(env!("ADAMAS_CC"));
    compile
        .args([
            "-std=c11",
            "-O1",
            "-Wall",
            // Порождённый код связывает поля, которых тело не смотрит, и берёт
            // вектор evidence, которого чистый фрагмент не читает: неиспользуемое
            // здесь - норма, а не находка. Неявное объявление функции - находка:
            // им ловится расхождение с заголовком рантайма.
            "-Wno-unused",
            "-Werror=implicit-function-declaration",
        ])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(runtime())
        .arg("-o")
        .arg(&binary);
    let compiled = compile.output().unwrap();
    assert!(
        compiled.status.success(),
        "{name}: порождённый C не собрался:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let run = Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "{name}: прогон оборвался:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    (
        String::from_utf8(run.stdout).unwrap(),
        String::from_utf8(run.stderr).unwrap(),
    )
}

/// Понижение, сборка, прогон и сверка с интерпретатором.
///
/// Понижается **специализированный** терм (трек E): §4.11 требует специализации
/// для release, и понижению проще идти по терму без словарей. Сверяется он с
/// ответом на терме **написанном** - том самом, который считает `adamas eval`.
fn agreed(name: &str, source: &str) -> Result<String, adamas_codegen::CompileError> {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = body(&signature, "main");
    let expected = ran(&signature, &written);
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .unwrap_or_else(|error| panic!("{name}: специализация отказала: {error}"));

    let text = adamas_codegen::compile(&signature, &made.term)?;
    let (stdout, stderr) = built(name, &text);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        expected,
        "{name}: понижение посчитало не то, что машина"
    );
    Ok(stderr)
}

/// Корпус целиком: либо отказ с названной причиной, либо сошедшийся ответ.
///
/// Обе половины обязательны. Без первой список [`TAKEN`] молча усох бы; без
/// второй «не берётся» покрывало бы и тихое расхождение тоже.
///
/// Тест один на оба утверждения намеренно: два теста собирали бы одни и те же
/// фикстуры в одни и те же файлы параллельно и мешали друг другу.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
#[test]
fn the_corpus_agrees_with_the_interpreter() {
    let mut fixtures: Vec<PathBuf> = std::fs::read_dir(corpus())
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
        match agreed(&name, &source) {
            Ok(stderr) => {
                // Perceus не вставлен, и цена среза видна числом, а не
                // умолчанием: программа не освобождает ничего.
                assert!(
                    stderr.contains("живо"),
                    "{name}: прогон не сказал, сколько блоков осталось живо"
                );
                taken.push(name);
            }
            Err(error) => refused.push((name, error.to_string())),
        }
    }

    for name in TAKEN {
        assert!(
            taken.iter().any(|it| it == name),
            "{name} больше не берётся: {}",
            refused
                .iter()
                .find(|(it, _)| it == name)
                .map_or_else(|| "фикстуры нет вовсе".to_owned(), |(_, why)| why.clone())
        );
    }

    // Границы, которых корпус не покрывает, стоят рядом со своим утверждением.
    agreed("captures", CAPTURES).unwrap_or_else(|error| panic!("захваты: {error}"));

    // Свидетель среза сперва обязан оказаться глубже среза: без этой проверки
    // он молча выродился бы в ещё одну мелкую программу, а тест остался бы
    // зелёным и пустым.
    let (signature, _, _) = elaborated(TOWER);
    let expected = ran(&signature, &body(&signature, "main"));
    assert!(
        expected.contains('…'),
        "свидетель мельче среза: обрыва в ответе нет, и сверять нечего"
    );
    agreed("tower", TOWER).unwrap_or_else(|error| panic!("глубина: {error}"));
}

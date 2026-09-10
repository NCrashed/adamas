//! Общее для тестов понижения: элаборация, сборка порождённого C, прогон.
//!
//! Живёт отдельно, потому что каждый файл в `tests/` - свой крейт, а сборка
//! рантайма и запуск бинаря нужны обоим. Место под артефакты у каждого крейта
//! своё (`OUT_DIR/<имя теста>`): прогоны идут параллельно, и общий каталог
//! означал бы гонку за одними и теми же `.o`.

// Модуль компилируется в каждый тестовый крейт целиком, а нужен каждому не
// весь: `printed` спрашивает только сверка глубины.
#![allow(dead_code, reason = "общий модуль двух тестовых крейтов")]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use adamas_codegen::ir::{Arm, Binding, Expr, LocalId};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::{PRINT_DEPTH, Term};
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::mono;
use adamas_elab::{Owned, Warnings};

/// Корпус `tests/golden/eval/`.
pub(crate) fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden/eval")
}

/// Место под порождённый C и его сборку - своё у каждого тестового крейта.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join(env!("CARGO_CRATE_NAME"));
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

/// Ответ `adamas eval` на `main` исходника.
pub(crate) fn printed(source: &str) -> String {
    let (signature, _, _) = elaborated(source);
    let written = body(&signature, "main");
    ran(&signature, &written)
}

/// Объектные файлы рантайма: собираются однажды на весь прогон.
fn runtime() -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let dir = scratch();
        [
            "object.c",
            "array.c",
            "region.c",
            "evidence.c",
            "closure.c",
            "frame.c",
        ]
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

/// Понижение, сборка, прогон и сверка с интерпретатором. Отдаёт stderr прогона.
///
/// Понижается **специализированный** терм (трек E): §4.11 требует специализации
/// для release, и понижению проще идти по терму без словарей. Сверяется он с
/// ответом на терме **написанном** - том самом, который считает `adamas eval`.
pub(crate) fn agreed(name: &str, source: &str) -> Result<String, adamas_codegen::CompileError> {
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

/// То же **без специализации**: понижается терм, как он написан.
///
/// Нужно ровно одному свидетелю - обобщённому коду над `{Flat a}` (§4.11).
/// Специализация подставляет тип элемента и превращает шаг индексации в
/// константу; здесь она не зовётся, и шаг приходит дескриптором, который
/// словарь класса и есть. Договор тот же, что у [`agreed`]: ответ обязан
/// сойтись с `adamas eval`.
pub(crate) fn as_written(name: &str, source: &str) -> Result<String, adamas_codegen::CompileError> {
    let (signature, _, _) = elaborated(source);
    let written = body(&signature, "main");
    let expected = ran(&signature, &written);
    let text = adamas_codegen::compile(&signature, &written)?;
    let (stdout, stderr) = built(name, &text);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        expected,
        "{name}: понижение посчитало не то, что машина"
    );
    Ok(stderr)
}

/// Текст порождённого C без специализации - для свидетелей формы кода.
///
/// # Errors
///
/// [`adamas_codegen::CompileError`] - отказ понижения либо эмиссии.
pub(crate) fn written_text(source: &str) -> Result<String, adamas_codegen::CompileError> {
    let (signature, _, _) = elaborated(source);
    let written = body(&signature, "main");
    adamas_codegen::compile(&signature, &written)
}

/// Он же после специализации: то, что собирает [`agreed`].
///
/// # Errors
///
/// [`adamas_codegen::CompileError`] - отказ понижения либо эмиссии.
pub(crate) fn text(source: &str) -> Result<String, adamas_codegen::CompileError> {
    compiled(source)
}

/// Понижение `main` с вставленным RC - для свидетелей, которым нужен не текст,
/// а узлы представления.
///
/// Идёт тем же путём, что [`agreed`], и до той же точки: специализация,
/// понижение, [`adamas_codegen::perceus`]. Отличие одно - эмиссии нет, потому
/// что утверждение про **отсутствие** узла в тексте C не прочитать.
pub(crate) fn lowered(name: &str, source: &str) -> adamas_codegen::ir::Program {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = body(&signature, "main");
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .unwrap_or_else(|error| panic!("{name}: специализация отказала: {error}"));
    let program = adamas_codegen::lower::lower(&signature, &made.term)
        .unwrap_or_else(|error| panic!("{name}: понижение отказало: {error}"));
    adamas_codegen::perceus::insert(program)
}

/// Текст C либо отказ - для свидетелей названной границы.
///
/// # Errors
///
/// [`adamas_codegen::CompileError`] - ровно то, ради чего свидетель и написан.
pub(crate) fn compiled(source: &str) -> Result<String, adamas_codegen::CompileError> {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = body(&signature, "main");
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .unwrap_or_else(|error| panic!("специализация отказала: {error}"));
    adamas_codegen::compile(&signature, &made.term)
}

/// Обход дерева выражения сверху вниз.
///
/// Живёт здесь, а не рядом со своим свидетелем, потому что читают его двое -
/// плоское значение (`flat.rs`) и регион (`region.rs`), - и обход, забывший
/// узел, молча делает утверждение об **отсутствии** зелёным.
pub(crate) fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    match expr {
        Expr::Local(_)
        | Expr::Erased
        | Expr::ConstructClosure { .. }
        | Expr::Literal { .. }
        | Expr::LayoutField { .. }
        | Expr::RegionNew
        | Expr::Layout { .. } => {}
        Expr::Unpack { value, .. } => walk(value, visit),
        Expr::RegionLast { region } => walk(region, visit),
        Expr::RegionAlloc { region, value, .. } => {
            walk(region, visit);
            walk(value, visit);
        }
        Expr::RegionRead { region, at, .. } => {
            walk(region, visit);
            walk(at, visit);
        }
        Expr::RegionWrite {
            region, at, value, ..
        } => {
            walk(region, visit);
            walk(at, visit);
            walk(value, visit);
        }
        Expr::Construct { arguments, .. }
        | Expr::Call { arguments, .. }
        | Expr::Pack {
            fields: arguments, ..
        } => {
            for argument in arguments {
                walk(argument, visit);
            }
        }
        Expr::ArrayNew { count, initial, .. } => {
            walk(count, visit);
            walk(initial, visit);
        }
        Expr::ArraySet {
            array, at, value, ..
        } => {
            walk(array, visit);
            walk(at, visit);
            walk(value, visit);
        }
        Expr::ArrayIndex { array, at, .. } => {
            walk(array, visit);
            walk(at, visit);
        }
        Expr::Closure { captured, .. } => {
            for capture in captured {
                walk(capture, visit);
            }
        }
        Expr::Primitive { left, right, .. } => {
            walk(left, visit);
            walk(right, visit);
        }
        Expr::Apply { callee, argument } => {
            walk(callee, visit);
            walk(argument, visit);
        }
        Expr::Bind { value, body, .. } => {
            walk(value, visit);
            walk(body, visit);
        }
        Expr::Match {
            scrutinee, arms, ..
        } => {
            walk(scrutinee, visit);
            for arm in arms {
                walk(&arm.body, visit);
            }
        }
        Expr::Dup { body, .. } | Expr::Drop { body, .. } | Expr::Reclaim { body, .. } => {
            walk(body, visit);
        }
    }
}

/// Все связывания тела: `let` и поля ветвей.
pub(crate) fn bindings(expr: &Expr, note: &mut impl FnMut(&Binding)) {
    walk(expr, &mut |inner| match inner {
        Expr::Bind { binding, .. } => note(binding),
        Expr::Match { arms, .. } => {
            for Arm { fields, .. } in arms {
                for field in fields {
                    note(field);
                }
            }
        }
        _ => {}
    });
}

/// Связывания, названные узлами `Dup`, `Drop` и `Reclaim`.
pub(crate) fn rc_nodes(expr: &Expr, out: &mut Vec<LocalId>) {
    walk(expr, &mut |inner| match inner {
        Expr::Dup { local, .. } | Expr::Drop { local, .. } | Expr::Reclaim { local, .. } => {
            out.push(*local);
        }
        _ => {}
    });
}

/// Сколько блоков прогон выдал и сколько оставил живыми.
///
/// Читается из строки счётчиков, которую печатает точка входа: своего вывода у
/// теста нет, и врать ему нечем.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: строка счётчиков печатается точкой входа безусловно"
)]
pub(crate) fn blocks(name: &str, stderr: &str) -> (usize, usize) {
    let numbers: Vec<usize> = stderr
        .split_whitespace()
        .filter_map(|word| word.trim_end_matches(',').parse().ok())
        .collect();
    assert_eq!(
        numbers.len(),
        2,
        "{name}: счётчики блоков не прочитались из `{}`",
        stderr.trim_end()
    );
    (numbers[0], numbers[1])
}

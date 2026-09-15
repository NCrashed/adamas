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

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::ir::{Arm, Binding, Expr, LocalId};
use adamas_codegen::llvm::{Pipeline, Toolchain};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::source::SourceFile;
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
pub(crate) fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join(env!("CARGO_CRATE_NAME"));
    let _ = std::fs::create_dir_all(&dir);
    dir
}

/// Кладёт исходник на диск **атомарно** и отдаёт путь к нему.
///
/// Читать его будет отладчик: DWARF называет каталог и имя, и без файла по
/// этому пути gdb показал бы номер строки без самой строки.
///
/// Через переименование, а не записью на месте: тесты одного крейта идут
/// параллельно, кладут они **один и тот же** файл, и обычная запись усекает его
/// на время. Отладчик, прочитавший файл в этот момент, показал бы пустую
/// строку - и виноват оказался бы DWARF.
///
/// # Panics
///
/// Файл не записался либо не переименовался.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn fixture(stem: &str, text: &str) -> PathBuf {
    // Черновик свой у каждого вызова: тесты крейта - потоки одного процесса, и
    // общее имя черновика вернуло бы ту же гонку, от которой он заведён.
    static DRAFTS: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let at = DRAFTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let path = scratch().join(format!("{stem}.adamas"));
    let draft = scratch().join(format!("{stem}.{at}.adamas.part"));
    std::fs::write(&draft, text).expect("исходник обязан записываться");
    std::fs::rename(&draft, &path).expect("исходник обязан переименовываться");
    path
}

/// Понижение с исходником: программа с позициями (§9 Фаза 7, трек E).
///
/// # Panics
///
/// Исходник не разобрался, не проверился либо не понизился.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
pub(crate) fn located(stem: &str, text: &str) -> (PathBuf, adamas_codegen::ir::Program) {
    let path = fixture(stem, text);
    let (mut signature, mut metas, instances) = elaborated(text);
    let written = body(&signature, "main");
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана проходить");
    let file = SourceFile::new(path.display().to_string(), text);
    let program = adamas_codegen::lower::located(&signature, &made.term, &file)
        .expect("понижение обязано проходить");
    (path, program)
}

/// Эмиссия с исходником: `.ll` с DWARF плюс спутник.
///
/// # Panics
///
/// Исходник не разобрался, не проверился либо форма вне скалярного фрагмента.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанный корпус"
)]
pub(crate) fn llvm_located(stem: &str, text: &str) -> (PathBuf, Artefacts) {
    let path = fixture(stem, text);
    let (mut signature, mut metas, instances) = elaborated(text);
    let written = body(&signature, "main");
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .expect("специализация обязана проходить");
    let file = SourceFile::new(path.display().to_string(), text);
    let artefacts = adamas_codegen::compile_llvm_located(&signature, &made.term, &file)
        .expect("скалярный фрагмент обязан брать фикстуру");
    (path, artefacts)
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

/// Отказ **элаборации**: текст ошибки у исходника, который до понижения не
/// доходит вовсе.
///
/// Нужно свидетелям порядка: «проверка стоит раньше понижения» читается только
/// так - программа обязана быть отвергнута там, где понижения ещё нет.
///
/// # Panics
///
/// Исходник не разобрался либо, вопреки ожиданию, прошёл проверку.
#[expect(
    clippy::expect_used,
    reason = "заготовка теста: пройденная проверка означает сломанный свидетель, и падать он должен громко"
)]
pub(crate) fn rejected(source: &str) -> String {
    let module = adamas_parser::parse(source).expect("исходник обязан разбираться");
    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    let error = adamas_elab::elaborate_into(
        &module,
        &mut signature,
        &mut metas,
        &mut owned,
        &mut fixities,
        &mut instances,
        &mut warnings,
    )
    .expect_err("исходник обязан быть отвергнут проверкой");
    error.to_string()
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
        // Список приходит от самого рантайма (`build.rs`), а не написан здесь:
        // вторая копия разъезжалась бы молча, и новый слой давал бы
        // «undefined reference» вместо отказа сборки.
        env!("ADAMAS_RUNTIME_UNITS")
            .split(',')
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
fn built(name: &str, text: &str) -> (String, String) {
    built_with(name, text, &[])
}

/// Он же с дописанными ключами компилятора.
///
/// Ключи идут **после** штатных, поэтому спорящий ключ побеждает: `-O2` после
/// `-O1`, `-ffp-contract=fast` после `-ffp-contract=off`. Нужно это ровно
/// одному свидетелю - строгому режиму плавающей арифметики (`tests/float.rs`),
/// который обязан перебрать уровни оптимизации, а не поверить одному.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
pub(crate) fn built_with(name: &str, text: &str, extra: &[&str]) -> (String, String) {
    let dir = scratch();
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();

    let mut compile = Command::new(env!("ADAMAS_CC"));
    compile
        .args([
            "-std=c11",
            "-O1",
            // §4.3 требует ключ явно, и требует не зря: у clang для C
            // умолчание `on`, а `on` контрактит `a * b + c` в пределах
            // выражения. Умолчание gcc под `-std=c11` совпадает с нашим
            // выбором, но обещание не должно держаться на чужом умолчании.
            "-ffp-contract=off",
            "-Wall",
            // Порождённый код связывает поля, которых тело не смотрит, и берёт
            // вектор evidence, которого чистый фрагмент не читает: неиспользуемое
            // здесь - норма, а не находка. Неявное объявление функции - находка:
            // им ловится расхождение с заголовком рантайма.
            "-Wno-unused",
            "-Werror=implicit-function-declaration",
            // Несовместимый указатель - тоже находка, и ловит она ровно ту
            // ошибку, которая иначе сокращается: скрытые аргументы второй формы
            // различаются **типами** (`const adamas_evidence *` против
            // `adamas_kont *`), и перестановка их местами становится отсюда
            // отказом сборки, а не молчанием.
            "-Werror=incompatible-pointer-types",
        ])
        .args(extra)
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
/// Шаг берётся у самого представления ([`Expr::children`]): свой обход у
/// свидетеля означал бы, что утверждение об **отсутствии** узла зеленеет молча,
/// стоит представлению вырасти.
pub(crate) fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
    visit(expr);
    for child in expr.children() {
        walk(child, visit);
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
///
/// Поля схлопнутого дропа (`Salvage`) сюда входят наравне с прочими: `dup` по
/// ним уехал внутрь узла, и обход, не спросивший его, объявил бы счёт по
/// плоскому отсутствующим просто потому, что перестал его видеть.
pub(crate) fn rc_nodes(expr: &Expr, out: &mut Vec<LocalId>) {
    walk(expr, &mut |inner| match inner {
        Expr::Dup { local, .. } => out.push(*local),
        Expr::Drop { local, salvage, .. } | Expr::Reclaim { local, salvage, .. } => {
            out.push(*local);
            out.extend(salvage.locals());
        }
        _ => {}
    });
}

/// Несёт ли конвейер рантайм в себе - то есть есть ли в нём `llvm-link`.
///
/// Читается у самого конвейера, потому что это его свойство: приложенный `.bc`
/// приносит определения рантайма в объектник, и вторая их копия с компоновщика
/// - ошибка, а не дубликат.
pub(crate) fn carries_runtime(pipeline: &Pipeline) -> bool {
    pipeline
        .stages
        .iter()
        .any(|stage| stage.tool == "llvm-link")
}

/// Переменная, называющая clang той же версии, что `ADAMAS_LLVM_BIN`.
///
/// Не `ADAMAS_CC`: тот приходит от `cc`-крейта и в dev-shell есть gcc, а
/// битового кода LLVM gcc не выдаёт. Путём, а не каталогом в `PATH`, - обёртка
/// clang кладёт рядом с собой `cc`, и попади она в `PATH`, весь порождённый C
/// собирался бы ею молча.
pub(crate) const CLANG_VARIABLE: &str = "ADAMAS_CLANG";

/// Рантайм целиком одним `.bc`: собирается однажды на весь прогон.
///
/// Нужен стадии `llvm-link` ([`Pipeline::whole_program`]), и без него `opt` не
/// видит сквозь `adamas_dup`.
///
/// # Host-атрибуты снимаются, и это не косметика
///
/// clang вешает на каждую функцию `target-cpu` и `target-features` хоста.
/// Порождённый `.ll` не несёт ни того, ни другого - строк цели в нём нет
/// намеренно, - а инлайнер требует, чтобы набор возможностей **вызываемого**
/// был подмножеством набора **вызывающего**. Пустой набор у вызывающего делает
/// подмножеством только пустой, и рантайм не инлайнится ни разу: измерено
/// 2026-09-15, со стадией и без неё вызовов остаётся поровну.
///
/// Снимаются они здесь, а не дописываются там: `.bc` рантайма собран под хост и
/// им же компилируется дальше, а `.ll` обязан остаться переносимым. Цена
/// названная - рантайм оптимизируется под базовую линию архитектуры, а не под
/// хост; на восьми функциях счётчика это не наблюдаемо, и наблюдаемым станет,
/// когда в рантайме появится что-то векторизуемое.
///
/// # Panics
///
/// Нет clang либо не собралось: молчаливый пропуск здесь был бы обманчивым
/// свидетелем ровно так же, как отсутствие LLVM.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn runtime_bitcode(tools: &Toolchain) -> PathBuf {
    static BITCODE: OnceLock<PathBuf> = OnceLock::new();
    BITCODE
        .get_or_init(|| {
            let clang = std::env::var_os(CLANG_VARIABLE)
                .filter(|it| !it.is_empty())
                .unwrap_or_else(|| {
                    panic!("`{CLANG_VARIABLE}` не задан, а в dev-shell он есть: рантайм в `.bc` собрать нечем")
                });
            let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
            let dir = scratch();
            let mut parts = Vec::new();
            for name in env!("ADAMAS_RUNTIME_UNITS").split(',') {
                let raw = dir.join(format!("{name}.raw.bc"));
                let made = Command::new(&clang)
                    .args(["-std=c11", "-O1", "-emit-llvm", "-c"])
                    .arg("-I")
                    .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                    .arg(sources.join(name))
                    .arg("-o")
                    .arg(&raw)
                    .output()
                    .unwrap();
                assert!(
                    made.status.success(),
                    "рантайм не собрался в `.bc`: {name}\n{}",
                    String::from_utf8_lossy(&made.stderr)
                );
                parts.push(stripped(tools, &dir, name, &raw));
            }
            let linked = dir.join("runtime.bc");
            let done = Command::new(tools.tool("llvm-link"))
                .args(&parts)
                .arg("-o")
                .arg(&linked)
                .output()
                .unwrap();
            assert!(
                done.status.success(),
                "рантайм не слинковался в один `.bc`:\n{}",
                String::from_utf8_lossy(&done.stderr)
            );
            linked
        })
        .clone()
}

/// Тот же `.bc` без host-атрибутов: через текст, потому что паса под это нет.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn stripped(tools: &Toolchain, dir: &Path, name: &str, raw: &Path) -> PathBuf {
    let text = dir.join(format!("{name}.raw.ll"));
    let shown = Command::new(tools.tool("llvm-dis"))
        .arg(raw)
        .arg("-o")
        .arg(&text)
        .output()
        .unwrap();
    assert!(shown.status.success(), "`{name}.bc` не разобрался обратно");
    let plain = without_host_attributes(&std::fs::read_to_string(&text).unwrap());
    let cleaned = dir.join(format!("{name}.plain.ll"));
    std::fs::write(&cleaned, plain).unwrap();
    let object = dir.join(format!("{name}.bc"));
    let back = Command::new(tools.tool("llvm-as"))
        .arg(&cleaned)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        back.status.success(),
        "`{name}` без host-атрибутов не собрался:\n{}",
        String::from_utf8_lossy(&back.stderr)
    );
    object
}

/// Текст IR без `target-cpu`, `target-features` и `tune-cpu`.
pub(crate) fn without_host_attributes(text: &str) -> String {
    let mut out = text.to_owned();
    for key in [
        "\"target-cpu\"=\"",
        "\"target-features\"=\"",
        "\"tune-cpu\"=\"",
    ] {
        while let Some(at) = out.find(key) {
            let value = at + key.len();
            let Some(end) = out[value..].find('"') else {
                break;
            };
            let stop = value + end + 1;
            let start = usize::from(at > 0 && out.as_bytes()[at - 1] == b' ');
            out.replace_range(at - start..stop, "");
        }
    }
    out
}

/// Сколько раз IR зовёт названную точку входа рантайма.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn calls(tools: &Toolchain, bitcode: &Path, names: &[&str]) -> Vec<usize> {
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
    names
        .iter()
        .map(|name| {
            read.lines()
                .filter(|line| line.contains("call ") && line.contains(&format!("@{name}(")))
                .count()
        })
        .collect()
}

/// Собирает `.ll` со спутником и запускает. Отдаёт stdout и stderr.
///
/// Путь ровно тот, что назван решением 2026-09-15: текст `.ll` -> `llvm-as` ->
/// `opt` -> `llc` -> объектник -> линковка с рантаймом. Спутник на C собирается
/// **тем же** компилятором, каким собран рантайм, и линкуется рядом.
///
/// `stem` отличает артефакты одной программы, прогнанной двумя цепочками:
/// файлы иначе перезаписывали бы друг друга, и вторая проверка мерила бы
/// объектник первой.
///
/// Объектники рантайма прикладываются, **если конвейер их ещё не приложил**.
/// Спрашивается это у самого конвейера ([`carries_runtime`]), а не флагом с
/// места вызова: приложи их дважды - и компоновщик отвергнет программу
/// дублирующимися определениями, то есть проверка сломалась бы там, где о
/// рантайме речи нет.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
pub(crate) fn llvm_built(
    stem: &str,
    artefacts: &Artefacts,
    tools: &Toolchain,
    pipeline: &Pipeline,
) -> (String, String) {
    let binary = llvm_binary(stem, artefacts, tools, pipeline);
    let run = Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "{stem}: прогон оборвался:\n{}",
        String::from_utf8_lossy(&run.stderr)
    );
    (
        String::from_utf8(run.stdout).unwrap(),
        String::from_utf8(run.stderr).unwrap(),
    )
}

/// Объектник из текста `.ll` названным конвейером.
///
/// Отдельно от [`llvm_built`], потому что отладочная информация читается
/// **из объектника** (`llvm-dwarfdump`), а не из прогона: сборка, потерявшая
/// метаданные, считает то же самое и молчит об этом.
///
/// # Panics
///
/// Конвейер отказал либо файл не записался.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn llvm_object(
    stem: &str,
    artefacts: &Artefacts,
    tools: &Toolchain,
    pipeline: &Pipeline,
) -> PathBuf {
    let text = scratch().join(format!("{stem}.ll"));
    std::fs::write(&text, &artefacts.ll).unwrap();
    pipeline
        .run(tools, &text, stem)
        .unwrap_or_else(|error| panic!("{stem}: конвейер LLVM отказал: {error}"))
}

/// Собранный и слинкованный бинарь: объектник, спутник, рантайм.
///
/// Отдельно от прогона ради отладчика: сеанс запускает программу сам, и
/// запущенная дважды она печатала бы счётчики блоков в чужой лог.
///
/// # Panics
///
/// Спутник не собрался либо линковка отказала.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn llvm_binary(
    stem: &str,
    artefacts: &Artefacts,
    tools: &Toolchain,
    pipeline: &Pipeline,
) -> PathBuf {
    let object = llvm_object(stem, artefacts, tools, pipeline);
    // Объектники рантайма прикладываются, **если конвейер их ещё не приложил**.
    // Спрашивается это у самого конвейера ([`carries_runtime`]), а не флагом с
    // места вызова: приложи их дважды - и компоновщик отвергнет программу
    // дублирующимися определениями, то есть проверка сломалась бы там, где о
    // рантайме речи нет.
    llvm_linked(
        stem,
        &object,
        &artefacts.support,
        !carries_runtime(pipeline),
    )
}

/// Линкует готовый объектник со спутником и, если просят, с рантаймом.
///
/// # Panics
///
/// Спутник не собрался либо линковка отказала.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn llvm_linked(
    stem: &str,
    object: &Path,
    support_text: &str,
    with_runtime: bool,
) -> PathBuf {
    let dir = scratch();
    let support = dir.join(format!("{stem}.support.c"));
    let support_object = dir.join(format!("{stem}.support.o"));
    std::fs::write(&support, support_text).unwrap();
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args([
            "-std=c11",
            "-O1",
            "-Wall",
            "-Wno-unused",
            "-Werror=implicit-function-declaration",
            "-c",
        ])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&support)
        .arg("-o")
        .arg(&support_object)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{stem}: спутник не собрался:\n{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let binary = dir.join(format!("{stem}.bin"));
    let mut link = Command::new(env!("ADAMAS_CC"));
    link.arg(object).arg(&support_object);
    if with_runtime {
        link.args(runtime());
    }
    let linked = link.arg("-o").arg(&binary).output().unwrap();
    assert!(
        linked.status.success(),
        "{stem}: линковка отказала:\n{}",
        String::from_utf8_lossy(&linked.stderr)
    );
    binary
}

/// Понижение в LLVM, сборка, прогон и сверка с интерпретатором.
///
/// Свидетель - **машина**, а не записанное руками ожидание: тот же договор, в
/// котором стоят первые два вычислителя (`agreement.rs`).
///
/// # Errors
///
/// [`adamas_codegen::CompileError`] - форма вне скалярного фрагмента.
pub(crate) fn llvm_agreed(
    name: &str,
    source: &str,
    tools: &Toolchain,
    pipeline: &Pipeline,
    stem: &str,
) -> Result<(String, String), adamas_codegen::CompileError> {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = body(&signature, "main");
    let expected = ran(&signature, &written);
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .unwrap_or_else(|error| panic!("{name}: специализация отказала: {error}"));

    let artefacts = adamas_codegen::compile_llvm(&signature, &made.term)?;
    let (stdout, stderr) = llvm_built(stem, &artefacts, tools, pipeline);
    let printed = stdout.trim_end_matches('\n').to_owned();
    assert_eq!(printed, expected, "{name}: LLVM посчитал не то, что машина");
    Ok((printed, stderr))
}

/// Что дал прогон названного текста: ответ и счётчики блоков.
///
/// Счётчики здесь **обязательны**, а не для полноты: правка, ломающая владение,
/// оставляет ответ тем же и видна только числом выданного и живого. Мутант,
/// которого не отличить ни ответом, ни счётчиком, ничего и не проверяет.
pub(crate) struct Mutated {
    /// Что ушло в stdout - ответ либо слово с причиной обрыва.
    pub(crate) printed: String,
    /// Сколько блоков выдано; `None` - строки счётчиков не было.
    pub(crate) allocated: Option<usize>,
    /// Сколько осталось живыми.
    pub(crate) live: Option<usize>,
}

/// Прогон **названного текста** `.ll`: тот же путь, но обрыв - ответ.
///
/// Отличие от [`llvm_built`] одно и существенное: там неудача прогона роняет
/// тест, здесь она **наблюдение**. Нужно это двум свидетелям. Мутанту:
/// сломанный код вправе сломаться, и сравнивать довольно слова с причиной.
/// И свидетелю хвостовых вызовов (`tail.rs`): переполнение стека там и есть
/// то, что мерится, а не поломка окружения.
///
/// Прогон ограничен по времени. Не украшение: правка, оставляющая счётчик
/// расти, превращает цикл в бесконечный, и без предела мутант вешал бы прогон
/// вместо того, чтобы отличаться ответом. Вывод читается после ожидания -
/// он короче трубы, и заполнить её не может.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn llvm_printed(
    stem: &str,
    text: &str,
    support: &str,
    tools: &Toolchain,
    pipeline: &Pipeline,
) -> Mutated {
    let dir = scratch();
    let source = dir.join(format!("{stem}.ll"));
    std::fs::write(&source, text).unwrap();
    let Ok(object) = pipeline.run(tools, &source, stem) else {
        return Mutated {
            printed: "IR отвергнут".to_owned(),
            allocated: None,
            live: None,
        };
    };

    let support_source = dir.join(format!("{stem}.support.c"));
    let support_object = dir.join(format!("{stem}.support.o"));
    std::fs::write(&support_source, support).unwrap();
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1", "-Wno-unused", "-c"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&support_source)
        .arg("-o")
        .arg(&support_object)
        .output()
        .unwrap();
    assert!(compiled.status.success(), "{stem}: спутник не собрался");

    let binary = dir.join(format!("{stem}.bin"));
    let linked = Command::new(env!("ADAMAS_CC"))
        .arg(&object)
        .arg(&support_object)
        .args(runtime())
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    if !linked.status.success() {
        return Mutated {
            printed: "не слинковался".to_owned(),
            allocated: None,
            live: None,
        };
    }
    within(&binary, std::time::Duration::from_secs(20))
}

/// Прогон с пределом по времени. Отдаёт напечатанное, причину и счётчики.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn within(binary: &Path, limit: std::time::Duration) -> Mutated {
    let mut child = Command::new(binary)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + limit;
    loop {
        match child.try_wait().unwrap() {
            Some(status) => {
                use std::io::Read as _;
                let mut printed = String::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_string(&mut printed);
                }
                let mut counted = String::new();
                if let Some(mut err) = child.stderr.take() {
                    let _ = err.read_to_string(&mut counted);
                }
                let numbers: Vec<usize> = counted
                    .split_whitespace()
                    .filter_map(|word| word.trim_end_matches(',').parse().ok())
                    .collect();
                let printed = if status.success() {
                    printed.trim_end_matches('\n').to_owned()
                } else {
                    "прогон оборвался".to_owned()
                };
                return Mutated {
                    printed,
                    allocated: numbers.first().copied(),
                    live: numbers.get(1).copied(),
                };
            }
            None if std::time::Instant::now() >= deadline => {
                let _ = child.kill();
                let _ = child.wait();
                return Mutated {
                    printed: "прогон не завершился".to_owned(),
                    allocated: None,
                    live: None,
                };
            }
            None => std::thread::sleep(std::time::Duration::from_millis(20)),
        }
    }
}

/// Текст `.ll` без сборки - для свидетелей формы IR и для мутантов.
///
/// # Errors
///
/// [`adamas_codegen::CompileError`] - форма вне скалярного фрагмента.
pub(crate) fn llvm_text(
    name: &str,
    source: &str,
) -> Result<Artefacts, adamas_codegen::CompileError> {
    let (mut signature, mut metas, instances) = elaborated(source);
    let written = body(&signature, "main");
    let made = mono::specialise(&mut signature, &mut metas, &instances, &written)
        .unwrap_or_else(|error| panic!("{name}: специализация отказала: {error}"));
    adamas_codegen::compile_llvm(&signature, &made.term)
}

/// Цепочки инструментов - штатная и минимальная, - либо объявленное отсутствие.
///
/// `None` только при `ADAMAS_LLVM=absent`. Всё остальное - отказ: инструмент,
/// которого нет, обязан ронять прогон, а не молчать. Исключение объявлено в
/// одном месте (`.github/workflows/ci.yml`, нога macOS), где LLVM в образе
/// раннера нет; и правило это - **одно** на всех свидетелей LLVM-пути, потому
/// что вторая его запись разъехалась бы с первой молча.
pub(crate) fn llvm_toolchains() -> Option<(Toolchain, Toolchain)> {
    if std::env::var("ADAMAS_LLVM").is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим (ADAMAS_LLVM=absent): договор не проверялся");
        return None;
    }
    Some((
        Toolchain::from_variable(adamas_codegen::llvm::TOOLS_VARIABLE),
        Toolchain::from_variable(adamas_codegen::llvm::MINIMUM_TOOLS_VARIABLE),
    ))
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

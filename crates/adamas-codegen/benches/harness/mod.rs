//! Общее двум стендам: сборка порождённого C, запуск процессом, пол выборки.
//!
//! Живёт отдельно по той же причине, по какой отдельно живёт
//! `tests/harness/mod.rs`: бенчмарк - свой крейт, а сборка рантайма, строка
//! release и оценка полом нужны обоим. Вторая копия здесь была бы не
//! неудобством, а разъездом: строка сборки [`RELEASE`] стоила **99%** разрыва
//! с соседом (замер 2026-09-13), и стенд, разошедшийся с ней на один флаг,
//! отвечал бы числом, которое ни с чем не сравнивается. Прецедент свежий -
//! список единиц трансляции рантайма лежал в четырёх местах копиями, и новый
//! слой дал «undefined reference» в двух из них.
//!
//! **Методика живёт не здесь**, а в шапке `native.rs`, разделом «Методика».
//! Здесь только её механика; читать надо там.
//!
//! Второй столбец таблицы трека Z (LLVM против C) собирается тоже здесь -
//! разделом «LLVM-путь» ниже, - потому что уравнивание строк сборки нужно обоим
//! стендам одинаково, а разъехавшись, они дали бы два несравнимых числа под
//! одним именем.

// Модуль компилируется в каждый стенд целиком, а нужен каждому не весь:
// `paired`-протокол берёт только `native`, соседа-процесс - оба, но с разным
// запросом.
#![allow(dead_code, reason = "общий модуль двух стендов")]
#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    reason = "заготовка бенчмарка: отказ здесь означает сломанный стенд, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use adamas_codegen::emit_llvm::Artefacts;
use adamas_codegen::llvm::{Pipeline, Stage, Toolchain, without_host_attributes};
use adamas_core::level::Level;
use adamas_core::meta::Metas;
use adamas_core::row::Row;
use adamas_core::sig::Signature;
use adamas_core::term::Term;
use adamas_elab::class::Instances;
use adamas_elab::fixity::Fixities;
use adamas_elab::{Owned, Warnings};

// --- программа берётся у корпуса -----------------------------------------

/// Путь к корпусной фикстуре по имени - без расширения.
pub(crate) fn corpus_path(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval")
        .join(format!("{name}.adamas"))
}

/// Текст корпусной фикстуры по имени - без расширения.
///
/// Нагрузка обязана быть **программой в корпусе**, а не программой в стенде:
/// корпусную прогоняет машина и сверяет с понижением договор трёх
/// вычислителей (`tests/agreement.rs`), стендовую не сверяет никто. Копий при
/// этом две быть не может: разъехавшись, они мерили бы одно, а проверяли
/// другое, и заметить это было бы нечем. Поэтому стенд читает **тот же файл**,
/// а размеры подставляет [`resized`].
pub(crate) fn corpus(name: &str) -> String {
    let path = corpus_path(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("корпусная фикстура {}: {error}", path.display()))
}

/// Та же программа с переписанными размерами.
///
/// Размер живёт в программе **именованной константой на своей строке**
/// (`cells = 8`), и подставить его значит переписать одну строку. Больше
/// стенду в корпусной программе менять нечего - в этом и смысл: разойтись двум
/// сторонам негде, потому что сторона одна.
///
/// Подстановка обязана быть честной, и это проверяется, а не подразумевается:
/// имя, встретившееся не ровно один раз, роняет стенд. Переименуй кто-нибудь
/// `cells` в корпусе - и стенд упадёт вместо того, чтобы тихо померить
/// корпусный размер.
pub(crate) fn resized(text: &str, sizes: &[(&str, u64)]) -> String {
    let mut out = text.to_owned();
    for (name, value) in sizes {
        let head = format!("{name} = ");
        let mut hit = 0_usize;
        let mut next = String::with_capacity(out.len());
        for line in out.lines() {
            match line.strip_prefix(&head) {
                Some(rest) if !rest.is_empty() && rest.bytes().all(|it| it.is_ascii_digit()) => {
                    hit += 1;
                    next.push_str(&head);
                    next.push_str(&value.to_string());
                }
                _ => next.push_str(line),
            }
            next.push('\n');
        }
        assert_eq!(
            hit, 1,
            "строк `{name} = <число>` в корпусной программе {hit}, а подстановка \
             требует ровно одной"
        );
        out = next;
    }
    out
}

// --- элаборация ----------------------------------------------------------

/// Элаборированная программа вместе с тем, что о ней знает разрешение.
pub(crate) fn elaborated(source: &str) -> (Signature, Metas, Instances) {
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

/// Тело `main` с подставленными аргументами уровня и row — то, что вычисляет
/// `adamas eval`.
pub(crate) fn entry(signature: &Signature) -> Term {
    let definition = signature.lookup("main").expect("`main` объявлен");
    let body = definition.body.as_ref().expect("у `main` есть тело");
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    body.substitute_levels(&levels).substitute_rows(&rows)
}

// --- порождённый C -------------------------------------------------------

/// Место под порождённый C и его сборку — своё у каждого стенда.
pub(crate) fn scratch(stand: &str) -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join(stand);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Строка сборки release: уровень оптимизации и межмодульная оптимизация.
///
/// `-O2`, а не `-O1` тестового харнесса: замер говорит о том, что получит
/// пользователь release-сборкой, и уровень оптимизации — часть окружения,
/// которое число обязано нести рядом с собой.
///
/// `-flto` здесь по той же причине и ещё по одной. Порождённый C и рантайм —
/// разные единицы трансляции, а горячий путь состоит из вызовов в рантайм:
/// `adamas_tag`, `adamas_field`, `adamas_dup`, `adamas_drop`. Каждый из них —
/// несколько инструкций, и без межмодульной оптимизации вызов дороже тела.
/// `adamas.h` называет это прямо: «Функции не `static inline`: горячий путь
/// ждёт LTO». Сосед на Rust собирается профилем `release` этого репозитория, а
/// он — `lto = "thin"`; без флага здесь сравнивались бы не два понижения, а
/// собранное межмодульно с собранным по отдельности. Измерено 2026-09-13:
/// флаг снимает **99% разрыва** с соседом (пофазно в процессе на глубине 18:
/// 42.3 мс против 17.7 при 17.6 у соседа).
pub(crate) const RELEASE: [&str; 3] = ["-std=c11", "-O2", "-flto"];

/// Объектные файлы рантайма: собираются однажды на весь прогон.
pub(crate) fn runtime(dir: &Path) -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        // Список приходит от самого рантайма (`build.rs`), а не написан здесь.
        env!("ADAMAS_RUNTIME_UNITS")
            .split(',')
            .map(|name| {
                let object = dir.join(format!("{name}.o"));
                let status = Command::new(env!("ADAMAS_CC"))
                    .args(RELEASE)
                    .arg("-c")
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

/// Та же строка **без** межмодульной оптимизации: только свидетелю.
///
/// Мерить ею нечего - число, снятое так, недействительно по «Методике». Нужна
/// она ровно одному наблюдению: второй столбец таблицы сравнивает бэкенды,
/// собранные разными цепочками, и «мы сравниваем коды, а не строки сборки»
/// обязано быть **предъявлено**, а не обещано. Предъявляется оно ценой:
/// сколько стоит C-стороне отнятая межмодульная оптимизация.
pub(crate) const RELEASE_APART: [&str; 2] = ["-std=c11", "-O2"];

/// Объектники рантайма, собранные [`RELEASE_APART`]: свои у свидетеля.
///
/// Свои, потому что `-flto` меняет содержимое объектника, а не только линковку:
/// приложи к сборке без него объектники с битовым кодом - и получишь третью
/// цепочку, ни на что не похожую.
fn runtime_apart(dir: &Path) -> &'static [PathBuf] {
    static OBJECTS: OnceLock<Vec<PathBuf>> = OnceLock::new();
    OBJECTS.get_or_init(|| {
        let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
        let apart = dir.join("apart");
        std::fs::create_dir_all(&apart).unwrap();
        env!("ADAMAS_RUNTIME_UNITS")
            .split(',')
            .map(|name| {
                let object = apart.join(format!("{name}.o"));
                let status = Command::new(env!("ADAMAS_CC"))
                    .args(RELEASE_APART)
                    .arg("-c")
                    .arg("-I")
                    .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
                    .arg(sources.join(name))
                    .arg("-o")
                    .arg(&object)
                    .status();
                assert!(
                    status.is_ok_and(|status| status.success()),
                    "рантайм не собрался без LTO: {name}"
                );
                object
            })
            .collect()
    })
}

/// Собирает порождённый C в исполняемый файл.
pub(crate) fn built(dir: &Path, name: &str, text: &str) -> PathBuf {
    let source = dir.join(format!("{name}.c"));
    let binary = dir.join(name);
    std::fs::write(&source, text).unwrap();
    compiled(dir, &source, &binary);
    binary
}

/// Он же **без** межмодульной оптимизации: свидетель строки сборки.
pub(crate) fn built_apart(dir: &Path, name: &str, text: &str) -> PathBuf {
    let source = dir.join(format!("{name}.apart.c"));
    let binary = dir.join(format!("{name}.apart"));
    std::fs::write(&source, text).unwrap();
    let output = Command::new(env!("ADAMAS_CC"))
        .args(RELEASE_APART)
        .args(["-fwrapv", "-ffp-contract=off", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(runtime_apart(dir))
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "порождённый C не собрался без LTO:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    binary
}

/// Вызов компилятора C — отдельно, потому что он же и мерится.
pub(crate) fn compiled(dir: &Path, source: &Path, binary: &Path) {
    let output = Command::new(env!("ADAMAS_CC"))
        .args(RELEASE)
        // `-ffp-contract=off` — требование §4.3, а не осторожность стенда:
        // `workload-column` считает ровно `x·gain + bias`, и разрешённая
        // контракция дала бы другие числа. Умолчание gcc под `-std=c11`
        // совпадает, но обещание не должно держаться на чужом умолчании.
        .args(["-fwrapv", "-ffp-contract=off", "-w"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(source)
        .args(runtime(dir))
        .arg("-o")
        .arg(binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "порождённый C не собрался:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Прогон собранной программы: ответ на stdout, счётчики блоков на stderr.
pub(crate) fn ran(binary: &Path) -> (String, String) {
    let output = Command::new(binary).output().unwrap();
    assert!(
        output.status.success(),
        "прогон оборвался: {}",
        output.status
    );
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// Сколько блоков прогон выдал и сколько оставил живыми.
///
/// Читается из строки счётчиков, которую печатает точка входа. Для FBIP это
/// не украшение отчёта, а свидетель: проход, переписывающий ячейку на месте,
/// от прохода, роняющего её и берущего новую, отличается **здесь**, а не во
/// времени.
pub(crate) fn blocks(stderr: &str) -> (usize, usize) {
    let numbers: Vec<usize> = stderr
        .split_whitespace()
        .filter_map(|word| word.trim_end_matches(',').parse().ok())
        .collect();
    assert_eq!(
        numbers.len(),
        2,
        "счётчики блоков не прочитались из `{}`",
        stderr.trim_end()
    );
    (numbers[0], numbers[1])
}

// --- LLVM-путь: второй столбец таблицы трека Z ----------------------------
//
// Половина таблицы, снятая волной 5 Фазы 6, сравнивает понижение через C с
// соседом на Rust. Второй столбец сравнивает **два бэкенда между собой**, и
// главный риск здесь назван Фазой 6 числом: 99% измеренного тогда разрыва
// оказались строкой сборки, а не кодом. Сборочные пути двух бэкендов
// различаются по построению - C идёт `gcc -O2 -flto`, LLVM идёт
// `llvm-as`/`llvm-link`/`opt -O2`/`llc`, - поэтому всё, что можно уравнять,
// уравнивается здесь, а то, что нельзя, мерится отдельно и называется числом.
//
// Что уравнено:
//
// - **Межмодульная оптимизация у обоих.** У C её даёт `-flto` ([`RELEASE`]):
//   порождённый код и рантайм собираются вместе. У LLVM - стадия `llvm-link`
//   ([`Pipeline::whole_program`]), приносящая рантайм битовым кодом **до**
//   `opt -O2`. Без неё рантайм приезжает готовым объектником, и число мерило
//   бы LTO, а не бэкенд (замер трека A, подтверждено A′).
// - **Уровень оптимизации рантайма.** `.bc` собирается clang'ом с тем же
//   `-O2`, каким gcc собирает объектники рантайма для C-стороны.
// - **Базовая линия архитектуры у обоих.** `gcc -O2` без `-march` берёт
//   generic; `llc` без `-mcpu` берёт его же; host-атрибуты с `.bc` снимаются
//   ([`without_host_attributes`]) - иначе инлайнер откажет всем.
// - **Спутник и линковка - той же строкой.** Спутник на C собирается теми же
//   ключами [`RELEASE`], каким собран порождённый C, и линкуется тем же
//   драйвером.
//
// Чего уравнять нельзя: объектник программы у C рождается внутри LTO-раздела
// gcc, у LLVM - отдельным `llc`. Это и есть различие бэкендов, ради которого
// столбец мерится; свидетелем того, что оно не различие **строк**, служит счёт
// вызовов рантайма в готовом бинаре у обеих сторон.

/// Переменная, которой объявляется отсутствие LLVM.
///
/// Правило то же и **одно** с тестовой заготовкой: инструмента нет - прогон
/// падает, а не молчит. Молчаливый пропуск дал бы столбец, пустой не потому,
/// что бэкенд не берёт нагрузку, а потому, что стенд не нашёл `llvm-as`.
pub(crate) const LLVM_ABSENT: &str = "ADAMAS_LLVM";

/// Переменная, называющая clang той же версии, что `ADAMAS_LLVM_BIN`.
pub(crate) const CLANG_VARIABLE: &str = "ADAMAS_CLANG";

/// Цепочка LLVM либо объявленное отсутствие.
pub(crate) fn llvm_tools() -> Option<Toolchain> {
    if std::env::var(LLVM_ABSENT).is_ok_and(|it| it == "absent") {
        eprintln!("LLVM объявлен отсутствующим ({LLVM_ABSENT}=absent): второй столбец не мерился");
        return None;
    }
    // Без clang'а столбец не мерится: рантайм в `.bc` собрать нечем. Решается
    // это здесь, а не у [`runtime_bitcode`], чтобы «столбец измерим» решало
    // одно место; иначе стенд доходит до сборки и падает - так и упал
    // `bench compiles` на CI, где у джобы переменных нет вовсе.
    if std::env::var_os(CLANG_VARIABLE).is_none_or(|it| it.is_empty()) {
        eprintln!(
            "`{CLANG_VARIABLE}` не задан: рантайм в `.bc` собрать нечем, второй столбец не мерился"
        );
        return None;
    }
    Some(Toolchain::from_variable(
        adamas_codegen::llvm::TOOLS_VARIABLE,
    ))
}

/// Рантайм целиком одним `.bc` без host-атрибутов: собирается раз на прогон.
///
/// `-O2`, а не `-O1` тестовой заготовки: у C-стороны объектники рантайма идут
/// [`RELEASE`], то есть `-O2 -flto`, и рантайм, собранный слабее, отдал бы
/// LLVM-стороне отставание, к бэкенду отношения не имеющее.
pub(crate) fn runtime_bitcode(tools: &Toolchain, dir: &Path) -> PathBuf {
    static BITCODE: OnceLock<PathBuf> = OnceLock::new();
    BITCODE
        .get_or_init(|| {
            let clang = std::env::var_os(CLANG_VARIABLE)
                .filter(|it| !it.is_empty())
                .unwrap_or_else(|| {
                    panic!(
                        "`{CLANG_VARIABLE}` не задан, а в dev-shell он есть: \
                         рантайм в `.bc` собрать нечем"
                    )
                });
            let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
            let mut parts = Vec::new();
            for name in env!("ADAMAS_RUNTIME_UNITS").split(',') {
                let raw = dir.join(format!("{name}.raw.bc"));
                let made = Command::new(&clang)
                    .args(["-std=c11", "-O2", "-emit-llvm", "-c"])
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
                parts.push(plain_bitcode(tools, dir, name, &raw));
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
fn plain_bitcode(tools: &Toolchain, dir: &Path, name: &str, raw: &Path) -> PathBuf {
    let text = dir.join(format!("{name}.raw.ll"));
    let shown = Command::new(tools.tool("llvm-dis"))
        .arg(raw)
        .arg("-o")
        .arg(&text)
        .output()
        .unwrap();
    assert!(shown.status.success(), "`{name}.bc` не разобрался обратно");
    let cleaned = dir.join(format!("{name}.plain.ll"));
    std::fs::write(
        &cleaned,
        without_host_attributes(&std::fs::read_to_string(&text).unwrap()),
    )
    .unwrap();
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

/// Как приезжает спутник на C: печать ответа, дроп его детей, точка входа.
///
/// Развилка не косметическая, и это измерено. У C-стороны `print.c`,
/// `release.c` и `main.c` лежат **в том же файле**, что и программа
/// (`include_str!` в эмиттере), то есть попадают в ту же единицу оптимизации.
/// У LLVM-стороны спутник исходно приезжал отдельной единицей трансляции, и
/// `adamas_release_extern` в ней оставался непрозрачным для `opt` - названный
/// долг трека A′. На FBIP-нагрузке дроп зовётся на ячейку, так что граница
/// стоит времени, и оно ушло бы в столбец под видом качества бэкенда.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Support {
    /// Штатно: битовым кодом в ту же стадию `llvm-link`, что и рантайм.
    ///
    /// Это и уравнивает LLVM-сторону с C-стороной: программа и спутник
    /// оптимизируются вместе у обоих.
    Bitcode,
    /// Свидетель: отдельной единицей трансляции названного уровня.
    Object(&'static str),
}

impl Backend {
    /// Собирает `.ll` со спутником в исполняемый файл.
    fn built(
        &self,
        name: &str,
        artefacts: &Artefacts,
        pipeline: &Pipeline,
        support: Support,
    ) -> PathBuf {
        let dir = scratch(self.stand);
        let text = dir.join(format!("{name}.ll"));
        std::fs::write(&text, &artefacts.ll).unwrap();

        // Спутник битовым кодом уезжает **внутрь** конвейера, объектником -
        // на линковку. Отсюда и ветвление: конвейер у двух форм разный.
        let mut pipeline = pipeline.clone();
        let mut support_object = None;
        match support {
            Support::Bitcode => {
                let bitcode = self.support_bitcode(&dir, name, &artefacts.support);
                let at = pipeline
                    .stages
                    .iter()
                    .position(|stage| stage.tool == "llvm-link")
                    .unwrap_or_else(|| {
                        pipeline
                            .stages
                            .insert(1, Stage::new("llvm-link", &[], "linked.bc"));
                        1
                    });
                pipeline.stages[at]
                    .arguments
                    .push(bitcode.display().to_string());
            }
            Support::Object(level) => {
                support_object = Some(Self::support_object(&dir, name, &artefacts.support, level));
            }
        }

        let object = pipeline
            .run(&self.tools, &text, name)
            .unwrap_or_else(|error| panic!("{name}: конвейер LLVM отказал: {error}"));

        let binary = dir.join(format!("{name}.llvm"));
        let mut link = Command::new(env!("ADAMAS_CC"));
        link.arg(&object);
        if let Some(support_object) = &support_object {
            link.arg(support_object);
        }
        // Объектники рантайма прикладываются, **если конвейер их ещё не
        // приложил**: приложи их дважды - и компоновщик отвергнет программу
        // дублирующимися определениями. Спрашивается это у самого конвейера, а
        // не флагом с места вызова, и спрашивается про **рантайм**, а не про
        // стадию: стадия бывает заведена одним спутником.
        let carried = pipeline.stages.iter().any(|stage| {
            stage
                .arguments
                .iter()
                .any(|argument| argument == &self.runtime.display().to_string())
        });
        if !carried {
            link.args(runtime(&dir));
        }
        let linked = link.args(RELEASE).arg("-o").arg(&binary).output().unwrap();
        assert!(
            linked.status.success(),
            "{name}: линковка отказала:\n{}",
            String::from_utf8_lossy(&linked.stderr)
        );
        binary
    }

    /// Спутник битовым кодом, без host-атрибутов - по тому же доводу, что и
    /// рантайм: инлайнер требует подмножества возможностей.
    fn support_bitcode(&self, dir: &Path, name: &str, text: &str) -> PathBuf {
        let clang = std::env::var_os(CLANG_VARIABLE)
            .filter(|it| !it.is_empty())
            .unwrap_or_else(|| {
                panic!("`{CLANG_VARIABLE}` не задан: спутник в `.bc` собрать нечем")
            });
        let source = dir.join(format!("{name}.support.c"));
        let raw = dir.join(format!("{name}.support.raw.bc"));
        std::fs::write(&source, text).unwrap();
        let made = Command::new(&clang)
            .args([
                "-std=c11",
                "-O2",
                "-fwrapv",
                "-ffp-contract=off",
                "-w",
                "-emit-llvm",
                "-c",
            ])
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg(&source)
            .arg("-o")
            .arg(&raw)
            .output()
            .unwrap();
        assert!(
            made.status.success(),
            "{name}: спутник не собрался в `.bc`:\n{}",
            String::from_utf8_lossy(&made.stderr)
        );
        plain_bitcode(&self.tools, dir, &format!("{name}.support"), &raw)
    }

    /// Он же отдельной единицей трансляции названного уровня.
    fn support_object(dir: &Path, name: &str, text: &str, level: &str) -> PathBuf {
        let source = dir.join(format!("{name}.support.c"));
        let object = dir.join(format!("{name}.support.o"));
        std::fs::write(&source, text).unwrap();
        let compiled = Command::new(env!("ADAMAS_CC"))
            .args(["-std=c11", level, "-fwrapv", "-ffp-contract=off", "-w"])
            .arg("-I")
            .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object)
            .output()
            .unwrap();
        assert!(
            compiled.status.success(),
            "{name}: спутник не собрался:\n{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        object
    }
}

/// Собранная нагрузка: двоичный файл, ответ, счётчики блоков.
///
/// Общая двум стендам, потому что второй столбец сверяет стороны **и ответом, и
/// счётчиком**, а счётчик читается из stderr одинаково у обоих.
pub(crate) struct Load {
    pub(crate) binary: PathBuf,
    pub(crate) answer: String,
    pub(crate) allocated: usize,
    pub(crate) live: usize,
}

impl Load {
    /// Прогон уже собранного двоичного файла.
    pub(crate) fn measured(name: &str, binary: PathBuf) -> Self {
        let (stdout, stderr) = ran(&binary);
        let (allocated, live) = blocks(&stderr);
        eprintln!("{name}: ответ {}, {}", stdout.trim_end(), stderr.trim_end());
        Self {
            binary,
            answer: stdout.trim_end_matches('\n').to_owned(),
            allocated,
            live,
        }
    }
}

/// Всё, что нужно LLVM-стороне: цепочка инструментов и рантайм битовым кодом.
///
/// Рантайм готовится однажды на прогон и **без host-атрибутов**: оставь их, и
/// инлайнер откажет всем вызовам рантайма разом, а число вышло бы про границу
/// единиц трансляции (измерено треком A′, `docs/phase7-plan.md`).
pub(crate) struct Backend {
    pub(crate) tools: Toolchain,
    runtime: PathBuf,
    stand: &'static str,
}

impl Backend {
    /// `None` — LLVM объявлен отсутствующим; иначе отсутствие роняет прогон.
    pub(crate) fn new(stand: &'static str) -> Option<Self> {
        let tools = llvm_tools()?;
        let runtime = runtime_bitcode(&tools, &scratch(stand));
        Some(Self {
            tools,
            runtime,
            stand,
        })
    }

    /// Сквозной конвейер: рантайм битовым кодом **до** `opt -O2`.
    ///
    /// Это и есть то, чем LLVM-сторона уравнена с `-flto` у C-стороны. Штатный
    /// [`Pipeline::optimised`] стадии не несёт, и с ним число мерило бы LTO.
    pub(crate) fn pipeline(&self) -> Pipeline {
        Pipeline::whole_program(&self.runtime)
    }

    /// Собирает и прогоняет нагрузку LLVM-путём.
    pub(crate) fn load(
        &self,
        name: &str,
        artefacts: &Artefacts,
        pipeline: &Pipeline,
        support: Support,
    ) -> Load {
        Load::measured(name, self.built(name, artefacts, pipeline, support))
    }
}

/// Переменная, включающая свидетелей второго столбца.
///
/// Врозь от самих строк, потому что стоят они дороже строк: каждый свидетель -
/// ещё одно отношение, померенное чередованием, то есть ещё семь блоков. Строка
/// таблицы обязана воспроизводиться одной командой; свидетель - той же командой
/// с переменной, и обе названы в README.
pub(crate) const WITNESS: &str = "ADAMAS_GAP_WITNESS";

/// Горячая функция готового бинаря, своя у каждого бэкенда.
///
/// У C-стороны `-flto` втягивает программу в `main`; у LLVM-стороны программа
/// целиком лежит в `adamas_entry`, а `main` приходит со спутником.
pub(crate) const HOT_C: &str = "main";
pub(crate) const HOT_LLVM: &str = "adamas_entry";

/// Две стороны нагрузки обязаны отвечать одно и выдавать столько же блоков.
///
/// Сверяется **и то и другое**: ответ ловит расхождение вычисления, счётчик -
/// расхождение владения. Строка, у которой бэкенды разошлись хоть в одном,
/// сравнивала бы две разные программы, и её отношение не значило бы ничего.
pub(crate) fn same_work(name: &str, c: &Load, llvm: &Load) {
    assert_eq!(
        llvm.answer, c.answer,
        "{name}: LLVM посчитал не то, что C-бэкенд"
    );
    assert_eq!(
        (llvm.allocated, llvm.live),
        (c.allocated, c.live),
        "{name}: у бэкендов разошлись счётчики блоков - сравнивались бы две \
         разные программы"
    );
}

/// Строка второго столбца: две стороны и их полы.
///
/// Четвёркой, а не четырьмя аргументами: полы отделять от своих сторон нельзя,
/// и перепутанная пара дала бы отношение, вычитающее чужой пол.
pub(crate) struct Column<'a> {
    pub(crate) llvm: &'a Load,
    pub(crate) llvm_floor: &'a Load,
    pub(crate) c: &'a Load,
    pub(crate) c_floor: &'a Load,
    /// Текст `.ll` LLVM-стороны: его читает свидетель схлопывания RC.
    pub(crate) ll: &'a str,
}

/// Отношение «LLVM против C»: обе стороны - двоичные файлы одного понижения.
///
/// Меньше единицы значит «LLVM-путь быстрее». Своё отношение, а не частное двух
/// отношений к соседу: то частное складывало бы два разных окна замера.
pub(crate) fn llvm_against_c(what: &str, column: &Column<'_>) -> Ratio {
    same_work(what, column.c, column.llvm);
    ratio(
        &format!("{what}: LLVM против C"),
        || drop(ran(&column.llvm.binary)),
        || drop(ran(&column.llvm_floor.binary)),
        || drop(ran(&column.c.binary)),
        || drop(ran(&column.c_floor.binary)),
    )
}

/// Свидетели строки второго столбца.
///
/// Два вопроса, и оба заданы числом, а не доводом.
///
/// **Сравниваются ли коды, а не строки сборки.** Фаза 6 намерила разрыв в 2.4
/// раза, из которого 99% оказались строкой сборки; здесь тот же риск в
/// квадрате, потому что цепочки двух бэкендов различаются по построению.
/// Свидетелей четыре: счёт вызовов в горячей функции обеих сторон, цена
/// отнятой стадии `llvm-link` у LLVM-стороны, цена отнятого `-flto` у
/// C-стороны и цена отдельной единицы трансляции у спутника.
///
/// **Отвечает ли строка на подсунутое замедление.** Замедление подсовывается
/// **одной** стороне - LLVM-пути, - потому что строка называет сравнение двух
/// бэкендов, а не программу. Замедлений два, слабое и сильное: `llc -O0` при
/// целом `opt` и снятый `opt` целиком. Второе заведено потому, что первое на
/// скалярных нагрузках **не отвечает**, и молчащий свидетель тут был бы хуже
/// отсутствующего.
///
/// Пересборка обеих сторон приходит **замыканиями**: у двух стендов программа
/// берётся по-разному (один читает корпусный файл, другой строит из скелета), а
/// сами свидетели одни и те же, и второй их копии быть не должно.
pub(crate) fn witnesses(
    what: &str,
    backend: &Backend,
    column: &Column<'_>,
    mut rebuilt: impl FnMut(&str, &Pipeline, Support) -> (Load, Load),
    mut apart: impl FnMut(&str) -> (Load, Load),
) {
    let (llvm, llvm_floor, c, c_floor) = (column.llvm, column.llvm_floor, column.c, column.c_floor);
    // Счёт вызовов - всегда: он стоит одного дизассемблирования и отвечает на
    // главный вопрос строки.
    hot_function(what, "LLVM", &backend.tools, &llvm.binary, HOT_LLVM);
    hot_function(what, "C", &backend.tools, &c.binary, HOT_C);
    pairs_after_inlining(what, backend, column.ll);

    if std::env::var_os(WITNESS).is_none() {
        eprintln!("свидетель/{what}: отношения не мерены ({WITNESS} не задана)");
        return;
    }
    let stem = sanitised(what);

    let mut variant = |name: &str, pipeline: &Pipeline, support: Support| {
        let (side, side_floor) = rebuilt(&format!("{stem}-{}", sanitised(name)), pipeline, support);
        same_work(what, c, &side);
        ratio(
            &format!("{what}: LLVM ({name}) против C"),
            || drop(ran(&side.binary)),
            || drop(ran(&side_floor.binary)),
            || drop(ran(&c.binary)),
            || drop(ran(&c_floor.binary)),
        );
    };

    // (1) Слабое замедление: `llc -O0` при целом `opt`.
    let blunt = Pipeline {
        stages: backend
            .pipeline()
            .stages
            .into_iter()
            .map(|stage| {
                if stage.tool == "llc" {
                    Stage::new(
                        "llc",
                        &["-O0", "-filetype=obj", "-relocation-model=pic"],
                        &stage.extension,
                    )
                } else {
                    stage
                }
            })
            .collect(),
    };
    variant("llc -O0", &blunt, Support::Bitcode);

    // (2) Сильное замедление: `opt` снят целиком, `llc -O2` на месте.
    let raw = Pipeline {
        stages: backend
            .pipeline()
            .stages
            .into_iter()
            .filter(|stage| stage.tool != "opt")
            .collect(),
    };
    variant("без opt", &raw, Support::Bitcode);

    // (3) Строка сборки, LLVM-сторона: ничего битовым кодом - ни рантайм, ни
    // спутник. Это состояние пути до трека A′.
    variant(
        "без llvm-link",
        &Pipeline::optimised(),
        Support::Object("-O2"),
    );

    // (4) Спутник отдельной единицей трансляции: граница, которой у C-стороны
    // нет вовсе - там печать и дроп лежат в одном файле с программой.
    variant("спутник врозь", &backend.pipeline(), Support::Object("-O2"));

    // (5) Строка сборки, C-сторона: та же программа без `-flto`.
    let (side, side_floor) = apart(&format!("{stem}-apart"));
    same_work(what, c, &side);
    ratio(
        &format!("{what}: LLVM против C без -flto"),
        || drop(ran(&llvm.binary)),
        || drop(ran(&llvm_floor.binary)),
        || drop(ran(&side.binary)),
        || drop(ran(&side_floor.binary)),
    );
}

/// Сколько пар `dup`/`drop` снимает собственный проход **после** инлайнинга.
///
/// Второй из двух механизмов, ради которых заводилась фаза («Зачем LLVM»,
/// пункт 2): в LLVM схлопывание идёт после того, как известно, что во что
/// въехало, а в C конвейер односторонний. Свидетель печатает отчёт прохода на
/// **этой** нагрузке, а не ссылается на замер трека C: пункт обещан нашим
/// программам, и проверять его надо на них.
///
/// Считается по тому же тексту, который видит конвейер трека C: `llvm-as`,
/// `opt -O2 -S`, проход. Пара, снятая здесь, есть выигрыш, недоступный
/// C-бэкенду; ноль здесь значит, что пункт 2 на этой нагрузке беспредметен.
fn pairs_after_inlining(what: &str, backend: &Backend, ll: &str) {
    let dir = scratch(backend.stand);
    let stem = format!("{}-collapse", sanitised(what));
    let source = dir.join(format!("{stem}.ll"));
    std::fs::write(&source, ll).unwrap();
    let inlining = Pipeline {
        stages: vec![
            Stage::new("llvm-as", &[], "bc"),
            Stage::new("opt", &["-O2", "-S"], "inlined.ll"),
        ],
    };
    let inlined = inlining
        .run(&backend.tools, &source, &stem)
        .unwrap_or_else(|error| panic!("{what}: инлайнинг для свидетеля пары отказал: {error}"));
    let text = std::fs::read_to_string(&inlined).unwrap();
    let (_, report) =
        adamas_codegen::collapse::collapse(&text, adamas_codegen::collapse::Between::Watched);
    eprintln!(
        "свидетель/{what}: схлопывание RC после инлайнинга - снято {} пар \
         (dup {}, drop {}, отказано {}, живых {})",
        report.cancelled, report.dups, report.drops, report.refused, report.live
    );
}

/// Что зовёт горячая функция одной стороны - строкой в лог.
pub(crate) fn hot_function(what: &str, side: &str, tools: &Toolchain, binary: &Path, symbol: &str) {
    let (instructions, calls) = inside(tools, binary, symbol);
    eprintln!(
        "свидетель/{what}: {side}, `{symbol}` - {instructions} инструкций, вызовы: {}",
        if calls.is_empty() {
            "ни одного".to_owned()
        } else {
            calls
                .iter()
                .map(|(name, count)| format!("{name} ×{count}"))
                .collect::<Vec<_>>()
                .join(", ")
        }
    );
}

/// Имя, годное файлу: русские слова и пробелы в именах артефактов не нужны.
pub(crate) fn sanitised(what: &str) -> String {
    what.chars()
        .map(|it| if it.is_ascii_alphanumeric() { it } else { '-' })
        .collect()
}

/// Что зовёт горячая функция готового бинаря: имена и число вызовов.
///
/// Свидетель того, что сравниваются **коды**, а не строки сборки. Вызов,
/// доживший до горячей функции, означает границу единиц трансляции: сторона, у
/// которой рантайм остался вызовом, платит за сборку, а не за бэкенд.
///
/// Считается **внутри названного символа**, а не по всему бинарю, и это не
/// придирка. По всему бинарю у C-стороны выходит двадцать два `adamas_drop`, у
/// LLVM-стороны два - и читается это как «C-стороне не досталось
/// инлайнинга», тогда как на деле двадцать из двадцати двух стоят в печати и
/// освобождении ответа, то есть вне витка. Счёт по бинарю - ровно тот
/// обманчивый свидетель, от которого предостерегает Фаза 6.
///
/// Горячая функция называется вызывающим, потому что зовётся она у двух
/// бэкендов по-разному: у C-стороны `-flto` втягивает программу в `main`, у
/// LLVM-стороны программа целиком лежит в `adamas_entry`, а `main` приходит со
/// спутником.
///
/// Отдаёт ещё и число инструкций символа: пустая горячая функция дала бы
/// «вызовов ноль» и выглядела бы победой.
pub(crate) fn inside(
    tools: &Toolchain,
    binary: &Path,
    symbol: &str,
) -> (usize, Vec<(String, usize)>) {
    let shown = Command::new(tools.tool("llvm-objdump"))
        .arg("-d")
        .arg(binary)
        .output()
        .unwrap();
    assert!(
        shown.status.success(),
        "`{}` не дизассемблировался",
        binary.display()
    );
    let text = String::from_utf8_lossy(&shown.stdout).into_owned();

    let head = format!("<{symbol}>:");
    let mut within = false;
    let mut instructions = 0_usize;
    let mut counted: std::collections::BTreeMap<String, usize> = std::collections::BTreeMap::new();
    for line in text.lines() {
        if line.ends_with(">:") {
            within = line.ends_with(&head);
            continue;
        }
        if !within || !line.contains('\t') {
            continue;
        }
        instructions += 1;
        if !line.contains("call") {
            continue;
        }
        // Имя цели стоит последним, в угловых скобках: `callq 0x1960 <adamas_drop>`.
        let Some(open) = line.rfind('<') else {
            continue;
        };
        let Some(close) = line.rfind('>') else {
            continue;
        };
        if close > open {
            *counted.entry(line[open + 1..close].to_owned()).or_default() += 1;
        }
    }
    assert!(
        instructions > 0,
        "символа `{symbol}` в `{}` нет вовсе: свидетель считал бы пустоту",
        binary.display()
    );
    (instructions, counted.into_iter().collect())
}

// --- сосед процессом -----------------------------------------------------

/// Переменная, которой стенд зовёт сам себя дочерним процессом.
///
/// Сосед мерится **тем же протоколом**, что и порождённый C: свежий процесс,
/// свежая куча, ответ на stdout. Иначе его цену задаёт не алгоритм, а то,
/// сколько успел выделить и освободить сам стенд — см. «Методика» в шапке
/// `native.rs`.
pub(crate) const NEIGHBOUR: &str = "ADAMAS_BENCH_NEIGHBOUR";

/// Прогон соседа отдельным процессом: ответ на stdout, свидетель на stderr.
pub(crate) fn ran_neighbour(request: &str) -> (String, String) {
    let executable = std::env::current_exe().expect("стенд знает путь к себе");
    let output = Command::new(executable)
        .env(NEIGHBOUR, request)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "прогон соседа оборвался: {}",
        output.status
    );
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

// --- оценка: пол выборки, а не её среднее --------------------------------

/// Наименьшее время из `runs` запусков.
///
/// Помеха может к времени процесса только **прибавить**: сосед по
/// гиперпотоку, прерывание, вытеснение. Поэтому наименьшее из повторов —
/// оценка того, чего программа стоит без помехи, а среднее — оценка того,
/// сколько помехи досталось окну замера. Измерено 2026-09-13 на `boxed/18`,
/// двенадцать блоков по сорок запусков: минимумы блоков легли в 19.94–20.23
/// (размах 0.29 мс), медианы — в 20.56–21.54 (0.98 мс), максимумы — в
/// 22.30–26.05 (3.75 мс). Хвост шире пола на порядок, и criterion по
/// умолчанию читает именно хвост.
pub(crate) fn least(runs: u64, mut run: impl FnMut()) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..runs {
        let start = Instant::now();
        run();
        best = best.min(start.elapsed());
    }
    best
}

/// Сколько запусков берётся под один пол, сколько бы ни просил criterion.
///
/// На разогреве criterion зовёт замер с одним-двумя повторами, а пол по
/// одному повтору — не пол. Число возвращается помноженным на `iters`, так
/// что планирование criterion остаётся верным: он делит обратно и получает
/// цену одного запуска.
pub(crate) const FLOOR_RUNS: u64 = 8;

/// Точка замера процесса: criterion получает пол, а не среднее.
pub(crate) fn by_floor(bencher: &mut criterion::Bencher<'_>, mut run: impl FnMut()) {
    bencher.iter_custom(|iters| {
        least(iters.max(FLOOR_RUNS), &mut run) * u32::try_from(iters).unwrap_or(u32::MAX)
    });
}

/// Идёт ли настоящий замер, а не проверка собираемости.
///
/// `cargo bench -- --test` в CI и `cargo test --all-targets` локально зовут
/// каждую точку по разу; долгий замер требует тихой машины, а ни разделяемый
/// раннер CI, ни машина под `cargo test` тихими не являются. В этом режиме
/// работа берётся минимальная, пороги не проверяются: проверяется, что код
/// проходит.
///
/// Правило — то же, каким его читает сам criterion: замер идёт, когда есть
/// `--bench` и нет `--test`. Под `cargo test` флага `--bench` не бывает.
pub(crate) fn measuring() -> bool {
    let mut bench = false;
    let mut test = false;
    for argument in std::env::args() {
        bench |= argument == "--bench";
        test |= argument == "--test";
    }
    bench && !test
}

/// Медиана выборки; портит порядок.
pub(crate) fn middle(sample: &mut [f64]) -> f64 {
    sample.sort_unstable_by(f64::total_cmp);
    sample[sample.len() / 2]
}

/// Размах выборки.
pub(crate) fn span(sample: &[f64]) -> f64 {
    let low = sample.iter().copied().fold(f64::MAX, f64::min);
    sample.iter().copied().fold(f64::MIN, f64::max) - low
}

// --- отношение двух сторон, померенное чередованием ----------------------

/// Блоков в замере отношения, пар в блоке и сколько блоков идёт в число.
///
/// Те же роли, что у `PAIRED_*` в `native.rs`, и та же причина: помеха
/// длится десятки секунд, поэтому две стороны нельзя мерить в разных окнах, а
/// блок, накрытый помехой целиком, отбрасывается по свидетелю пола.
const RATIO_BLOCKS: usize = 7;
const RATIO_QUIET: usize = 4;
const RATIO_PAIRS: u64 = 8;

/// Отношение двух сторон и то, из чего оно сложилось.
pub(crate) struct Ratio {
    /// Медиана отношения по тишайшим блокам.
    pub(crate) median: f64,
    /// Размах отношения между ними.
    pub(crate) spread: f64,
    /// Пол своей стороны, за вычетом своего пола запуска, мс.
    pub(crate) ours: f64,
    /// То же у соседа.
    pub(crate) theirs: f64,
}

/// Отношение «мы против соседа», померенное чередованием внутри одного окна.
///
/// Зачем не хватает точек criterion. Отношение берётся у двух точек, которые
/// в отчёте стоят на расстоянии десятков секунд, а окружение уводит их за это
/// время на единицы процентов — и не всегда вместе. Замер 2026-09-15 на
/// занятой машине дал по символьной строке одиннадцать прогонов в размахе
/// 0.75–1.57 при медиане около 0.90: отношение из отчёта там не читается
/// вовсе. Тот же довод, каким `native.rs` завёл свой парный замер, только там
/// он о разности, а здесь об отношении.
///
/// Что делает чередование. В блоке стороны идут подряд, оценка каждой — пол
/// блока (помеха прибавляет), пол запуска процесса вычитается **свой** у
/// каждой и меряется в том же блоке. Помеха, накрывшая блок, поднимает обе
/// стороны разом и из отношения уходит; блок, накрытый ею целиком, отсеивается
/// по полу нашей стороны — свидетелю, который о самом отношении ничего не
/// знает.
pub(crate) fn ratio(
    what: &str,
    mut ours: impl FnMut(),
    mut our_floor: impl FnMut(),
    mut theirs: impl FnMut(),
    mut their_floor: impl FnMut(),
) -> Ratio {
    let (blocks, pairs) = if measuring() {
        (RATIO_BLOCKS, RATIO_PAIRS)
    } else {
        (2, 2)
    };
    let milliseconds = |run: &mut dyn FnMut()| least(1, run).as_secs_f64() * 1e3;
    // Блок: пол каждой из четырёх точек, померенный чередованием.
    let mut measured: Vec<(f64, f64, f64)> = Vec::with_capacity(blocks);
    for block in 0..blocks {
        let (mut us, mut them) = (f64::MAX, f64::MAX);
        let (mut our_pit, mut their_pit) = (f64::MAX, f64::MAX);
        for _ in 0..pairs {
            us = us.min(milliseconds(&mut ours));
            them = them.min(milliseconds(&mut theirs));
            our_pit = our_pit.min(milliseconds(&mut our_floor));
            their_pit = their_pit.min(milliseconds(&mut their_floor));
        }
        let (us, them) = (us - our_pit, them - their_pit);
        if measuring() {
            eprintln!(
                "отношение/{what}: блок {block}: мы {us:.3} против соседа {them:.3} мс \
                 (полы {our_pit:.3} / {their_pit:.3}), отношение {:.4}",
                us / them
            );
        }
        measured.push((us, them, us / them));
    }

    // Тишайшие блоки вперёд, шумные — за черту. Свидетель тишины — пол нашей
    // стороны: он о самом отношении ничего не знает.
    measured.sort_unstable_by(|left, right| left.0.total_cmp(&right.0));
    let quiet = RATIO_QUIET.min(measured.len());
    let kept = &measured[..quiet];
    let mut ratios: Vec<f64> = kept.iter().map(|(_, _, ratio)| *ratio).collect();
    let median = middle(&mut ratios);
    let spread = span(&ratios);
    let ours = kept.iter().map(|(us, _, _)| *us).fold(f64::MAX, f64::min);
    let theirs = kept
        .iter()
        .map(|(_, them, _)| *them)
        .fold(f64::MAX, f64::min);
    // Вне замера отношение печатать нельзя, и дело не в тишине машины.
    // Наша сторона — двоичный файл, собранный строкой release всегда; сосед
    // перезапускает **этот** стенд, а под `cargo test` он собран отладочным
    // профилем (`target/debug`, против `target/release` под `cargo bench`).
    // Стороны оказываются из разных сборок, и отношение не просто неточно, а
    // перевёрнуто: колонное ядро даёт здесь 0.37 вместо 6.95. Строка итога в
    // том же формате, что у настоящего замера, — свидетель обманчивый, и
    // читателю лога `cargo test` отличить её нечем. Поэтому формат другой.
    if measuring() {
        eprintln!(
            "отношение/{what}: по {quiet} тишайшим блокам {median:.4} \
             (размах {spread:.4}), запас {:.1}x; пол наш {ours:.3} мс, соседа {theirs:.3}",
            median / spread
        );
    } else {
        eprintln!(
            "отношение/{what}: проверка собираемости, не замер - сосед собран \
             отладочным профилем, отношение недействительно"
        );
    }
    Ratio {
        median,
        spread,
        ours,
        theirs,
    }
}

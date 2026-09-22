//! Секция `[link]` манифеста: проект собирается и **запускается** с чужой
//! библиотекой (§5.3, §7.1).
//!
//! # Почему библиотека своя, а не системная
//!
//! Системная ничего бы не показала: стандартную библиотеку C подключают сами
//! обе стороны - `cc` без единого ключа, машина по [`C_LIBRARY`]. Секция
//! наблюдаема ровно там, где без неё **не работает**, и потому здесь строится
//! настоящая разделяемая библиотека в каталоге проекта: без `-L` её не найдёт
//! компоновщик, без `-l` не найдёт символ, без обоих не найдёт `dlopen`.
//!
//! Собирается она тем же `cc`, каким собран рантайм, и на диске лежит там же,
//! где лежала бы чужая: `vendor/lib/libadamasprobe.so`.
//!
//! # Что здесь проверяется
//!
//! Четыре вещи, и каждая - прогон, а не разбор манифеста.
//!
//! 1. `adamas run` собирает C-путём, линкуется и печатает ответ.
//! 2. `adamas run --backend llvm` делает то же: секция обязана доехать до
//!    линковки объектника `.ll` наравне с `cc`.
//! 3. `adamas eval` отвечает **то же самое**: машина ищет символ по тем же
//!    библиотекам, что и компоновщик.
//! 4. Тот же проект **без** секции не собирается и не считается. Без этой
//!    половины тест был бы зелен и при начисто проигнорированной секции: в
//!    системных каталогах `libadamasprobe.so` нет, но убедиться в этом можно
//!    только отказом.

#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Чужая библиотека: две функции, и ответ у них такой, какого не даст ошибка.
///
/// `adamas_probe_scale` умножает на семь и прибавляет три: перепутанный порядок
/// аргументов, потерянный вызов или подставленный ноль меняют **число**.
const PROBE: &str = "\
#include <stdint.h>

static uint64_t stashed = 0u;

uint64_t adamas_probe_scale(uint64_t value) {
    return value * 7u + 3u;
}

uint64_t adamas_probe_blend(uint64_t left, uint64_t right) {
    return left * 100u + right;
}

/* Пара, которой наблюдается **`void`-символ**. Иначе он не наблюдаем ничем:
 * значения у него нет по построению, и пропущенный вызов молчит. Измерено
 * мутантом: ветвь `(long) -> void`, не зовущая ничего, не роняла ни одного
 * свидетеля, пока этой пары не было. */
void adamas_probe_stash(uint64_t value) {
    stashed = value;
}

uint64_t adamas_probe_fetch(void) {
    return stashed;
}
";

/// Имя библиотеки в написании `-l`: файл её - `libadamasprobe.so`.
const LIBRARY: &str = "adamasprobe";

/// Каталог библиотеки внутри проекта - относительный, как его пишет манифест.
const VENDOR: &str = "vendor/lib";

/// Программа: четыре чужих вызова четырёх разных форм, ответ - их арифметика.
///
/// `scale 6` даёт 45; `stash 45` кладёт его на чужой стороне, `fetch` достаёт
/// обратно; `blend 45 2` даёт 4502. Пропущенный `stash` - единственный из
/// четырёх, чьё отсутствие не видно **в нём самом**: значения у `void`-символа
/// нет. Видно оно в `fetch`, и потому пара стоит здесь целиком.
const MAIN: &str = "\
data Unit where
  MkUnit : Unit

effect Foreign

@trusted
extern \"C\" fn adamas_probe_scale : UInt64 -> UInt64

@trusted
extern \"C\" fn adamas_probe_blend : UInt64 -> UInt64 -> UInt64

@trusted
extern \"C\" fn adamas_probe_stash : UInt64 -> Unit

@trusted
extern \"C\" fn adamas_probe_fetch : UInt64

body : (ω u : Unit) -> {Foreign} UInt64
body u =
  let scaled : UInt64 = adamas_probe_scale 6
  let kept : Unit = adamas_probe_stash scaled
  let back : UInt64 = adamas_probe_fetch
  adamas_probe_blend back 2

main : UInt64
main = handle @Foreign body with
  return v -> v
";

/// Ответ программы.
const ANSWER: &str = "4502";

/// Пустой каталог под один сценарий.
fn scratch(case: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("linking")
        .join(case);
    if dir.exists() {
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Кладёт файл, создавая каталоги по дороге.
fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

/// Компилятор C: тот же, которым собирает драйвер, если его назвали.
fn cc() -> Command {
    Command::new(
        std::env::var_os(adamas_codegen::native::CC_VARIABLE)
            .filter(|it| !it.is_empty())
            .unwrap_or_else(|| "cc".into()),
    )
}

/// Собирает чужую разделяемую библиотеку в каталоге проекта.
fn probe(dir: &Path) {
    let source = dir.join("probe.c");
    write(&source, PROBE);
    let object = dir.join(VENDOR).join(format!(
        "lib{LIBRARY}.{}",
        adamas_interp::foreign::SHARED_SUFFIX
    ));
    std::fs::create_dir_all(object.parent().unwrap()).unwrap();
    let built = cc()
        .args(["-std=c11", "-O1", "-Wall", "-fPIC", "-shared"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "чужая библиотека не собралась:\n{}",
        String::from_utf8_lossy(&built.stderr)
    );
    assert!(object.is_file(), "библиотеки нет: {}", object.display());
}

/// Проект с секцией `[link]` либо без неё.
fn project(dir: &Path, linked: bool) {
    let section = if linked {
        format!("\n[link]\nlibraries = [\"{LIBRARY}\"]\npaths = [\"{VENDOR}\"]\n")
    } else {
        String::new()
    };
    write(
        &dir.join("adamas.toml"),
        &format!("[package]\nname = \"app\"\n{section}"),
    );
    write(&dir.join("src/Main.adamas"), MAIN);
    probe(dir);
}

/// Запускает драйвер и отдаёт `(успех, stdout, stderr)`.
///
/// Текущим каталогом ставится сам проект: программа `zlib-stream` пишет файл
/// **относительным** именем, и без этого он ложился бы туда, откуда запущен
/// тест, - то есть в исходники крейта, и два тестовых бинаря дрались бы за
/// него.
fn adamas(dir: &Path, args: &[&str]) -> (bool, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_adamas"))
        .args(args)
        .arg(dir)
        .current_dir(dir)
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    assert!(!stderr.contains("panicked"), "драйвер упал: {stderr}");
    (output.status.success(), stdout, stderr)
}

/// Проект с `[link]` собирается, запускается и считается - тремя путями.
#[test]
fn a_project_links_against_a_foreign_library() {
    let dir = scratch("linked");
    project(&dir, true);

    let (ok, stdout, stderr) = adamas(&dir, &["run"]);
    assert!(ok, "C-путь не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == ANSWER),
        "C-путь посчитал не то:\n{stdout}"
    );

    let (ok, stdout, stderr) = adamas(&dir, &["run", "--backend", "llvm"]);
    assert!(ok, "путь LLVM не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == ANSWER),
        "путь LLVM посчитал не то:\n{stdout}"
    );

    let (ok, stdout, stderr) = adamas(&dir, &["eval"]);
    assert!(ok, "машина не посчитала:\n{stderr}\n{stdout}");
    assert_eq!(stdout, ANSWER, "машина посчитала не то");
}

/// Тот же проект без секции: ни сборки, ни ответа.
///
/// Вторая половина свидетеля выше. Без неё зелёный цвет означал бы только, что
/// `libadamasprobe.so` нашлась - а найтись она могла бы и сама.
#[test]
fn the_same_project_without_the_section_finds_nothing() {
    let dir = scratch("bare");
    project(&dir, false);

    let (ok, stdout, stderr) = adamas(&dir, &["build"]);
    assert!(!ok, "сборка без `[link]` обязана отказать:\n{stdout}");
    assert!(
        stderr.contains("adamas_probe_scale") || stderr.contains(LIBRARY),
        "отказ обязан назвать, чего не хватило:\n{stderr}"
    );

    let (ok, _, stderr) = adamas(&dir, &["eval"]);
    assert!(!ok, "машина без `[link]` обязана отказать");
    assert!(
        stderr.contains("adamas_probe_scale"),
        "отказ машины обязан назвать символ:\n{stderr}"
    );
}

// ---------------------------------------------------------------------------
// Поток gzip: `resource` над чужим объектом настоящей библиотеки (§3.3, §5.3).
// ---------------------------------------------------------------------------

/// Слои обёртки берутся из корпуса, а не пишутся здесь второй раз.
fn wrapper(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/golden/eval/Zlib")
        .join(format!("{name}.adamas"));
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("слой {}: {error}", path.display()))
}

/// Программа над `Zlib.Stream`: записать, прочитать, сверить, спросить
/// несуществующий файл.
///
/// Ответ - список из четырёх единиц, и каждая своя. `hello gzip` вместе с
/// завершающим нулём - одиннадцать байт; столько же обязано прочитаться
/// обратно, и первый из них обязан быть `h` (104). Четвёртая - `gzread` по
/// несуществующему файлу: `-1`.
///
/// Ответ **списком**, а не числом, и это не стиль: деструктор ресурса дробит
/// тело точкой приостановки, а функция с плоским ответом обрыв вернуть не
/// может (§4.11). Тем же отказом пришлось боксировать `Transferred` в самом
/// слое.
const STREAM: &str = "\
import Zlib.Raw (Unit, MkUnit, Foreign)
import Zlib.Stream (Transferred, Bytes, writeGz, readGz, absentFile)

data Bool where
  True : Bool
  False : Bool

data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data List (a : Type) where
  Nil : List a
  Cons : a -> List a -> List a

pick : Bool -> Nat -> Nat -> Nat
pick True yes no = yes
pick False yes no = no

one : Nat
one = Succ Zero

blank : UInt8
blank = 0

letter : UInt8
letter = 104

count : UInt64
count = 11

room : UInt64
room = 32

written : Int32
written = 11

path : Array 17 UInt8
path = \"zstream-probe.gz\"

absent : Array 18 UInt8
absent = \"zstream-absent.gz\"

writeMode : Array 3 UInt8
writeMode = \"wb\"

readMode : Array 3 UInt8
readMode = \"rb\"

payload : Array 11 UInt8
payload = \"hello gzip\"

matched : Transferred -> Int32 -> Nat
matched (Bytes seen) wanted = pick (eqInt32 seen wanted) one Zero

body : (ω u : Unit) -> {Foreign} List Nat
body u =
  let buffer : Array 32 UInt8 = arrayNew 32 blank
  let put : Transferred = writeGz path writeMode payload count
  let got : Transferred = readGz path readMode buffer room
  let first : UInt8 = arrayIndex buffer 0
  let gone : Transferred = readGz absent readMode buffer room
  Cons (matched put written)
    (Cons (matched got written)
      (Cons (pick (eqUInt8 first letter) one Zero)
        (Cons (matched gone absentFile) Nil)))

main : List Nat
main = handle @Foreign body with
  return v -> v
";

/// Ответ программы потока.
const STREAM_ANSWER: &str =
    "Cons (Succ Zero) (Cons (Succ Zero) (Cons (Succ Zero) (Cons (Succ Zero) Nil)))";

/// Файл, который программа кладёт на диск.
const ARTEFACT: &str = "zstream-probe.gz";

/// Проект над настоящей zlib: слои из корпуса плюс программа.
fn stream_project(dir: &Path) {
    write(
        &dir.join("adamas.toml"),
        "[package]\nname = \"zstream\"\n\n[link]\nlibraries = [\"z\"]\n",
    );
    write(&dir.join("src/Zlib/Raw.adamas"), &wrapper("Raw"));
    write(&dir.join("src/Zlib/Stream.adamas"), &wrapper("Stream"));
    write(&dir.join("src/Main.adamas"), STREAM);
}

/// Обёртка `resource` над `gzFile`: три вычислителя и файл на диске.
///
/// Живёт здесь, а не в корпусе, и причина одна: программа **пишет файл**.
/// Фикстуру `eval/` считают три вычислителя из трёх разных процессов, и два из
/// них идут параллельно в одном каталоге - имя файла у программы одно, и гонка
/// за ним была бы флаки-тестом. Здесь каталог свой на прогон.
#[test]
fn a_resource_over_a_gzip_stream_agrees_across_three_evaluators() {
    let dir = scratch("zstream");
    stream_project(&dir);

    let (ok, stdout, stderr) = adamas(&dir, &["eval"]);
    assert!(ok, "машина не посчитала:\n{stderr}\n{stdout}");
    assert_eq!(stdout, STREAM_ANSWER, "машина посчитала не то");
    assert!(
        dir.join(ARTEFACT).is_file(),
        "машина не оставила файла на диске: {}",
        dir.display()
    );

    // Файл снимается перед каждой сборкой: иначе следующий прогон читал бы
    // написанное предыдущим, и «записалось» было бы зелено при неработающей
    // записи.
    std::fs::remove_file(dir.join(ARTEFACT)).unwrap();
    let (ok, stdout, stderr) = adamas(&dir, &["run"]);
    assert!(ok, "C-путь не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == STREAM_ANSWER),
        "C-путь посчитал не то:\n{stdout}"
    );
    assert!(
        stderr.lines().any(|line| line.contains("живо 0")),
        "C-путь оставил блоки живыми:\n{stderr}"
    );

    std::fs::remove_file(dir.join(ARTEFACT)).unwrap();
    let (ok, stdout, stderr) = adamas(&dir, &["run", "--backend", "llvm"]);
    assert!(ok, "путь LLVM не собрался:\n{stderr}\n{stdout}");
    assert!(
        stdout.lines().any(|line| line == STREAM_ANSWER),
        "путь LLVM посчитал не то:\n{stdout}"
    );
    assert!(
        stderr.lines().any(|line| line.contains("живо 0")),
        "путь LLVM оставил блоки живыми:\n{stderr}"
    );
}

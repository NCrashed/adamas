//! Порождённый код в исполняемый файл: `cc`, рантайм, линковка (§7.1).
//!
//! Симметрия с [`crate::llvm`] прямая. Там «бэкенд» есть последовательность
//! процессов `llvm-as`/`opt`/`llc`; здесь - один процесс `cc`, и модуль нужен
//! по той же причине: кто-то обязан знать ключи, рантайм и порядок линковки, и
//! этот кто-то не драйвер. До волны 2 Фазы 9 знание жило в заготовке тестов
//! (`tests/harness/mod.rs`), то есть было недоступно `adamas build` вовсе.
//!
//! # Рантайм вшит, а не найден
//!
//! [`RUNTIME`] - таблица «имя файла - текст», собранная `build.rs` через
//! `include_str!`. Альтернатива - записать путь к `crates/adamas-runtime/c` и
//! читать его на прогоне - работает ровно до первого `cargo install`: путь
//! указывает в дерево исходников, а установленный бинарь живёт от него
//! отдельно. Цена вшивания названа: ~290 КБ в бинаре компилятора и
//! пересборка драйвера при правке рантайма.
//!
//! Раскладка на диске:
//!
//! ```text
//! <каталог сборки>/
//!   runtime/adamas.h, object.c, …    вшитый рантайм, выложенный как есть
//!   runtime/object.o, …              его объектники, общие на все сборки
//!   <имя>.c                          порождённый код
//!   <имя>                            что запускается
//! ```
//!
//! # Что здесь **не** сделано
//!
//! Режимов сборки §7.1 (debug/release/profile) нет: уровень один, `-O1`, тот
//! же, на котором корпус сверен с интерпретатором. Ключ, меняющий уровень, без
//! прогона на каждом уровне был бы обещанием без свидетеля.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Переменная окружения, называющая компилятор C.
pub const CC_VARIABLE: &str = "ADAMAS_CC";

/// Исходники рантайма: имя файла и его текст.
///
/// Первым идёт `adamas.h` - заголовок, который включает и порождённый код, и
/// каждая единица рантайма.
pub const RUNTIME: &[(&str, &str)] = include!(concat!(env!("OUT_DIR"), "/runtime.rs"));

/// Почему сборка не доехала.
#[derive(Debug, thiserror::Error)]
pub enum NativeError {
    /// Компилятора нет или он не запускается.
    #[error("компилятор C `{cc}` не запускается ({why}); другой задаёт `{CC_VARIABLE}`")]
    Missing {
        /// Что пробовали запустить.
        cc: String,
        /// Что сказала операционная система.
        why: String,
    },

    /// Компиляция или линковка отказала.
    #[error("{what}: компилятор C отказал\n{output}")]
    Failed {
        /// Что собиралось.
        what: String,
        /// Его вывод целиком.
        output: String,
    },

    /// Файл не записался или каталог не создался.
    #[error("не записать {path}: {why}")]
    Write {
        /// Какой путь.
        path: String,
        /// Что сказала операционная система.
        why: String,
    },
}

/// Компилятор C вместе с каталогом, в котором он работает.
#[derive(Clone, Debug)]
pub struct Native {
    cc: PathBuf,
    dir: PathBuf,
}

impl Native {
    /// Сборка в названном каталоге компилятором из окружения.
    ///
    /// Порядок поиска: `ADAMAS_CC` окружения, затем тот компилятор, которым
    /// собран сам рантайм (его записала `build.rs`). Второе существеннее
    /// первого в Nix-среде, где `cc` из `PATH` - не тот `cc`.
    #[must_use]
    pub fn new(dir: impl Into<PathBuf>) -> Self {
        let cc = std::env::var_os(CC_VARIABLE)
            .filter(|it| !it.is_empty())
            .map_or_else(|| PathBuf::from(env!("ADAMAS_CC")), PathBuf::from);
        Self {
            cc,
            dir: dir.into(),
        }
    }

    /// Она же названным компилятором.
    #[must_use]
    pub fn with(dir: impl Into<PathBuf>, cc: impl Into<PathBuf>) -> Self {
        Self {
            cc: cc.into(),
            dir: dir.into(),
        }
    }

    /// Каталог сборки.
    #[must_use]
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// Собирает порождённый C в исполняемый файл и отдаёт путь к нему.
    ///
    /// # Errors
    ///
    /// [`NativeError`] - каталог не создался, компилятора нет, сборка отказала.
    pub fn build(&self, name: &str, generated: &str) -> Result<PathBuf, NativeError> {
        let objects = self.runtime()?;
        let source = self.dir.join(format!("{name}.c"));
        write(&source, generated)?;
        let binary = self.dir.join(name);
        let mut command = self.cc();
        command
            .args(PROGRAM_FLAGS)
            .arg("-I")
            .arg(self.runtime_dir())
            .arg(&source)
            .args(&objects);
        self.linked_with(&mut command);
        command.arg("-o").arg(&binary);
        self.run(&mut command, name)?;
        Ok(binary)
    }

    /// Линкует готовый объектник (путь LLVM) со спутником на C и рантаймом.
    ///
    /// # Errors
    ///
    /// [`NativeError`] - те же три причины, что у [`Self::build`].
    pub fn link(&self, name: &str, object: &Path, support: &str) -> Result<PathBuf, NativeError> {
        let objects = self.runtime()?;
        let source = self.dir.join(format!("{name}.support.c"));
        let compiled = self.dir.join(format!("{name}.support.o"));
        write(&source, support)?;
        let mut command = self.cc();
        command
            .args(PROGRAM_FLAGS)
            .arg("-c")
            .arg("-I")
            .arg(self.runtime_dir())
            .arg(&source)
            .arg("-o")
            .arg(&compiled);
        self.run(&mut command, &format!("спутник {name}"))?;

        let binary = self.dir.join(name);
        let mut command = self.cc();
        command.arg(object).arg(&compiled).args(&objects);
        self.linked_with(&mut command);
        command.arg("-o").arg(&binary);
        self.run(&mut command, name)?;
        Ok(binary)
    }

    /// Дописывает то, что подключается всегда: вторую половину стандартной
    /// библиотеки C.
    fn linked_with(&self, command: &mut Command) {
        command.arg(C_MATH);
    }

    /// Каталог, в который выкладывается рантайм.
    fn runtime_dir(&self) -> PathBuf {
        self.dir.join("runtime")
    }

    /// Выкладывает вшитый рантайм на диск и собирает его объектники.
    ///
    /// Пересборка - по содержимому: текст пишется только когда он разошёлся с
    /// лежащим, а `.o` собирается только когда его нет или он старше своего
    /// `.c`. Иначе каждая сборка проекта заново компилировала бы восемь единиц
    /// рантайма, и `adamas build` был бы медленнее не по своей вине.
    fn runtime(&self) -> Result<Vec<PathBuf>, NativeError> {
        let dir = self.runtime_dir();
        let mut objects = Vec::new();
        for (name, text) in RUNTIME {
            let path = dir.join(name);
            if std::fs::read_to_string(&path).ok().as_deref() != Some(*text) {
                write(&path, text)?;
            }
            if Path::new(name).extension().is_none_or(|it| it != "c") {
                continue;
            }
            let object = dir.join(format!("{name}.o"));
            if !fresh(&object, &path) {
                let mut command = self.cc();
                command
                    .args(RUNTIME_FLAGS)
                    .arg("-c")
                    .arg("-I")
                    .arg(&dir)
                    .arg(&path)
                    .arg("-o")
                    .arg(&object);
                self.run(&mut command, &format!("рантайм {name}"))?;
            }
            objects.push(object);
        }
        Ok(objects)
    }

    /// Заготовка вызова компилятора.
    fn cc(&self) -> Command {
        Command::new(&self.cc)
    }

    /// Запускает вызов и переводит отказ в [`NativeError`].
    fn run(&self, command: &mut Command, what: &str) -> Result<(), NativeError> {
        let done = command.output().map_err(|why| NativeError::Missing {
            cc: self.cc.display().to_string(),
            why: why.to_string(),
        })?;
        if done.status.success() {
            return Ok(());
        }
        Err(NativeError::Failed {
            what: what.to_owned(),
            output: format!(
                "{}{}",
                String::from_utf8_lossy(&done.stdout),
                String::from_utf8_lossy(&done.stderr)
            ),
        })
    }
}

/// Ключи сборки порождённого кода.
///
/// Те же, на которых корпус сверен с интерпретатором (`tests/agreement.rs`):
/// `-ffp-contract=off` требует §4.3, и требует не зря - умолчание clang'а
/// контрактит `a * b + c` внутри выражения. `-Wno-unused` - потому что
/// порождённый код связывает поля, которых тело не смотрит.
///
/// `-fno-builtin` - про **корректность**, а не про скорость (§5.3). Чужой вызов
/// с константным аргументом `gcc` сворачивает сам, уже на `-O0`, и считает
/// иначе, чем библиотека: `cbrt(27.0)` даёт у него `3.0`
/// (`4008000000000000`), а glibc - `3.0000000000000004` (`4008000000000001`).
/// LLVM на том же месте не сворачивает ничего, и машина отвечает как glibc, -
/// то есть свёрнутый вызов разводит два понижения молча.
///
/// **Сегодняшний вклад этого ключа измерен, и он ноль.** Свёртку отменяет
/// раньше другое - `emit_c::prototypes` объявляет чужой символ **своим** именем
/// с ассемблерной меткой, а узнавание у `gcc` идёт по написанному имени. Ключ
/// остаётся по двум причинам: он переживёт смену схемы именования, и он
/// симметричен `nobuiltin`, который `.ll` печатает у объявления и без которого
/// `opt -O2` сворачивает `pow` и `labs` в константы. Оба довода и оба замера -
/// `tests/folding.rs`.
///
/// Ключ **глобальный**, а не точечный `-fno-builtin-<имя>` на каждый чужой
/// символ, и выбор измерен. Цена глобального оценивалась как «компилятор
/// перестанет знать про `memcpy`» - не подтвердилось: единственный горячий
/// образец в порождённой единице трансляции, восьмибайтовый `memcpy` битового
/// каста (`flat.c`, `adamas_bits_Float64`), компилируется с ключом и без него в
/// те же две инструкции. Всё прочее, чего ключ касается в этой единице, -
/// `printf`, `snprintf`, `strtod` печати. А у точечного варианта есть цена,
/// которой у глобального нет: список имён можно забыть пополнить, и свёртка
/// вернётся молча.
const PROGRAM_FLAGS: [&str; 5] = [
    "-std=c11",
    "-O1",
    "-ffp-contract=off",
    "-Wno-unused",
    "-fno-builtin",
];

/// Ключи сборки рантайма: он свой C, и предупреждения в нём - находки.
///
/// `-fno-builtin` сюда **не** идёт: чужих вызовов в рантайме нет ни одного, а
/// свёртка своего кода - обычная оптимизация, ради которой рантайм и собирается
/// отдельно.
const RUNTIME_FLAGS: [&str; 2] = ["-std=c11", "-O1"];

/// Стандартная библиотека C, которую `cc` **не** подключает сам.
///
/// У glibc она разложена по двум файлам, и за `libm.so.6` компоновщик требует
/// ключ. Для языка это одна библиотека (та же, которую ищет машина -
/// `adamas_interp::foreign::C_LIBRARY`), и требовать её в манифесте значило бы
/// заставить автора знать, в каком из двух файлов у его libc лежит `cbrt`.
const C_MATH: &str = "-lm";

/// Не старше ли `object`, чем `source`.
fn fresh(object: &Path, source: &Path) -> bool {
    let at = |path: &Path| std::fs::metadata(path).and_then(|it| it.modified()).ok();
    match (at(object), at(source)) {
        (Some(object), Some(source)) => object >= source,
        _ => false,
    }
}

/// Кладёт файл, создавая каталоги по дороге.
fn write(path: &Path, text: &str) -> Result<(), NativeError> {
    let failed = |why: std::io::Error| NativeError::Write {
        path: path.display().to_string(),
        why: why.to_string(),
    };
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).map_err(failed)?;
    }
    std::fs::write(path, text).map_err(failed)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Список приходит от рантайма, а не написан здесь: заголовок плюс восемь
    /// единиц трансляции. Разъедься он - линковка дала бы «undefined
    /// reference», и виноватым выглядел бы порождённый код.
    #[test]
    fn the_runtime_travels_with_the_compiler() {
        let names: Vec<&str> = RUNTIME.iter().map(|(name, _)| *name).collect();
        assert_eq!(names.first(), Some(&"adamas.h"), "{names:?}");
        assert!(names.contains(&"object.c"), "{names:?}");
        assert_eq!(
            names.len(),
            env!("ADAMAS_RUNTIME_UNITS").split(',').count() + 1,
            "{names:?}"
        );
        for (name, text) in RUNTIME {
            assert!(!text.is_empty(), "{name} вшит пустым");
        }
    }
}

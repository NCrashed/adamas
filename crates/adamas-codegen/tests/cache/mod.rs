//! Заготовка, общая процессам прогона.
//!
//! Прогон идёт `cargo nextest`, и каждый тест - свой процесс. Объектники
//! рантайма и уклады, которые прежде собирались однажды на процесс-бинарь
//! (`OnceLock`), собирались теперь в каждом тесте и в одно и то же место: читатель
//! видел недописанный `.o` («file format not recognized»), исполнитель - бинарь
//! в записи («Text file busy»). Заготовка собирается в черновик своего процесса
//! и встаёт на место переименованием каталога: оно атомарно, и каталог под
//! готовым именем всегда целый. Проигравший гонку выбрасывает свой черновик и
//! берёт готовое.

#![allow(
    dead_code,
    reason = "модуль общий нескольким тестовым крейтам, и каждый берёт свою часть"
)]

use std::hash::{Hash as _, Hasher as _};
use std::path::{Path, PathBuf};

/// Каталог `root/name`, собранный `build` однажды на все процессы.
///
/// `name` обязан меняться вместе с тем, из чего заготовка собрана, - см.
/// [`stamp`]: иначе правка рантайма подхватила бы прежние объектники.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn staged(root: &Path, name: &str, build: impl FnOnce(&Path)) -> PathBuf {
    let ready = root.join(name);
    if ready.is_dir() {
        return ready;
    }
    let draft = root.join(format!("{name}.{}.draft", std::process::id()));
    let _ = std::fs::remove_dir_all(&draft);
    std::fs::create_dir_all(&draft).unwrap();
    build(&draft);
    // Занято - значит, другой процесс успел первым, и его каталог целый.
    if std::fs::rename(&draft, &ready).is_err() {
        let _ = std::fs::remove_dir_all(&draft);
    }
    ready
}

/// Отпечаток файлов и ключей: имя заготовки, меняющееся вместе с ними.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn stamp(files: &[PathBuf], keys: &[&str]) -> String {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for file in files {
        file.hash(&mut hasher);
        std::fs::read(file).unwrap().hash(&mut hasher);
    }
    keys.hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

/// Исходники рантайма и его заголовки - то, из чего собран всякий объектник.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn runtime_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = [
        env!("ADAMAS_RUNTIME_SOURCES"),
        env!("ADAMAS_RUNTIME_INCLUDE"),
    ]
    .iter()
    .flat_map(|dir| std::fs::read_dir(dir).unwrap())
    .map(|entry| entry.unwrap().path())
    .filter(|path| path.is_file())
    .collect();
    files.sort();
    files
}

/// Каталог `root/<pid>` - свой у процесса - без каталогов умерших процессов.
///
/// Для свидетелей, у которых тестов единицы: заготовку они собирают каждый
/// себе, и гонок нет вовсе. Каталог умершего процесса удаляется здесь же, иначе
/// они копились бы от прогона к прогону.
#[allow(
    clippy::unwrap_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
pub(crate) fn private(root: &Path) -> PathBuf {
    if let Ok(entries) = std::fs::read_dir(root) {
        for entry in entries.flatten() {
            let name = entry.file_name();
            let Some(pid) = name.to_str().and_then(|it| it.parse::<u32>().ok()) else {
                continue;
            };
            if !Path::new("/proc").join(pid.to_string()).exists() {
                let _ = std::fs::remove_dir_all(entry.path());
            }
        }
    }
    let dir = root.join(std::process::id().to_string());
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

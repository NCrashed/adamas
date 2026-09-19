//! Достача зависимости: зеркало репозитория и чекаут коммита.
//!
//! # Через `git`, а не через библиотеку
//!
//! Зовётся системный `git`. Альтернатива - `libgit2` через `git2`, - стоила бы
//! сборки C-библиотеки в каждом окружении и всё равно не покрыла бы
//! `credential.helper`, `insteadOf` и прочую конфигурацию, ради которой люди
//! настраивают git один раз на машину. Цена выбора названа: `git` обязан быть
//! в `PATH`, и это же записано в `flake.nix`.
//!
//! # Раскладка
//!
//! ```text
//! <проект>/.adamas/
//!   git/<слаг>/            зеркало (`git clone --mirror`), общее на URL
//!   checkout/<префикс>/<коммит>/   рабочее дерево, одно на коммит
//! ```
//!
//! Кеш **внутри проекта**, а не в общем домашнем каталоге. Цена: два проекта с
//! одной зависимостью клонируют её дважды. Что покупается: сборка не зависит от
//! состояния чужого каталога, а прогон тестов - от предыдущего прогона.
//!
//! # Когда сеть не трогается вовсе
//!
//! Если коммит известен заранее (из `rev` манифеста или из `adamas.lock`) и
//! его чекаут уже лежит - не вызывается даже `git`. Если чекаута нет, но
//! коммит есть в зеркале - `git` зовётся, наружу он не ходит. За источником
//! идут ровно в двух случаях: зеркала нет, или коммит неизвестен (тег).

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::error::PkgError;
use crate::manifest::{Dependency, Requirement};

/// Каталог кеша внутри проекта.
pub const STORE: &str = ".adamas";

/// Достанутая зависимость.
#[derive(Clone, Debug)]
pub struct Fetched {
    /// Полный хеш коммита, который лежит в чекауте.
    pub rev: String,
    /// Корень чекаута.
    pub dir: PathBuf,
    /// Ходили ли к источнику - клонировали зеркало или обновляли его.
    pub refreshed: bool,
}

/// Кеш проекта: зеркала и чекауты.
#[derive(Clone, Debug)]
pub struct Store {
    root: PathBuf,
}

impl Store {
    /// Кеш внутри каталога проекта.
    #[must_use]
    pub fn new(project: &Path) -> Self {
        Self {
            root: project.join(STORE),
        }
    }

    /// Зеркало репозитория.
    #[must_use]
    pub fn mirror_dir(&self, git: &str) -> PathBuf {
        self.root.join("git").join(slug(git))
    }

    /// Чекаут коммита.
    #[must_use]
    pub fn checkout_dir(&self, prefix: &str, rev: &str) -> PathBuf {
        self.root.join("checkout").join(prefix).join(rev)
    }

    /// Кладёт зависимость на диск и отдаёт коммит, на котором она стоит.
    ///
    /// `pinned` - коммит из `adamas.lock`, если он там был. Манифест с `rev`
    /// точнее замка и перекрывает его: в замке живёт разрешение **тега**, а
    /// написанный коммит разрешения не требует.
    ///
    /// # Errors
    ///
    /// `git` не запустился, репозиторий недостижим, тега или коммита в нём нет,
    /// каталог не создаётся.
    pub fn provide(
        &self,
        dependency: &Dependency,
        pinned: Option<&str>,
    ) -> Result<Fetched, PkgError> {
        let pin = match &dependency.want {
            Requirement::Rev(rev) => Some(rev.clone()),
            Requirement::Tag(_) => pinned.map(str::to_owned),
        };

        // Коммит известен полным хешем и уже лежит: ни зеркала, ни `git`.
        // Сокращение берётся только на полном хеше - иначе ключ каталога не
        // совпал бы с тем, под которым чекаут был записан.
        if let Some(rev) = pin.as_deref().filter(|it| full_hash(it)) {
            let dir = self.checkout_dir(&dependency.prefix, rev);
            if dir.is_dir() {
                return Ok(Fetched {
                    rev: rev.to_owned(),
                    dir,
                    refreshed: false,
                });
            }
        }

        let mirror = self.mirror_dir(&dependency.git);
        let mut refreshed = false;
        if mirror.join("HEAD").is_file() {
            // Тег разрешается заново при каждой сборке без замка - в этом и
            // состоит разница между «с lockfile» и «без».
            let known = pin.as_deref().is_some_and(|rev| has_commit(&mirror, rev));
            if !known {
                run(
                    &["fetch", "--prune", "--force", "origin", "+refs/*:refs/*"],
                    Some(&mirror),
                )?;
                refreshed = true;
            }
        } else {
            create(&mirror)?;
            run(
                &[
                    "clone",
                    "--mirror",
                    "--quiet",
                    &dependency.git,
                    &mirror.display().to_string(),
                ],
                None,
            )?;
            refreshed = true;
        }

        let asked = pin.map_or_else(
            || dependency.want.refspec(),
            |rev| format!("{rev}^{{commit}}"),
        );
        let rev = run(
            &["rev-parse", "--verify", "--end-of-options", &asked],
            Some(&mirror),
        )
        .map_err(|error| match error {
            PkgError::Git { command, message } => PkgError::Git {
                command,
                message: format!(
                    "{message}\n  в репозитории {}: не найден {asked}",
                    dependency.git
                ),
            },
            other => other,
        })?;
        let rev = rev.trim().to_owned();

        let dir = self.checkout_dir(&dependency.prefix, &rev);
        if !dir.is_dir() {
            self.extract(&mirror, &rev, &dir)?;
        }
        Ok(Fetched {
            rev,
            dir,
            refreshed,
        })
    }

    /// Разворачивает коммит в отдельный каталог.
    ///
    /// Собирается рядом и переименовывается: прерванная достача не оставляет
    /// полчекаута, который следующий прогон принял бы за готовый.
    fn extract(&self, mirror: &Path, rev: &str, dir: &Path) -> Result<(), PkgError> {
        let parent = dir.parent().unwrap_or(&self.root);
        create(parent)?;
        let staging = parent.join(format!(".{rev}.{}", std::process::id()));
        if staging.exists() {
            remove(&staging)?;
        }
        run(
            &[
                "clone",
                "--quiet",
                "--no-checkout",
                &mirror.display().to_string(),
                &staging.display().to_string(),
            ],
            None,
        )?;
        run(&["checkout", "--quiet", "--detach", rev], Some(&staging))?;
        if std::fs::rename(&staging, dir).is_err() && !dir.is_dir() {
            return Err(PkgError::Write {
                path: dir.to_path_buf(),
                source: std::io::Error::other("чекаут не переименовался"),
            });
        }
        if staging.exists() {
            remove(&staging)?;
        }
        Ok(())
    }
}

/// Есть ли коммит в зеркале. Ответ - да или нет, отказа тут быть не может:
/// отсутствие коммита и есть ответ.
fn has_commit(mirror: &Path, rev: &str) -> bool {
    run(
        &["cat-file", "-e", &format!("{rev}^{{commit}}")],
        Some(mirror),
    )
    .is_ok()
}

/// Запускает `git` и отдаёт `stdout`.
///
/// `GIT_TERMINAL_PROMPT=0`: репозиторий, требующий пароля, обязан отказать, а
/// не повесить сборку на невидимом приглашении.
fn run(args: &[&str], cwd: Option<&Path>) -> Result<String, PkgError> {
    let mut command = Command::new("git");
    command.env("GIT_TERMINAL_PROMPT", "0");
    if let Some(cwd) = cwd {
        command.arg("-C").arg(cwd);
    }
    command.args(args);
    let written = args.join(" ");
    let output = command.output().map_err(|source| PkgError::Git {
        command: written.clone(),
        message: format!("не запустился: {source}"),
    })?;
    if !output.status.success() {
        return Err(PkgError::Git {
            command: written,
            message: format!(
                "{}\n{}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn create(dir: &Path) -> Result<(), PkgError> {
    std::fs::create_dir_all(dir).map_err(|source| PkgError::Write {
        path: dir.to_path_buf(),
        source,
    })
}

fn remove(dir: &Path) -> Result<(), PkgError> {
    std::fs::remove_dir_all(dir).map_err(|source| PkgError::Write {
        path: dir.to_path_buf(),
        source,
    })
}

/// Полный хеш коммита - сорок шестнадцатеричных цифр.
fn full_hash(text: &str) -> bool {
    text.len() == 40 && text.bytes().all(|it| it.is_ascii_hexdigit())
}

/// Имя каталога зеркала: читаемый хвост URL плюс хеш всего URL.
///
/// Хвост - чтобы в `.adamas/git/` можно было смотреть глазами; хеш - чтобы два
/// разных URL с одинаковым хвостом не делили зеркало.
fn slug(git: &str) -> String {
    let tail: String = git
        .rsplit(['/', '\\'])
        .find(|it| !it.is_empty())
        .unwrap_or("repo")
        .chars()
        .map(|it| {
            if it.is_ascii_alphanumeric() || it == '-' || it == '_' || it == '.' {
                it
            } else {
                '-'
            }
        })
        .take(32)
        .collect();
    format!("{tail}-{:016x}", fnv1a(git))
}

/// FNV-1a, 64 бита. Хеш здесь различает имена каталогов, а не защищает от
/// подбора, поэтому криптографического не нужно - и криптографической
/// зависимости тоже.
fn fnv1a(text: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_slug_is_readable_and_unique() {
        let left = slug("https://example.invalid/a/std.git");
        let right = slug("https://example.invalid/b/std.git");
        assert!(left.starts_with("std.git-"), "{left}");
        assert!(right.starts_with("std.git-"), "{right}");
        assert_ne!(left, right, "разные URL обязаны дать разные зеркала");
    }

    #[test]
    fn a_slug_has_no_separators() {
        let written = slug("file:///tmp/../etc/passwd");
        assert!(!written.contains('/'), "{written}");
        assert!(!written.contains(std::path::MAIN_SEPARATOR), "{written}");
    }

    #[test]
    fn a_full_hash_is_forty_hex_digits() {
        assert!(full_hash(&"a".repeat(40)));
        assert!(!full_hash(&"a".repeat(39)));
        assert!(!full_hash(&"z".repeat(40)));
    }
}

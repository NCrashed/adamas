//! Манифест проекта: `adamas.toml`.
//!
//! # Почему TOML
//!
//! §7.1 называет инструмент cargo-inspired, §7.3 - зависимость git URL плюс
//! коммит или тег; форму файла не задаёт ни один раздел, и выбор здесь.
//! Рассмотрено четыре:
//!
//! - **TOML.** Знаком всякому, кто открывал `Cargo.toml`; комментарии есть;
//!   разборщик с позициями ошибок готов. Цена измерена: `toml` с
//!   `default-features = false, features = ["parse"]` даёт **+5 крейтов**
//!   (44 → 49 в графе обычных зависимостей рабочего пространства) - `toml`,
//!   `toml_parser`, `toml_datetime`, `serde_spanned`, `winnow`, - без `serde`
//!   и без единого proc-macro. Полный `toml` стоил бы **+9**.
//! - **Свой строчный формат.** Ноль зависимостей, но второй диалект
//!   конфигурации в проекте и свои позиции ошибок руками.
//! - **JSON.** `serde_json` в дереве нет, комментариев нет, а манифест люди
//!   читают глазами.
//! - **Сам Adamas.** Красиво для языка с зависимыми типами и невозможно по
//!   порядку: чтобы разобрать манифест, нужен компилятор, а чтобы собрать
//!   компилируемое - манифест. Круг.
//!
//! Взят TOML: пять крейтов за знакомый формат с готовой диагностикой.
//!
//! # Что в нём написано
//!
//! ```toml
//! [package]
//! name = "example"
//! root = "src"    # каталог модулей, по умолчанию `src`
//! entry = "Main"  # модуль-вход, по умолчанию `Main`
//! test = "Test"   # модуль с тестами, по умолчанию `Test`
//!
//! [dependencies]
//! Std = { git = "https://example.invalid/std.git", tag = "v0.1.0" }
//! Data = { git = "https://example.invalid/data.git", rev = "0123abc…" }
//!
//! [link]
//! libraries = ["curl"]   # -lcurl, он же libcurl.so у `dlopen`
//! paths = ["vendor/lib"] # -Lvendor/lib, относительно каталога манифеста
//! ```
//!
//! **Ключ в `[dependencies]` - это префикс путей модулей, а не имя пакета.**
//! `Std.Prelude` может прийти только из пакета, записанного под `Std`, и
//! больше ниоткуда. Это и есть «явные зависимости» §7.3 на уровне файла:
//! глядя в манифест, видно, какой репозиторий отвечает за какое имя, без
//! поиска по диску. Цена выбора названа: два пакета не могут делить префикс,
//! и переименование префикса переписывает `import`'ы.
//!
//! # Почему `[link]` - отдельная секция
//!
//! Зависимость-**пакет** и зависимость-**библиотека** разные по всем трём
//! своим полям, и §7.3 говорит только про первую. Пакет приносит **модули**: у
//! него есть префикс путей, git URL и коммит, и достаёт его `adamas-pkg`.
//! Библиотека приносит **символы**: префикса у неё нет - `extern "C"` называет
//! символ, а не модуль (§5.3); доставать её нечем - она либо стоит в системе,
//! либо её кладёт чужая система сборки; а «версия» у неё soname, а не тег.
//! Записанные одной таблицей, они заставили бы половину полей каждой стороны
//! быть бессмысленными, и `Std = { git = … }` рядом с `curl = { }` читалось бы
//! как одно и то же.
//!
//! Написание взято у компоновщика (`-l`, `-L`), и взято **ради машины**:
//! `-lname` компоновщик разрешает в файл `libname.so`, и он же открывается
//! `dlopen`'ом. То есть `adamas build` и `adamas eval` требуют от системы
//! одного и того же файла, а не двух разных написаний одного.

use std::path::{Path, PathBuf};

use toml::de::{DeTable, DeValue};

use crate::error::PkgError;

/// Имя файла манифеста.
pub const MANIFEST: &str = "adamas.toml";

/// Чего манифест хочет от репозитория (§7.3: «git URL + commit/tag»).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Requirement {
    /// Точный коммит. Неподвижен по построению, и lockfile к нему ничего не
    /// добавляет, кроме кеша.
    Rev(String),
    /// Тег. В git тег **подвижен** - его можно переставить на другой коммит, -
    /// и именно поэтому §7.1 требует lockfile.
    Tag(String),
}

impl Requirement {
    /// Ссылка в написании `git rev-parse`.
    #[must_use]
    pub fn refspec(&self) -> String {
        match self {
            Self::Rev(rev) => format!("{rev}^{{commit}}"),
            Self::Tag(tag) => format!("refs/tags/{tag}^{{commit}}"),
        }
    }
}

/// Одна зависимость.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dependency {
    /// Префикс путей модулей, которые обслуживает этот пакет.
    pub prefix: String,
    /// git URL - любой, какой понимает `git clone`, включая `file://`.
    pub git: String,
    /// Коммит или тег.
    pub want: Requirement,
}

/// Секция `[link]`: с чем связывать программу сверх рантайма (§5.3, §7.1).
///
/// Довод в пользу отдельной секции - в шапке модуля.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Link {
    /// Библиотеки в написании `-l`: без `lib` и без расширения.
    pub libraries: Vec<String>,
    /// Каталоги поиска - абсолютные, уже склеенные с каталогом манифеста.
    pub paths: Vec<PathBuf>,
}

/// Разобранный `adamas.toml`.
#[derive(Clone, Debug)]
pub struct Manifest {
    /// Каталог, в котором лежал манифест.
    pub dir: PathBuf,
    /// Имя пакета. Ни на что не влияет, кроме сообщений: реестра нет (§7.3).
    pub name: String,
    /// Корень поиска модулей - абсолютный, уже склеенный с [`Self::dir`].
    pub root: PathBuf,
    /// Путь модуля-входа: `Main` - это `<root>/Main.adamas`.
    pub entry: String,
    /// Путь модуля с тестами: `Test` - это `<root>/Test.adamas`.
    ///
    /// Отдельный модуль, а не тесты во входном: программа и её тесты - две
    /// разные программы, и у второй свой вход. Иначе тестовое определение
    /// уезжало бы в собранный бинарь.
    pub test: String,
    /// Зависимости в порядке написания.
    pub dependencies: Vec<Dependency>,
    /// С чем линковать: секция `[link]` (§5.3).
    pub link: Link,
}

impl Manifest {
    /// Читает `<dir>/adamas.toml`.
    ///
    /// # Errors
    ///
    /// Манифеста нет, он не читается, не разбирается или собран не так.
    pub fn open(dir: &Path) -> Result<Self, PkgError> {
        let path = dir.join(MANIFEST);
        if !path.is_file() {
            return Err(PkgError::NoManifest(path));
        }
        let text = std::fs::read_to_string(&path).map_err(|source| PkgError::Read {
            path: path.clone(),
            source,
        })?;
        Self::parse(dir, &path, &text)
    }

    /// Разбирает текст манифеста. `path` идёт только в сообщения.
    ///
    /// # Errors
    ///
    /// TOML не разобрался или поля собраны не так.
    pub fn parse(dir: &Path, path: &Path, text: &str) -> Result<Self, PkgError> {
        let document = DeTable::parse(text).map_err(|error| PkgError::Syntax {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        let document = document.get_ref();
        let package = document
            .get("package")
            .map(toml::Spanned::get_ref)
            .ok_or_else(|| PkgError::shape(path, "нет таблицы `[package]`"))?
            .as_table()
            .ok_or_else(|| PkgError::shape(path, "`package` - не таблица"))?;

        let name = string(path, package, "package", "name")?
            .ok_or_else(|| PkgError::shape(path, "в `[package]` нет `name`"))?;
        // Имя стало **именем файла**: `adamas build` кладёт под ним артефакт.
        // Слеш и `..` в нём поэтому отсекаются здесь же, где и в путях модулей.
        file_name(path, "package.name", &name)?;
        let root = string(path, package, "package", "root")?.unwrap_or_else(|| "src".to_owned());
        let entry = string(path, package, "package", "entry")?.unwrap_or_else(|| "Main".to_owned());
        module_path(path, "package.entry", &entry)?;
        let suite = string(path, package, "package", "test")?.unwrap_or_else(|| "Test".to_owned());
        module_path(path, "package.test", &suite)?;

        let dependencies = match document.get("dependencies") {
            None => Vec::new(),
            Some(value) => {
                let table = value
                    .get_ref()
                    .as_table()
                    .ok_or_else(|| PkgError::shape(path, "`dependencies` - не таблица"))?;
                let mut out = Vec::new();
                for (key, value) in table {
                    out.push(dependency(path, key.get_ref(), value.get_ref())?);
                }
                out
            }
        };

        Ok(Self {
            dir: dir.to_path_buf(),
            name,
            root: dir.join(inside(path, "package.root", &root)?),
            entry,
            test: suite,
            dependencies,
            link: link(path, dir, document)?,
        })
    }

    /// Файл модуля-входа.
    #[must_use]
    pub fn entry_file(&self) -> PathBuf {
        self.file_of(&self.entry)
    }

    /// Файл модуля с тестами.
    #[must_use]
    pub fn test_file(&self) -> PathBuf {
        self.file_of(&self.test)
    }

    /// Файл, в котором лежал бы модуль этого проекта.
    fn file_of(&self, module: &str) -> PathBuf {
        adamas_elab::program::Directory::new(&self.root).file_of(module)
    }
}

/// Строковое поле таблицы. `None` - поля нет.
fn string(
    path: &Path,
    table: &DeTable<'_>,
    section: &str,
    key: &str,
) -> Result<Option<String>, PkgError> {
    match table.get(key) {
        None => Ok(None),
        Some(value) => value
            .get_ref()
            .as_str()
            .map(|it| Some(it.to_owned()))
            .ok_or_else(|| PkgError::shape(path, format!("`{section}.{key}` - не строка"))),
    }
}

/// Секция `[link]`. Её нет - связывать нечего сверх стандартной библиотеки C.
fn link(path: &Path, dir: &Path, document: &DeTable<'_>) -> Result<Link, PkgError> {
    let Some(value) = document.get("link") else {
        return Ok(Link::default());
    };
    let table = value
        .get_ref()
        .as_table()
        .ok_or_else(|| PkgError::shape(path, "`link` - не таблица"))?;
    let mut libraries = Vec::new();
    for written in strings(path, table, "link", "libraries")? {
        library_name(path, &written)?;
        libraries.push(written);
    }
    let mut paths = Vec::new();
    for written in strings(path, table, "link", "paths")? {
        paths.push(dir.join(inside(path, "link.paths", &written)?));
    }
    Ok(Link { libraries, paths })
}

/// Массив строк. Поля нет - пустой список.
fn strings(
    path: &Path,
    table: &DeTable<'_>,
    section: &str,
    key: &str,
) -> Result<Vec<String>, PkgError> {
    let Some(value) = table.get(key) else {
        return Ok(Vec::new());
    };
    let items = value
        .get_ref()
        .as_array()
        .ok_or_else(|| PkgError::shape(path, format!("`{section}.{key}` - не список строк")))?;
    items
        .iter()
        .map(|item| {
            item.get_ref().as_str().map(str::to_owned).ok_or_else(|| {
                PkgError::shape(path, format!("`{section}.{key}` - не список строк"))
            })
        })
        .collect()
}

/// Проверяет, что строка годится в `-l`: буквы, цифры, `_`, `-`, `.`, `+`.
///
/// Проверка не косметическая, и жанр её тот же, что у [`file_name`]: имя
/// уезжает в командную строку компилятора **и** в `dlopen`, а написанное в
/// манифесте разбора Adamas не проходило. `libraries = ["m -o /etc/passwd"]`
/// отсекается здесь.
fn library_name(path: &Path, written: &str) -> Result<(), PkgError> {
    let ok = !written.is_empty()
        && written
            .chars()
            .all(|it| it.is_alphanumeric() || matches!(it, '_' | '-' | '.' | '+'));
    if ok {
        return Ok(());
    }
    Err(PkgError::shape(
        path,
        format!(
            "`link.libraries` = `{written}` - не имя библиотеки: пишется оно как у `-l`, \
             без `lib` и без расширения"
        ),
    ))
}

/// Одна запись `[dependencies]`.
fn dependency(path: &Path, prefix: &str, value: &DeValue<'_>) -> Result<Dependency, PkgError> {
    let table = value.as_table().ok_or_else(|| {
        PkgError::shape(
            path,
            format!("`dependencies.{prefix}` - не таблица: зависимость пишется `{{ git = \"…\", tag = \"…\" }}`"),
        )
    })?;
    module_path(path, &format!("dependencies.{prefix}"), prefix)?;
    let section = format!("dependencies.{prefix}");
    let Some(git) = string(path, table, &section, "git")? else {
        // Точка в ключе TOML значит вложение, а не сегмент пути: `Data.Map = …`
        // даёт таблицу `Data` внутри `dependencies`. Сказать это прямо дешевле,
        // чем оставить «нет `git`» на таблице, которую никто не писал.
        return Err(PkgError::shape(
            path,
            format!(
                "в `[dependencies.{prefix}]` нет `git`; \
                 составной префикс пишется в кавычках: `\"{prefix}.Что-то\" = {{ git = … }}`"
            ),
        ));
    };
    let rev = string(path, table, &section, "rev")?;
    let tag = string(path, table, &section, "tag")?;
    let want = match (rev, tag) {
        (Some(rev), None) => Requirement::Rev(rev),
        (None, Some(tag)) => Requirement::Tag(tag),
        (None, None) => {
            return Err(PkgError::shape(
                path,
                format!(
                    "в `[dependencies.{prefix}]` нет ни `rev`, ни `tag` (§7.3: git URL плюс коммит или тег)"
                ),
            ));
        }
        (Some(_), Some(_)) => {
            return Err(PkgError::shape(
                path,
                format!("в `[dependencies.{prefix}]` написаны и `rev`, и `tag`: выберите одно"),
            ));
        }
    };
    Ok(Dependency {
        prefix: prefix.to_owned(),
        git,
        want,
    })
}

/// Проверяет, что строка - путь модуля: сегменты через точку, каждый из букв,
/// цифр, `_` и `'`.
///
/// Проверка не косметическая. Пути модулей, пришедшие из `import`, уже прошли
/// разбор Adamas и выйти за корень не могут; **написанное в манифесте разбора
/// не проходило**, поэтому `..` и слеш отсекаются здесь.
fn module_path(path: &Path, field: &str, written: &str) -> Result<(), PkgError> {
    let ok = !written.is_empty()
        && written.split('.').all(|segment| {
            !segment.is_empty()
                && segment
                    .chars()
                    .all(|it| it.is_alphanumeric() || it == '_' || it == '\'')
        });
    if ok {
        return Ok(());
    }
    Err(PkgError::shape(
        path,
        format!(
            "`{field}` = `{written}` - не путь модуля: сегменты через точку, каждый из букв, цифр, `_` и `'`"
        ),
    ))
}

/// Проверяет, что строка годится в имя файла: буквы, цифры, `_`, `-`.
///
/// Требование пришло от `adamas build`: артефакт кладётся под именем пакета, и
/// `name = "../../bin/sh"` в чужом манифесте писал бы файл вне проекта.
fn file_name(path: &Path, field: &str, written: &str) -> Result<(), PkgError> {
    let ok = !written.is_empty()
        && written
            .chars()
            .all(|it| it.is_alphanumeric() || it == '_' || it == '-');
    if ok {
        return Ok(());
    }
    Err(PkgError::shape(
        path,
        format!("`{field}` = `{written}` - не имя файла: буквы, цифры, `_` и `-`"),
    ))
}

/// Проверяет, что относительный путь не выводит за каталог манифеста.
///
/// `root = "../.."` в чужом репозитории открыл бы чтение файлов вне чекаута.
fn inside(path: &Path, field: &str, written: &str) -> Result<PathBuf, PkgError> {
    let candidate = PathBuf::from(written);
    let escapes = candidate.is_absolute()
        || candidate
            .components()
            .any(|it| matches!(it, std::path::Component::ParentDir));
    if escapes {
        return Err(PkgError::shape(
            path,
            format!("`{field}` = `{written}` выводит за каталог манифеста"),
        ));
    }
    Ok(candidate)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parsed(text: &str) -> Result<Manifest, PkgError> {
        Manifest::parse(Path::new("/проект"), Path::new("/проект/adamas.toml"), text)
    }

    #[test]
    fn defaults_are_the_cargo_shaped_ones() {
        let manifest = parsed("[package]\nname = \"example\"\n").expect("манифест");
        assert_eq!(manifest.root, Path::new("/проект/src"));
        assert_eq!(manifest.entry, "Main");
        assert_eq!(manifest.entry_file(), Path::new("/проект/src/Main.adamas"));
        assert_eq!(manifest.test_file(), Path::new("/проект/src/Test.adamas"));
        assert!(manifest.dependencies.is_empty());
    }

    /// Имя пакета называет файл артефакта, поэтому путём быть не вправе.
    #[test]
    fn a_package_name_that_is_a_path_is_refused() {
        let error = parsed("[package]\nname = \"../../bin/sh\"\n")
            .expect_err("путь в имени обязан быть отвергнут");
        assert!(format!("{error}").contains("не имя файла"), "{error}");
    }

    #[test]
    fn a_dependency_carries_url_and_commit() {
        let manifest = parsed(
            "[package]\nname = \"example\"\n\n[dependencies]\nStd = { git = \"file:///std\", rev = \"abc\" }\n",
        )
        .expect("манифест");
        assert_eq!(
            manifest.dependencies,
            vec![Dependency {
                prefix: "Std".to_owned(),
                git: "file:///std".to_owned(),
                want: Requirement::Rev("abc".to_owned()),
            }]
        );
    }

    /// Одно поле - один смысл: коммит **или** тег, но не оба сразу. Иначе
    /// пришлось бы объявлять, какое из двух главнее, а §7.3 такого не говорит.
    #[test]
    fn rev_and_tag_together_are_refused() {
        let error = parsed(
            "[package]\nname = \"e\"\n\n[dependencies]\nStd = { git = \"g\", rev = \"a\", tag = \"v1\" }\n",
        )
        .expect_err("оба поля обязаны быть отвергнуты");
        assert!(format!("{error}").contains("выберите одно"), "{error}");
    }

    #[test]
    fn a_dependency_without_a_commit_is_refused() {
        let error = parsed("[package]\nname = \"e\"\n\n[dependencies]\nStd = { git = \"g\" }\n")
            .expect_err("без коммита обязан быть отказ");
        assert!(format!("{error}").contains("ни `rev`, ни `tag`"), "{error}");
    }

    /// Точка в ключе TOML - вложение. Отказ обязан назвать это, а не молчать
    /// про таблицу, которой никто не писал.
    #[test]
    fn a_dotted_key_is_named_as_nesting() {
        let error = parsed(
            "[package]\nname = \"e\"\n\n[dependencies]\nData.Map = { git = \"g\", tag = \"v\" }\n",
        )
        .expect_err("вложение обязано быть названо");
        assert!(format!("{error}").contains("в кавычках"), "{error}");
    }

    #[test]
    fn a_quoted_dotted_prefix_works() {
        let manifest = parsed(
            "[package]\nname = \"e\"\n\n[dependencies]\n\"Data.Map\" = { git = \"g\", tag = \"v\" }\n",
        )
        .expect("манифест");
        assert_eq!(manifest.dependencies[0].prefix, "Data.Map");
    }

    /// Написанное в манифесте разбор Adamas не проходило, поэтому выход за
    /// корень отсекается здесь - и проверяется прогоном, а не доверием.
    #[test]
    fn a_root_outside_the_manifest_directory_is_refused() {
        let error = parsed("[package]\nname = \"e\"\nroot = \"../../etc\"\n")
            .expect_err("выход за каталог обязан быть отвергнут");
        assert!(format!("{error}").contains("выводит за каталог"), "{error}");
    }

    #[test]
    fn a_prefix_with_a_slash_is_refused() {
        let error = parsed(
            "[package]\nname = \"e\"\n\n[dependencies]\n\"../etc\" = { git = \"g\", tag = \"v\" }\n",
        )
        .expect_err("слеш в префиксе обязан быть отвергнут");
        assert!(format!("{error}").contains("не путь модуля"), "{error}");
    }

    /// Секции нет - список пуст, и стандартную библиотеку C в него писать не
    /// надо: её подключают сами обе стороны.
    #[test]
    fn without_a_link_section_nothing_is_linked() {
        let manifest = parsed("[package]\nname = \"e\"\n").expect("манифест");
        assert_eq!(manifest.link, Link::default());
    }

    /// Каталоги склеиваются с каталогом манифеста: `dlopen` относительного пути
    /// от каталога запуска не поймёт.
    #[test]
    fn a_link_section_carries_libraries_and_paths() {
        let manifest = parsed(
            "[package]\nname = \"e\"\n\n[link]\nlibraries = [\"curl\", \"z\"]\npaths = [\"vendor/lib\"]\n",
        )
        .expect("манифест");
        assert_eq!(manifest.link.libraries, ["curl", "z"]);
        assert_eq!(manifest.link.paths, [PathBuf::from("/проект/vendor/lib")]);
    }

    /// Имя уезжает в командную строку компилятора и в `dlopen`, а разбора
    /// Adamas оно не проходило.
    #[test]
    fn a_library_name_that_is_not_a_name_is_refused() {
        let error =
            parsed("[package]\nname = \"e\"\n\n[link]\nlibraries = [\"m -o /etc/passwd\"]\n")
                .expect_err("ключ в имени обязан быть отвергнут");
        assert!(format!("{error}").contains("не имя библиотеки"), "{error}");
    }

    /// Тот же запрет на выход за каталог, что у `package.root`.
    #[test]
    fn a_link_path_outside_the_manifest_directory_is_refused() {
        let error = parsed("[package]\nname = \"e\"\n\n[link]\npaths = [\"../../lib\"]\n")
            .expect_err("выход за каталог обязан быть отвергнут");
        assert!(format!("{error}").contains("выводит за каталог"), "{error}");
    }

    #[test]
    fn broken_toml_names_the_file() {
        let error = parsed("[package\nname =").expect_err("синтаксис обязан быть отвергнут");
        assert!(format!("{error}").contains("adamas.toml"), "{error}");
    }
}

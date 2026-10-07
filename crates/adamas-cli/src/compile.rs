//! `adamas build` и `adamas run`: программа в исполняемый файл (§7.1).
//!
//! # Чего у драйвера не было
//!
//! До волны 2 Фазы 9 драйвер умел `check` и `eval` - проверку и интерпретацию.
//! Понижение при этом было написано и проверено на корпусе **обоими**
//! бэкендами, но звали его только тесты `adamas-codegen`: компилятор языка
//! ничего не компилировал.
//!
//! # Во что собирается
//!
//! В нативный исполняемый файл `<проект>/.adamas/build/<имя пакета>`. Каталог
//! тот же, в котором `adamas-pkg` держит чекауты зависимостей: у проекта одно
//! место под порождённое, и заводить второе незачем.
//!
//! Собранный файл печатает **то же**, что `adamas eval`: это договор трёх
//! вычислителей, на котором стоит весь корпус (`adamas-codegen`,
//! `tests/agreement.rs`). Сверх ответа рантайм печатает на stderr счётчики
//! блоков - живых в конце прогона и выданных за прогон (§5.1).
//!
//! # Как выбран бэкенд
//!
//! Умолчание - **C**, и выбор измерен, а не назначен. Оба эмиттера берут
//! корпус целиком (107 из 107), но путь до бинаря у них разный: C-бэкенду
//! нужен один `cc`, LLVM-бэкенду - `llvm-as`, `opt` и `llc` не ниже
//! восемнадцатой версии ([`MINIMUM_MAJOR`](adamas_codegen::llvm::MINIMUM_MAJOR)).
//! Первое есть у всякого, кто собрал компилятор; второе - нет, и умолчанием
//! оно давало бы «инструмент не запускается» там, где программа ни при чём.
//!
//! `--backend llvm` берёт второй путь, и отказ у него **назван**: цепочку
//! задаёт `ADAMAS_LLVM_BIN`.

use std::path::{Path, PathBuf};

use adamas_codegen::llvm::{Pipeline, Toolchain};
use adamas_codegen::native::Native;
use adamas_core::source::SourceFile;
use anyhow::Context as _;

use crate::project;

/// Имя определения, с которого начинается программа.
const ENTRY: &str = "main";

/// Каким эмиттером идти от IR до объектника.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub(crate) enum Backend {
    /// Порождённый C, собранный `cc`.
    #[default]
    C,
    /// Текст `.ll`, собранный цепочкой LLVM.
    Llvm,
}

/// Собирает программу и отдаёт путь к исполняемому файлу.
///
/// # Errors
///
/// Программа не проверяется, форма вне среза бэкенда, инструмента нет либо
/// сборка отказала.
pub(crate) fn build(path: &Path, backend: Backend) -> anyhow::Result<PathBuf> {
    let opened = project::opened(path)?;
    let checked = project::checked(&opened.entry, opened.sources.as_ref())?;
    let mut signature = checked.signature;
    let mut metas = checked.metas;
    let entry = project::entry(&signature, ENTRY)?;
    let written = entry.term;

    // Специализация - требование §4.11 к release-сборке, и понижению проще
    // идти по терму без словарей. Сверяется собранное с ответом на терме
    // **написанном** - том самом, который считает `adamas eval`.
    //
    // Отказ переводится в текст здесь, а не `with_context`: `MonoError` несёт
    // `Rc`, как и всё ядро, и потому не `Send`.
    let made =
        adamas_elab::mono::specialise(&mut signature, &mut metas, &checked.instances, &written)
            .map_err(|why| {
                anyhow::anyhow!(
                    "{}",
                    adamas_l10n::tr!("cli-specialisation", name = checked.name, why = why)
                )
            })?;

    let dir = opened.store.join("build");
    // Чужие библиотеки едут в обе сборки одинаково: `-L`/`-l` у `cc` и у
    // линковки объектника `.ll`. Разойдись они, `--backend llvm` переставал бы
    // собирать ровно те программы, ради которых секция и заведена.
    let native = Native::new(&dir).linking(adamas_codegen::native::Linking {
        paths: opened.link.paths.clone(),
        libraries: opened.link.libraries.clone(),
    });
    let name = &opened.artefact;
    let binary = match backend {
        Backend::C => {
            let text = adamas_codegen::compile(&signature, &made.term)
                .map_err(|error| refused(&checked.units, &signature, error))?;
            let text = if entry.printed {
                text
            } else {
                adamas_codegen::silenced(&text)
            };
            native.build(name, &text)?
        }
        Backend::Llvm => {
            let artefacts = adamas_codegen::compile_llvm(&signature, &made.term)
                .map_err(|error| refused(&checked.units, &signature, error))?;
            let text = dir.join(format!("{name}.ll"));
            if let Some(parent) = text.parent() {
                std::fs::create_dir_all(parent).with_context(|| {
                    adamas_l10n::tr!("cli-cannot-create", path = parent.display())
                })?;
            }
            std::fs::write(&text, &artefacts.ll)
                .with_context(|| adamas_l10n::tr!("cli-cannot-write", path = text.display()))?;
            let tools = Toolchain::from_variable(adamas_codegen::llvm::TOOLS_VARIABLE);
            let object = Pipeline::optimised().run(&tools, &text, name)?;
            let support = if entry.printed {
                artefacts.support
            } else {
                adamas_codegen::silenced(&artefacts.support)
            };
            native.link(name, &object, &support)?
        }
    };
    eprintln!(
        "{}",
        adamas_l10n::tr!("cli-built", name = checked.name, path = binary.display())
    );
    Ok(binary)
}

/// Собирает и запускает. Отдаёт код возврата запущенного.
///
/// Потоки наследуются: собранная программа печатает ответ на stdout и счётчики
/// блоков на stderr, и перехватывать их драйверу незачем - спрашивали про
/// программу, а не про него.
///
/// # Errors
///
/// Те же, что у [`build`], плюс «собранное не запустилось».
pub(crate) fn run(path: &Path, backend: Backend) -> anyhow::Result<i32> {
    let binary = build(path, backend)?;
    let status = std::process::Command::new(&binary)
        .status()
        .with_context(|| adamas_l10n::tr!("cli-cannot-start", path = binary.display()))?;
    // Сигнал кода возврата не даёт, а нулём отвечать на него нельзя: оборванный
    // прогон отличается от успешного именно этим.
    Ok(status.code().unwrap_or(1))
}

/// Отказ понижения или эмиттера с местом, если оно известно (§10 вопрос 217).
///
/// Бэкенд называет определение, а не узел: спана в терме нет. Файл ищется по
/// имени - самый длинный путь модуля, которым имя начинается, а без такого -
/// входной файл, чьи члены не квалифицируются. Хвост специализации (`@…`,
/// `#ev`) снимается: у написанного определения его нет.
///
/// Отказ внутри прелюдии показывается у определения автора, до него
/// дотянувшегося: `Add#Int32` сам по себе не говорит, что чинить. Цепочку
/// запросов отдаёт понижение; у эмиттеров её нет, и место там - своё.
fn refused(
    units: &[(Option<String>, SourceFile)],
    signature: &adamas_core::sig::Signature,
    error: adamas_codegen::CompileError,
) -> anyhow::Error {
    let (definition, via) = match &error {
        adamas_codegen::CompileError::Lower(lower) => (lower.definition(), lower.via()),
        adamas_codegen::CompileError::Emit(emit) => (Some(emit.function()), &[][..]),
        adamas_codegen::CompileError::Llvm(llvm) => (Some(llvm.function()), &[][..]),
    };
    let Some(definition) = definition else {
        return error.into();
    };
    let written = |name: &str| {
        let name = name.strip_suffix("#ev").unwrap_or(name);
        name.split('@').next().unwrap_or(name).to_owned()
    };
    let place = |name: &str| {
        let short = written(name);
        let span = signature
            .origin(name)
            .or_else(|| signature.origin(&short))?;
        let (path, file) = units
            .iter()
            .filter(|(path, _)| {
                path.as_deref()
                    .is_some_and(|path| short.starts_with(&format!("{path}.")))
            })
            .max_by_key(|(path, _)| path.as_deref().map_or(0, str::len))
            .or_else(|| units.iter().find(|(path, _)| path.is_none()))?;
        (path.as_deref() != Some(adamas_elab::program::PRELUDE)).then_some((short, file, span))
    };
    let failed = written(definition);
    let found = std::iter::once(definition)
        .chain(via.iter().map(String::as_str))
        .find_map(place);
    match found {
        Some((short, file, span)) if short == failed => {
            anyhow::anyhow!("{}", adamas_elab::located(file, span, &error.to_string()))
        }
        Some((short, file, span)) => anyhow::anyhow!(
            "{}\n  {}",
            adamas_elab::located(file, span, &error.to_string()),
            adamas_l10n::tr!("cli-reached-from", failed = failed, short = short)
        ),
        None => anyhow::anyhow!(
            "{error}\n  {}",
            adamas_l10n::tr!("cli-in-definition", name = failed)
        ),
    }
}

#[cfg(test)]
mod tests {
    use adamas_codegen::CompileError;
    use adamas_codegen::EmitError;
    use adamas_codegen::lower::LowerError;
    use adamas_core::sig::Signature;
    use adamas_core::source::{SourceFile, Span};

    use super::refused;

    /// Отказ внутри прелюдии показывается у первого определения автора по
    /// цепочке запросов (§10 вопрос 217), и называет оба.
    ///
    /// Ошибка составлена руками: после вопроса 214 отказов внутри прелюдии не
    /// осталось, а правило драйвера от этого не перестало быть правилом.
    #[test]
    fn a_refusal_inside_the_prelude_is_shown_at_the_authors_definition() {
        let main = "xs : Int32\nxs = 1\n\nmain : Int32\nmain = xs\n";
        let prelude = "add : Int32\nadd = 2\n";
        let units = vec![
            (
                None,
                SourceFile::new("Main.adamas".to_owned(), main.to_owned()),
            ),
            (
                Some(adamas_elab::program::PRELUDE.to_owned()),
                SourceFile::new("Prelude.adamas".to_owned(), prelude.to_owned()),
            ),
        ];
        let mut signature = Signature::default();
        let at = main.find("main =").unwrap_or(0);
        signature.locate("main", Span::new(at, at + 4));
        signature.locate("Prelude.add", Span::new(0, 3));
        let error = CompileError::Lower(
            LowerError::Representation {
                at: "параметр недобранного вызова",
                want: "указательное значение".to_owned(),
                got: "плоское `Int32`".to_owned(),
            }
            .within("Prelude.add@_", vec!["main".to_owned()]),
        );
        let said = refused(&units, &signature, error).to_string();
        assert!(said.starts_with("Main.adamas:5:1:"), "{said}");
        assert!(
            said.contains("отказ в `Prelude.add`, до которого дотянулось `main`"),
            "{said}"
        );
    }

    /// Отказ эмиттера - тем же правилом: функцию он называет, место находит
    /// драйвер (§10 вопрос 217).
    ///
    /// Ошибка составлена руками: все отказы эмиттера, до которых дотягивалась
    /// пользовательская программа, сняты (§10 вопросы 215, 221), а правило
    /// драйвера от этого не перестало быть правилом. Хвост `@` специализации
    /// снимается.
    #[test]
    fn an_emitter_refusal_names_the_file_and_line() {
        let main = "xs : Int32\nxs = 1\n\nbody : Int32\nbody = xs\n";
        let units = vec![(
            None,
            SourceFile::new("Main.adamas".to_owned(), main.to_owned()),
        )];
        let mut signature = Signature::default();
        let at = main.find("body =").unwrap_or(0);
        signature.locate("body", Span::new(at, at + 4));
        let error = CompileError::Emit(EmitError::Parked {
            function: "body@".to_owned(),
            shape: "adamas_simd_4_Float32".to_owned(),
        });
        let said = refused(&units, &signature, error).to_string();
        assert!(said.starts_with("Main.adamas:5:1:"), "{said}");
        assert!(said.contains("переживает точку приостановки"), "{said}");
    }
}

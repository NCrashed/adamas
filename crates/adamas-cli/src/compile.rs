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
    let written = project::body(&signature, ENTRY)?;

    // Специализация - требование §4.11 к release-сборке, и понижению проще
    // идти по терму без словарей. Сверяется собранное с ответом на терме
    // **написанном** - том самом, который считает `adamas eval`.
    //
    // Отказ переводится в текст здесь, а не `with_context`: `MonoError` несёт
    // `Rc`, как и всё ядро, и потому не `Send`.
    let made =
        adamas_elab::mono::specialise(&mut signature, &mut metas, &checked.instances, &written)
            .map_err(|why| anyhow::anyhow!("{}: специализация отказала: {why}", checked.name))?;

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
            let text = adamas_codegen::compile(&signature, &made.term)?;
            native.build(name, &text)?
        }
        Backend::Llvm => {
            let artefacts = adamas_codegen::compile_llvm(&signature, &made.term)?;
            let text = dir.join(format!("{name}.ll"));
            if let Some(parent) = text.parent() {
                std::fs::create_dir_all(parent)
                    .with_context(|| format!("не удалось создать {}", parent.display()))?;
            }
            std::fs::write(&text, &artefacts.ll)
                .with_context(|| format!("не удалось записать {}", text.display()))?;
            let tools = Toolchain::from_variable(adamas_codegen::llvm::TOOLS_VARIABLE);
            let object = Pipeline::optimised().run(&tools, &text, name)?;
            native.link(name, &object, &artefacts.support)?
        }
    };
    println!("{}: собрано в {}", checked.name, binary.display());
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
        .with_context(|| format!("не удалось запустить {}", binary.display()))?;
    // Сигнал кода возврата не даёт, а нулём отвечать на него нельзя: оборванный
    // прогон отличается от успешного именно этим.
    Ok(status.code().unwrap_or(1))
}

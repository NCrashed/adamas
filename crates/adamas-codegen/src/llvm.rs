//! Конвейер LLVM: текст `.ll` в объектник (§9 Фаза 7, волна 1, треки A и A′).
//!
//! Привязка текстовая (решение 2026-09-15), поэтому «бэкенд» здесь - не
//! библиотека, слинкованная в компилятор, а **последовательность процессов**:
//! `llvm-as`, `opt`, `llc`. Отсюда всё содержимое модуля.
//!
//! # Конвейер - данные, а не код
//!
//! [`Pipeline`] есть список [`Stage`], и это шов **трека C**: собственный
//! проход схлопывания RC обязан встать между инлайнингом и остальным
//! конвейером (`docs/phase7-plan.md`, пункт 2), то есть посередине списка.
//! Зашей стадии в тело функции - и вставлять пришлось бы переписыванием
//! драйвера.
//!
//! Шов **занят дважды**. [`Pipeline::whole_program`] прикладывает рантайм
//! битовым кодом перед `opt`; [`Pipeline::collapsing`] ставит между `opt` и
//! рантаймом собственный проход ([`crate::collapse`], трек C закрыт
//! 2026-09-15). Порядок здесь и есть содержание трека: пара `dup`/`drop`
//! становится видна, когда подставлены тела **наших** функций, и перестаёт быть
//! парой, когда подставлены тела рантайма.
//!
//! Не всякая стадия - процесс: у [`Stage`] есть поле [`Stage::own`], и своя
//! стадия считается прямо здесь. Почему не плагином `opt` и не отдельным
//! бинарём - в шапке [`crate::collapse`], замером.
//!
//! # Минимальная версия проверяется прогоном
//!
//! [`MINIMUM_MAJOR`] - не пожелание в документации, а число, по которому
//! `tests/llvm.rs` берёт **вторую** цепочку инструментов и прогоняет ею тот же
//! `.ll`. Правило «консервативное подмножество IR» иначе не проверяется:
//! замеры 2026-09-08 показали, что матрица чтения `.ll` строго треугольная
//! (новая версия читает старый IR, обратно нет) и ломает её ровно один
//! необязательный флаг - `getelementptr inbounds nuw`, появившийся после 18.
//! Греп по формам такое ловит ровно до первого нового флага; прогон ловит
//! всегда. Дисциплина та же, что у MSRV, и заведена она так потому, что греп
//! по формам врал трижды подряд.
//!
//! Флаг проверен на своём выходе, а не только в чужом замере: GEP эмиттер
//! теперь печатает (трек A′), и 18.1.8 отвергает `inbounds nuw` разбором,
//! принимая и голый `getelementptr`, и `getelementptr inbounds`. То есть ломает
//! чтение `nuw`, а не `inbounds`.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Минимальная поддерживаемая мажорная версия LLVM.
///
/// Восемнадцать - не круглое число, а измеренное: 18.1.8 читает IR, написанный
/// 21.1.8, собирает его в объектник и даёт тот же ответ, если из IR убран
/// единственный необязательный флаг, появившийся позже (замеры 2026-09-08,
/// `docs/phase7-plan.md`). Ниже восемнадцати матрица не проверялась вовсе, и
/// объявлять её было бы обещанием без свидетеля.
pub const MINIMUM_MAJOR: u32 = 18;

/// Переменная окружения, называющая каталог с `llvm-as`, `opt` и `llc`.
pub const TOOLS_VARIABLE: &str = "ADAMAS_LLVM_BIN";

/// Она же для минимальной поддерживаемой версии.
pub const MINIMUM_TOOLS_VARIABLE: &str = "ADAMAS_LLVM_MIN_BIN";

/// Почему конвейер не доехал.
#[derive(Debug, thiserror::Error)]
pub enum ToolError {
    /// Инструмента нет: ни в названном каталоге, ни в `PATH`.
    #[error(
        "{tool} не запускается ({why}); каталог задаёт `{TOOLS_VARIABLE}`, а в dev-shell он есть"
    )]
    Missing {
        /// Какой инструмент.
        tool: String,
        /// Что сказала операционная система.
        why: String,
    },

    /// Стадия отработала с ненулевым кодом.
    #[error("{tool} отказал:\n{output}")]
    Failed {
        /// Какой инструмент.
        tool: String,
        /// Его вывод целиком.
        output: String,
    },

    /// Версию не прочитать: формат вывода `--version` разошёлся с ожидаемым.
    #[error("версия {tool} не прочиталась из `{output}`")]
    Version {
        /// Какой инструмент.
        tool: String,
        /// Что он напечатал.
        output: String,
    },

    /// Своя стадия не прочитала вход либо не записала выход.
    #[error("проход {pass} не прочитал вход либо не записал выход: {why}")]
    Own {
        /// Какой проход.
        pass: String,
        /// Что сказала операционная система.
        why: String,
    },
}

/// Откуда брать `llvm-as`, `opt` и `llc`.
///
/// Каталог, а не три пути: инструменты одной версии живут вместе, и собрать
/// цепочку из разных версий значило бы получить конвейер, чьи стадии читают
/// разный IR. Ровно этим свойством и пользуется проверка минимальной версии:
/// вторая цепочка - второй каталог, а не второй набор ключей.
#[derive(Clone, Debug)]
pub struct Toolchain {
    /// Каталог; `None` - искать в `PATH`.
    directory: Option<PathBuf>,
}

impl Toolchain {
    /// Цепочка из названного каталога.
    #[must_use]
    pub fn at(directory: impl Into<PathBuf>) -> Self {
        Self {
            directory: Some(directory.into()),
        }
    }

    /// Цепочка из `PATH`.
    #[must_use]
    pub fn from_path() -> Self {
        Self { directory: None }
    }

    /// Цепочка, названная переменной окружения; иначе - из `PATH`.
    ///
    /// Пустое значение считается неназванным: CI выставляет переменные матрицей,
    /// и незаполненная ветка даёт именно пустую строку, а не отсутствие.
    #[must_use]
    pub fn from_variable(variable: &str) -> Self {
        match std::env::var_os(variable) {
            Some(directory) if !directory.is_empty() => Self::at(directory),
            _ => Self::from_path(),
        }
    }

    /// Путь к инструменту.
    #[must_use]
    pub fn tool(&self, name: &str) -> PathBuf {
        match &self.directory {
            Some(directory) => directory.join(name),
            None => PathBuf::from(name),
        }
    }

    /// Мажорная версия цепочки.
    ///
    /// Спрашивается у `llvm-as`, потому что он же и разбирает `.ll`: версия
    /// разборщика и есть то, что проверяет правило подмножества.
    ///
    /// # Errors
    ///
    /// [`ToolError`] - инструмент не запустился либо напечатал не то.
    pub fn major(&self) -> Result<u32, ToolError> {
        let tool = self.tool("llvm-as");
        let shown = Command::new(&tool)
            .arg("--version")
            .output()
            .map_err(|why| ToolError::Missing {
                tool: tool.display().to_string(),
                why: why.to_string(),
            })?;
        let text = String::from_utf8_lossy(&shown.stdout).into_owned();
        parse_major(&text).ok_or_else(|| ToolError::Version {
            tool: tool.display().to_string(),
            output: text.trim().to_owned(),
        })
    }
}

/// Мажорная версия из вывода `--version`.
///
/// Ищется строка `LLVM version X.Y.Z`; её печатают все версии от 3.х до 22-й,
/// и разбирать её целиком незачем - правило подмножества про мажор.
fn parse_major(text: &str) -> Option<u32> {
    let at = text.find("LLVM version ")? + "LLVM version ".len();
    let rest = &text[at..];
    let end = rest.find(|it: char| !it.is_ascii_digit())?;
    rest[..end].parse().ok()
}

/// Свой проход конвейера: текст `.ll` на входе, текст `.ll` на выходе.
///
/// Указатель на функцию, а не замыкание: стадии - **данные**, и данные обязаны
/// оставаться `Clone` и `Debug`.
pub type Pass = fn(&str) -> String;

/// Одна стадия конвейера: инструмент, ключи и расширение своего выхода.
#[derive(Clone, Debug)]
pub struct Stage {
    /// Имя инструмента: ищется в цепочке. У своего прохода - имя прохода.
    pub tool: String,
    /// Ключи перед входным файлом.
    pub arguments: Vec<String>,
    /// Расширение файла, который стадия порождает.
    pub extension: String,
    /// Свой проход вместо внешнего процесса.
    ///
    /// Не всякая стадия есть инструмент: трек C ставит в конвейер собственное
    /// схлопывание RC ([`crate::collapse`]), и запускать его отдельным бинарём
    /// было бы платой без покупки. Плагин `opt` отвергнут замером - он
    /// **молча** не грузится в минимальную версию, - а отдельный бинарь даёт то
    /// же, что функция, плюс второй артефакт, который драйверу надо найти на
    /// диске. Версии LLVM проход не знает вовсе: он не линкуется с ней ни на
    /// каком шаге, и потому одинаков на 18 и на 21.
    pub own: Option<Pass>,
}

impl Stage {
    /// Стадия из имени, ключей и расширения.
    #[must_use]
    pub fn new(tool: &str, arguments: &[&str], extension: &str) -> Self {
        Self {
            tool: tool.to_owned(),
            arguments: arguments.iter().map(|it| (*it).to_owned()).collect(),
            extension: extension.to_owned(),
            own: None,
        }
    }

    /// Стадия, которую конвейер считает сам.
    #[must_use]
    pub fn pass(name: &str, pass: Pass, extension: &str) -> Self {
        Self {
            tool: name.to_owned(),
            arguments: Vec::new(),
            extension: extension.to_owned(),
            own: Some(pass),
        }
    }
}

/// Ключи `llc` при названном уровне оптимизации.
const fn llc(level: &'static str) -> [&'static str; 3] {
    [level, "-filetype=obj", "-relocation-model=pic"]
}

/// Конвейер: стадии в порядке прохождения.
///
/// Каждая читает файл предыдущей и пишет свой; имена файлов раздаёт
/// [`Self::run`] по расширению стадии. Промежуточные файлы остаются на диске
/// намеренно: без них отладка сводится к угадыванию, на какой стадии IR
/// перестал читаться.
///
/// Ключи стоят **перед** входным файлом, поэтому стадия вправе принести с собой
/// второй вход: `Stage::new("llvm-link", &["рантайм.bc"], "linked.bc")` даёт
/// `llvm-link рантайм.bc вход.bc -o выход.bc`. Не гипотеза про будущее, а
/// названная дыра: рантайм приезжает к `.ll` готовым объектником, и `opt` не
/// видит сквозь `adamas_con0` с `adamas_tag` (измерено 2026-09-15, см.
/// [`crate::emit_llvm`]). Закрывает её стадия, а не эмиттер.
#[derive(Clone, Debug)]
pub struct Pipeline {
    /// Стадии.
    pub stages: Vec<Stage>,
}

impl Pipeline {
    /// Штатный конвейер: разбор, `-O2`, объектник.
    ///
    /// `opt -O2`, а не `-passes='default<O2>'`: короткая форма принимается и
    /// восемнадцатой, и двадцать первой, а длинная - то же правило подмножества
    /// применительно к самим ключам.
    ///
    /// `-relocation-model=pic` - не украшение, а измеренное требование: по
    /// умолчанию `llc` берёт статическую модель, а обёртка компоновщика в
    /// dev-shell линкует PIE, и объектник отвергается ошибкой
    /// «`R_X86_64_32` ... can not be used when making a PIE object». Ключ
    /// древний и принимается обеими версиями.
    #[must_use]
    pub fn optimised() -> Self {
        Self {
            stages: vec![
                Stage::new("llvm-as", &[], "bc"),
                Stage::new("opt", &["-O2"], "opt.bc"),
                Stage::new("llc", &llc("-O2"), "o"),
            ],
        }
    }

    /// Тот же конвейер без оптимизации: свидетель того, что ответ не от `opt`.
    #[must_use]
    pub fn plain() -> Self {
        Self {
            stages: vec![
                Stage::new("llvm-as", &[], "bc"),
                Stage::new("llc", &llc("-O0"), "o"),
            ],
        }
    }

    /// Он же с рантаймом, приложенным битовым кодом **до** `opt`.
    ///
    /// Стадия одна - `llvm-link`, - и стоит она между разбором и оптимизацией,
    /// потому что смысл её ровно в том, чтобы `opt` увидел тела рантайма.
    ///
    /// *Здесь стояло «без неё треку C схлопывать нечего». Треком C замерено
    /// 2026-09-15 и не подтвердилось:* пара `dup`/`drop` снимается на уровне
    /// **вызовов**, то есть пока рантайм ещё непрозрачен, и
    /// [`Self::portable`] обходится без битового кода вовсе. Битовый код нужен
    /// не проходу, а его **мере**: без него остаток пары не увидеть чтениями
    /// счётчика.
    ///
    /// Измерено 2026-09-15 на `workload-fbip`: без стадии после `-O2` остаются
    /// вызовы всех восьми точек входа рантайма; со стадией - ни одного, а на их
    /// месте восемь чтений и восемь записей счётчика ссылок. Ответ и счётчик
    /// блоков при этом те же.
    ///
    /// **Стадии мало.** Битовый код, собранный clang'ом, несёт `target-cpu` и
    /// `target-features` хоста, а порождённый `.ll` не несёт ничего - строк цели
    /// в нём нет намеренно. Инлайнер требует, чтобы набор возможностей
    /// вызываемого был подмножеством набора вызывающего, и на пустом наборе
    /// вызывающего отказывает **всем**: со стадией и без неё вызовов остаётся
    /// поровну. Снимается это подготовкой `.bc`, а не конвейером, - см.
    /// свидетеля в `tests/llvm.rs`.
    ///
    /// Штатный конвейер этого не делает и делать не должен: `.bc` рантайма
    /// собран под **хост**, а `.ll` переносим, и вписать одно в другое значило
    /// бы отдать переносимость за инлайнинг во всех прогонах разом.
    #[must_use]
    pub fn whole_program(runtime: &Path) -> Self {
        Self {
            stages: vec![
                Stage::new("llvm-as", &[], "bc"),
                Stage::new("llvm-link", &[&runtime.display().to_string()], "linked.bc"),
                Stage::new("opt", &["-O2"], "opt.bc"),
                Stage::new("llc", &llc("-O2"), "o"),
            ],
        }
    }

    /// Конвейер трека C: инлайнинг, схлопывание RC, рантайм, вторая `opt`.
    ///
    /// Порядок стадий и есть содержание трека. `opt -O2 -S` подставляет тела
    /// **наших** функций - после него `dup` вызывающего и `drop` вызываемого
    /// лежат рядом; свой проход снимает пару; `llvm-link` приносит рантайм; и
    /// только вторая `opt` подставляет тела `adamas_dup` с `adamas_drop`, то
    /// есть превращает то, что осталось, в чтения и записи счётчика.
    ///
    /// Проход стоит **до** `llvm-link` намеренно: после него пара уже не пара, а
    /// две развилки по `rc`, и узнавать её пришлось бы по форме CFG. Здесь она
    /// узнаётся по имени вызова.
    ///
    /// `pass` равен `None` - тот же конвейер без одной стадии. Это не удобство,
    /// а требование к замеру: сравнивать «с проходом» надо с «без прохода» при
    /// прочих равных, а не со штатным [`Self::whole_program`], у которого
    /// `opt` зовётся однажды.
    #[must_use]
    pub fn collapsing(runtime: &Path, pass: Option<Pass>) -> Self {
        let mut stages = vec![
            Stage::new("llvm-as", &[], "bc"),
            Stage::new("opt", &["-O2", "-S"], "inlined.ll"),
        ];
        if let Some(pass) = pass {
            stages.push(Stage::pass("схлопывание RC", pass, "collapsed.ll"));
        }
        stages.push(Stage::new(
            "llvm-link",
            &[&runtime.display().to_string()],
            "linked.bc",
        ));
        stages.push(Stage::new("opt", &["-O2"], "opt.bc"));
        stages.push(Stage::new("llc", &llc("-O2"), "o"));
        Self { stages }
    }

    /// Он же **без рантайма**: пара снимается, а счётчик остаётся вызовом.
    ///
    /// Нужен затем, что рантайм в `.bc` собран под хост и читается только своей
    /// версией LLVM, а проверка минимальной версии гоняет тот же `.ll` обеими
    /// цепочками. Здесь рантайм приходит объектником на линковке, как у
    /// [`Self::optimised`], и потому конвейер целиком идёт и на 18-й.
    ///
    /// Замер (2026-09-15) показал, что треку C этого **довольно**: пара
    /// схлопывается от инлайнинга наших функций, а инлайнинг рантайма нужен
    /// только тому, кто мерит остаток в чтениях счётчика.
    #[must_use]
    pub fn portable(pass: Option<Pass>) -> Self {
        let mut stages = vec![
            Stage::new("llvm-as", &[], "bc"),
            Stage::new("opt", &["-O2", "-S"], "inlined.ll"),
        ];
        if let Some(pass) = pass {
            stages.push(Stage::pass("схлопывание RC", pass, "collapsed.ll"));
        }
        stages.push(Stage::new("llc", &llc("-O2"), "o"));
        Self { stages }
    }

    /// Прогоняет конвейер и отдаёт путь к последнему файлу.
    ///
    /// # Errors
    ///
    /// [`ToolError`] - инструмента нет либо стадия отказала.
    pub fn run(&self, tools: &Toolchain, source: &Path, stem: &str) -> Result<PathBuf, ToolError> {
        let directory = source.parent().unwrap_or(Path::new("."));
        let mut input = source.to_path_buf();
        for stage in &self.stages {
            let output = directory.join(format!("{stem}.{}", stage.extension));
            if let Some(pass) = stage.own {
                let text = std::fs::read_to_string(&input)
                    .and_then(|text| std::fs::write(&output, pass(&text)))
                    .map_err(|why| ToolError::Own {
                        pass: stage.tool.clone(),
                        why: why.to_string(),
                    });
                text?;
                input = output;
                continue;
            }
            let tool = tools.tool(&stage.tool);
            let done = Command::new(&tool)
                .args(&stage.arguments)
                .arg(&input)
                .arg("-o")
                .arg(&output)
                .output()
                .map_err(|why| ToolError::Missing {
                    tool: tool.display().to_string(),
                    why: why.to_string(),
                })?;
            if !done.status.success() {
                return Err(ToolError::Failed {
                    tool: tool.display().to_string(),
                    output: format!(
                        "{}{}",
                        String::from_utf8_lossy(&done.stdout),
                        String::from_utf8_lossy(&done.stderr)
                    ),
                });
            }
            input = output;
        }
        Ok(input)
    }
}

#[cfg(test)]
mod tests {
    use super::parse_major;

    #[test]
    fn the_major_is_read_from_what_llvm_as_prints() {
        let printed = "LLVM (http://llvm.org/):\n  LLVM version 18.1.8\n  Optimized build.\n";
        assert_eq!(parse_major(printed), Some(18));
    }

    #[test]
    fn a_line_without_a_version_is_not_guessed() {
        assert_eq!(parse_major("совсем не то"), None);
    }
}

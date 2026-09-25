//! Программа из нескольких файлов: `import`, порядок между файлами (§4.8).
//!
//! # Файл - это модуль
//!
//! Подключённый файл элаборируется ровно так, как §4.8 элаборирует тело
//! `module M where …`: члены поднимаются на верхний уровень под
//! квалифицированным именем (`Data.Map.insert`), короткое имя внутри файла
//! ищется по той же лестнице, а снаружи пишется путь. Второго механизма
//! квалификации заводить не пришлось - он уже написан, и этим выбор и
//! обоснован.
//!
//! Различие одно, и оно названо в [`crate::expr::Enclosing`]: файл ничем не
//! объемлется, поэтому формы, которые §4.8 запрещает **вложенному** модулю,
//! законны в нём. Класс и инстанс остаются именами программы, а не членами
//! файла, - так их и описывает §4.4 («классы, доступные без импорта»).
//!
//! # Порядок между файлами
//!
//! **Импорт входит в порядок объявлений наравне с прочими** (§10 вопрос 178).
//! Подключённый файл объявляется целиком в точке, где написан `import`:
//! написанное ниже видит его весь, написанное выше - не видит вовсе. Это то же
//! ordered scoping, что §4.8 задаёт внутри файла, и другого правила для границы
//! файлов поэтому не заводится.
//!
//! Альтернатива - «модуль виден всему файлу, где бы `import` ни стоял» -
//! отвергнута замером, а не доводом. Она написана пробной правкой в 14 строк
//! (подъём `import`'ов в начало списка объявлений) и прогнана: во всём наборе
//! она меняет **один** вердикт - программа, зовущая имя выше строки `import`,
//! из отвергнутой становится принятой. Корпус, драйвер и девять прочих
//! свидетелей импорта на неё не отзываются. Покупается за неё, значит, не
//! поведение, а второе правило видимости рядом с первым.
//!
//! Из порядка следует и судьба кольца: у цикла импортов такого порядка нет, и
//! выразить взаимную видимость нечем - `mutual` живёт внутри файла. Кольцо
//! поэтому отвергается названной причиной ([`ElabError::ImportCycle`]), а не
//! разрешается молча.
//!
//! # Где берутся файлы
//!
//! Чтением занимается [`Sources`], а не элаборация: `adamas-elab` о диске не
//! знает и знать не обязан. [`Directory`] кладёт `Data.Map` в
//! `<корень>/Data/Map.adamas`, [`Memory`] держит ту же карту в памяти - тестам
//! и всякому, у кого программа не на диске.

use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use adamas_core::meta::Metas;
use adamas_core::sig::{Scope, Signature};
use adamas_core::source::{SourceFile, Span};
use adamas_parser::ast::{self, Module};

use crate::class::Instances;
use crate::decl::{Importer, Pass};
use crate::diag::{Diagnostic, Severity};
use crate::error::ElabError;
use crate::expr::Enclosing;
use crate::fixity::Fixities;
use crate::lifecycle::Observed;
use crate::own::Owned;
use crate::recover::Refusals;
use crate::warn::Warnings;

/// Откуда берутся тексты подключаемых модулей.
pub trait Sources {
    /// Текст модуля под написанным путём. `None` - такого модуля нет.
    fn text(&self, path: &str) -> Option<String>;

    /// Где модуль искали - это попадает в отказ «модуль не найден».
    fn looked(&self, path: &str) -> String;
}

/// Каталог на диске: `Data.Map` - это `<корень>/Data/Map.adamas`.
#[derive(Clone, Debug)]
pub struct Directory {
    root: PathBuf,
}

impl Directory {
    /// Корень поиска модулей.
    #[must_use]
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    /// Файл, в котором лежал бы модуль.
    ///
    /// Сегменты пути - идентификаторы: разбор не пропустит ни `..`, ни слеша,
    /// поэтому выйти за корень написанным путём нечем.
    #[must_use]
    pub fn file_of(&self, path: &str) -> PathBuf {
        let mut out = self.root.clone();
        for segment in path.split('.') {
            out.push(segment);
        }
        out.set_extension("adamas");
        out
    }
}

impl Sources for Directory {
    fn text(&self, path: &str) -> Option<String> {
        std::fs::read_to_string(self.file_of(path)).ok()
    }

    fn looked(&self, path: &str) -> String {
        self.file_of(path).display().to_string()
    }
}

/// Путь прелюдии, подключаемой неявно (§4.4). Знает его и ядро - третья
/// ступень `Signature::convention` отличает прелюдное объявление от своего.
pub use adamas_core::prim::PRELUDE;

/// Текст прелюдии, вшитый в компилятор.
///
/// Вшит, а не прочитан с диска, и довод простой: `adamas eval один-файл.adamas`
/// обязан работать где угодно, а каталога рядом с бинарём у него нет. Цена -
/// правка прелюдии требует пересборки компилятора; для прелюдии из полусотни
/// строк это дешевле, чем раскладка файлов, которую пришлось бы искать.
const PRELUDE_TEXT: &str = include_str!("../../../lib/Prelude.adamas");

/// Карта «путь - текст» в памяти.
#[derive(Clone, Debug, Default)]
pub struct Memory {
    modules: HashMap<String, String>,
}

impl Memory {
    /// Пустая карта.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Та же карта с ещё одним модулем.
    #[must_use]
    pub fn with(mut self, path: &str, text: &str) -> Self {
        self.modules.insert(path.to_owned(), text.to_owned());
        self
    }
}

impl Sources for Memory {
    fn text(&self, path: &str) -> Option<String> {
        self.modules.get(path).cloned()
    }

    fn looked(&self, _path: &str) -> String {
        "модули в памяти".to_owned()
    }
}

/// Файл программы вместе с тем, что о нём известно.
#[derive(Debug)]
pub struct Unit {
    /// Путь модуля. `None` - входной файл: он и есть программа, и его члены
    /// не квалифицируются.
    pub path: Option<String>,
    /// Текст вместе с именем - им рисуется позиция отказа.
    pub file: SourceFile,
    /// Дерево, если текст разобрался.
    pub module: Option<Module>,
}

/// Диагностика вместе с файлом, которому принадлежит её спан.
#[derive(Debug)]
pub struct Located {
    /// Индекс в [`Program::units`].
    pub unit: usize,
    /// Что сказано.
    pub diagnostic: Diagnostic,
}

/// Что известно о программе после полного прохода.
#[derive(Debug)]
pub struct Program {
    /// Файлы в порядке **объявления**: подключённый стоит раньше того, кто его
    /// подключил. Входной файл идёт первым - он корень обхода, а не первый
    /// объявленный.
    pub units: Vec<Unit>,
    /// Что успело объявиться - одна сигнатура на всю программу.
    pub signature: Option<Signature>,
    /// Отказы и предупреждения в порядке появления.
    pub diagnostics: Vec<Located>,
    /// Дырки прохода. Отдаются наружу затем же, зачем их принимает
    /// [`crate::elaborate_into`]: мономорфизация (§6) читает решения, а
    /// хранилище одно на прогон (§10 вопрос 51).
    pub metas: Metas,
    /// Что знает разрешение инстансов (§3.5) - оно общее на программу.
    pub instances: Instances,
    /// Что §7.2 показывает читателю про **входной** файл: жизнь ресурсов и
    /// погашение меток ([`crate::lifecycle`]).
    ///
    /// Входного, а не программы: места здесь - спаны, а спан живёт в тексте
    /// своего файла. Редактор рисует их по буферу, который открыт, и место из
    /// чужого текста подчеркнуло бы в нём случайную строку - тот же довод, что
    /// у диагностики подключённого модуля.
    ///
    /// Собирается по ходу элаборации, в той самой точке, где решается вставка
    /// `drop` ([`crate::lifecycle`]): второй проход, повторяющий правило,
    /// разошёлся бы с ним молча.
    pub observed: Observed,
}

impl Program {
    /// Первый отказ, если он был.
    #[must_use]
    pub fn error(&self) -> Option<&Located> {
        self.diagnostics
            .iter()
            .find(|it| it.diagnostic.severity == Severity::Error)
    }

    /// Текст диагностики для терминала - вместе с исходником того файла, к
    /// которому она относится.
    ///
    /// Диагностика чужой программы даёт текст без исходника: указывать спаном в
    /// чужой файл значило бы подчеркнуть случайную строку, а падать на этом -
    /// ронять компилятор ради печати.
    #[must_use]
    pub fn rendered(&self, located: &Located) -> String {
        self.units.get(located.unit).map_or_else(
            || located.diagnostic.message(),
            |unit| located.diagnostic.rendered(&unit.file),
        )
    }
}

/// Разбор, элаборация и проверка типов программы целиком (§4.8).
///
/// `entry` - входной файл: его члены квалификации не получают, потому что он и
/// есть программа. Всё, что он подключает, объявляется под своим написанным
/// путём.
#[must_use]
pub fn analyze(entry: SourceFile, sources: &dyn Sources) -> Program {
    let parsed = adamas_parser::parse(entry.text());
    let mut loader = Loader {
        sources,
        declared: Vec::new(),
        frames: vec![Frame {
            path: None,
            imported: Vec::new(),
            seeded: Vec::new(),
        }],
        units: vec![Unit {
            path: None,
            file: entry,
            module: None,
        }],
        blame: Vec::new(),
        broken: Vec::new(),
    };
    let module = match parsed {
        Ok(module) => module,
        Err(error) => {
            return Program {
                units: loader.units,
                signature: None,
                diagnostics: vec![Located {
                    unit: 0,
                    diagnostic: Diagnostic::of_parse(&error),
                }],
                metas: Metas::default(),
                instances: Instances::default(),
                observed: Observed::new(),
            };
        }
    };

    let mut signature = Signature::default();
    let mut metas = Metas::default();
    let mut owned = Owned::default();
    let mut fixities = Fixities::default();
    let mut instances = Instances::default();
    let mut warnings = Warnings::new();
    let mut observed = Observed::new();
    let mut refusals = Refusals::new();
    let outcome = {
        let pass = Pass {
            signature: &mut signature,
            metas: &mut metas,
            owned: &mut owned,
            fixities: &mut fixities,
            instances: &mut instances,
            warnings: &mut warnings,
            observed: &mut observed,
        };
        let mut pass = pass;
        match loader.seed(&module.decls, None, pass.reborrow()) {
            Err(error) => Err(error),
            Ok(()) => {
                crate::decl::elaborate_file(&module.decls, None, pass, &mut loader, &mut refusals)
            }
        }
    };

    let mut units = loader.units;
    units[0].module = Some(module);
    // Отказы входного файла - его спанами; отказы подключённых уже разложены по
    // своим единицам в `blame`. Первыми идут чужие: подключённый файл
    // объявляется раньше того, кто его подключил, и читается панель сверху.
    //
    // Отказ, поднятый **значением**, доходит сюда только если восстановление
    // его не пережило; его спан живёт в тексте входного файла по построению -
    // чужой уехал бы в `blame`.
    let mut diagnostics = loader.blame;
    if let Err(error) = outcome {
        refusals.refused(error, Vec::new());
    }
    diagnostics.extend(refusals.iter().map(|error| Located {
        unit: 0,
        diagnostic: Diagnostic::of_error(error),
    }));
    diagnostics.extend(warnings.iter().map(|warning| Located {
        unit: 0,
        diagnostic: Diagnostic::of_warning(warning),
    }));
    Program {
        units,
        signature: Some(signature),
        diagnostics,
        metas,
        instances,
        observed,
    }
}

/// Файл, который сейчас элаборируется, и что он успел подключить.
struct Frame {
    /// Путь. `None` - входной файл.
    path: Option<String>,
    /// Пути, написанные в его `import`, в порядке написания.
    imported: Vec<String>,
    /// Короткие имена, положенные в область видимости прелюдией.
    ///
    /// Нужны затем, чтобы поймать столкновение: имя, пришедшее сюда из
    /// прелюдии и открытое потом импортом, даёт два разных объявления под
    /// одним написанием ([`ElabError::PreludeClash`]).
    seeded: Vec<Rc<str>>,
}

struct Loader<'a> {
    sources: &'a dyn Sources,
    /// Пути уже объявленных модулей в порядке объявления.
    declared: Vec<String>,
    /// Стек подключения: вершина - файл, который элаборируется сейчас.
    frames: Vec<Frame>,
    units: Vec<Unit>,
    /// Отказы, случившиеся внутри подключённых файлов, каждый со своим файлом.
    blame: Vec<Located>,
    /// Пути модулей, которые уже отказали: второй `import` не элаборирует их
    /// заново.
    broken: Vec<String>,
}

impl Loader<'_> {
    /// Область видимости текущего файла: закрыто всё, чего он не подключал.
    ///
    /// Пустой стек невозможен - входной кадр кладётся при сборке и не
    /// снимается, - но паниковать по этому поводу не за что: без кадра закрыть
    /// нечего, и проход идёт дальше.
    fn restrict(&self, signature: &mut Signature) {
        let Some(frame) = self.frames.last() else {
            return;
        };
        let hidden: Vec<&str> = self
            .declared
            .iter()
            .map(String::as_str)
            .filter(|path| {
                frame.path.as_deref() != Some(*path) && !frame.imported.iter().any(|it| it == *path)
            })
            .collect();
        signature.scope_mut().restrict(hidden);
    }

    /// Объявляет модуль, если он ещё не объявлен.
    fn declare(&mut self, path: &str, span: Span, mut pass: Pass<'_>) -> Result<(), ElabError> {
        if self.declared.iter().any(|it| it == path) {
            return Ok(());
        }
        // Уже отказавший модуль второй раз не элаборируется. До восстановления
        // (§10 вопрос 177) памяти этой не требовалось - первый отказ
        // останавливал проход, и второго `import` того же пути не случалось, -
        // а теперь проход доходит до конца файла, и без неё модуль,
        // подключённый дважды, отдавал бы свои отказы дважды, а члены,
        // успевшие объявиться, давали бы сверх них «определение уже
        // существует»: отказ, которого в тексте нет.
        //
        // Наверх идёт `InModule` - он не печатается (см. `recover`), а сами
        // отказы уже лежат в `blame` со своим файлом.
        if self.broken.iter().any(|it| it == path) {
            return Err(ElabError::InModule {
                path: Rc::from(path),
                span,
            });
        }
        // Кольцо: путь уже элаборируется выше по стеку. Порядка у такой
        // программы нет, а выразить взаимную видимость между файлами нечем -
        // `mutual` живёт внутри файла (§10 вопрос 178).
        if self
            .frames
            .iter()
            .any(|it| it.path.as_deref() == Some(path))
        {
            let mut through: Vec<&str> = self
                .frames
                .iter()
                .skip_while(|it| it.path.as_deref() != Some(path))
                .map(|it| it.path.as_deref().unwrap_or("вход"))
                .collect();
            through.push(path);
            return Err(ElabError::ImportCycle {
                through: through.join(" -> "),
                span,
            });
        }
        // Прелюдия берётся у источника первой: проект вправе положить свой
        // `Std/Prelude.adamas` рядом и тем заменить вшитый целиком - та же
        // свобода, какую §4.8 даёт всякому имени.
        let text = match self.sources.text(path) {
            Some(text) => text,
            None if path == PRELUDE => PRELUDE_TEXT.to_owned(),
            None => {
                return Err(ElabError::UnknownModule {
                    path: Rc::from(path),
                    file: self.sources.looked(path),
                    span,
                });
            }
        };
        let file = SourceFile::new(self.sources.looked(path), text);
        let parsed = adamas_parser::parse(file.text());
        let at = self.units.len();
        self.units.push(Unit {
            path: Some(path.to_owned()),
            file,
            module: None,
        });
        let module = match parsed {
            Ok(module) => module,
            Err(error) => {
                self.blamed(at, Diagnostic::of_parse(&error));
                self.broken.push(path.to_owned());
                return Err(ElabError::InModule {
                    path: Rc::from(path),
                    span,
                });
            }
        };

        self.frames.push(Frame {
            path: Some(path.to_owned()),
            imported: Vec::new(),
            seeded: Vec::new(),
        });
        let outer = pass.signature.set_scope(Scope::of(path));
        self.restrict(pass.signature);
        let within = Enclosing::file(Rc::from(path));
        // Своё восстановление на каждый файл: граница определения проходит по
        // файлу (§10 вопрос 177), а отказы отсюда надо разложить по **этой**
        // единице - позицию свою они несут в её тексте.
        let mut refusals = Refusals::new();
        // Жизненные циклы подключённого файла **отбрасываются**, и это не
        // экономия. Место у них - спан, а спан живёт в тексте своего файла:
        // отданный наружу вместе с циклами входного, он указал бы редактору в
        // строку открытого буфера, которой не соответствует ничего. Тот же
        // довод, что у диагностики подключённого модуля, только лечение проще -
        // показывать их некому: редактор рисует подсказки по буферу, который
        // открыт, а открытый буфер здесь и есть входной файл.
        let mut aside = Observed::new();
        let outcome = {
            let mut inner = pass.reborrow();
            inner.observed = &mut aside;
            match self.seed(&module.decls, Some(path), inner.reborrow()) {
                Err(error) => Err(error),
                Ok(()) => crate::decl::elaborate_file(
                    &module.decls,
                    Some(&within),
                    inner,
                    self,
                    &mut refusals,
                ),
            }
        };
        pass.signature.set_scope(outer);
        self.frames.pop();
        self.units[at].module = Some(module);
        let broken = !refusals.is_empty() || outcome.is_err();
        if let Err(error) = outcome {
            refusals.refused(error, Vec::new());
        }
        for error in refusals.iter() {
            self.blamed(at, Diagnostic::of_error(error));
        }
        if broken {
            self.broken.push(path.to_owned());
            // Наверх идёт «модуль не проходит проверку», а не сами отказы: их
            // спаны живут в **чужом** тексте, и всякий, кто нарисует их по
            // исходнику входного файла, подчеркнёт случайную строку. Сами они
            // уехали в `blame` вместе со своим файлом.
            return Err(ElabError::InModule {
                path: Rc::from(path),
                span,
            });
        }
        self.declared.push(path.to_owned());
        Ok(())
    }

    /// Запоминает отказ вместе с файлом, в котором он случился.
    fn blamed(&mut self, unit: usize, diagnostic: Diagnostic) {
        self.blame.push(Located { unit, diagnostic });
    }

    /// Кладёт прелюдию в область видимости файла, ничего в нём не написав.
    ///
    /// Два случая пропуска, и оба обязательны. Сама прелюдия себя не
    /// подключает - это было бы кольцо. И файл, написавший `import Std.Prelude`
    /// **сам**, неявного подключения не получает: его список и есть его
    /// решение, а `import Std.Prelude ()` пустым списком - способ отказаться от
    /// прелюдии вовсе. Новой формы для отказа поэтому не заводится.
    ///
    /// Имена кладутся **все**: у прелюдии нет «внутреннего», её список и есть
    /// её поверхность. Затеняются они обычным порядком - объявление файла
    /// сильнее, и корпус, где сотня программ объявляет свой `Bool`, этим и
    /// держится.
    fn seed(
        &mut self,
        decls: &[ast::Decl],
        path: Option<&str>,
        mut pass: Pass<'_>,
    ) -> Result<(), ElabError> {
        if path == Some(PRELUDE) {
            return Ok(());
        }
        let written = decls.iter().any(|decl| match &decl.kind {
            ast::DeclKind::Import(import) => import.written() == PRELUDE,
            _ => false,
        });
        if written {
            return Ok(());
        }
        // Спан отсутствующей строки: подключения в тексте нет, и указывать
        // отказу некуда. Отказать здесь может только сломанная прелюдия, то
        // есть сам компилятор, - и читать его будет не автор программы.
        let span = Span::new(0, 0);
        // Имена файла считаются **до** подключения, и прелюдное имя, совпавшее
        // с ними, не кладётся вовсе. Затенение «по порядку» тут не годится:
        // псевдоним встаёт раньше всех объявлений, и собственный `data Bool`
        // оказался бы слабее прелюдного - проверено, программа с тремя
        // конструкторами отвергалась «конструктор `Both` не принадлежит типу
        // `Std.Prelude.Bool`».
        //
        // Цена названа: имя, объявленное **ниже** по файлу, закрывает прелюдное
        // и выше себя, то есть здесь ordered scoping не работает. Направление
        // выбрано сознательно - прелюдия не меняет смысла написанного ни в
        // одной строке, а недостающее имя видно сразу.
        // Считаются **объявления** файла, а не всё, что `declares` называет:
        // открытые импортом имена сюда не входят намеренно. Иначе прелюдное
        // имя не клалось бы вовсе, и столкновение с чужим разрешалось бы молча
        // в пользу чужого - тихий выбор там, где решение принимает автор.
        let mine: std::collections::HashSet<Rc<str>> = decls
            .iter()
            .filter(|decl| !matches!(decl.kind, ast::DeclKind::Import(_)))
            .flat_map(crate::recover::declares)
            .map(|name| Rc::from(&*name))
            .collect();
        self.declare(PRELUDE, span, pass.reborrow())?;
        let head = format!("{PRELUDE}.");
        let names: Vec<_> = pass
            .signature
            .names()
            .into_iter()
            .filter(|name| name.starts_with(&head))
            .collect();
        for full in names {
            let short = &full[head.len()..];
            if short.contains('.') || mine.contains(short) {
                continue;
            }
            pass.signature.scope_mut().alias(short, &full);
            // Столкновение стережётся только у **имён-соглашений** (§4.3):
            // их читает сам компилятор, и читает после того, как область
            // видимости свёрнута, - молчаливый выбор там даёт программу,
            // которая собирается и обрывается на прогоне. У обычного имени
            // такого механизма нет вовсе, и импорт, затеняющий прелюдное
            // `not`, - нормальная работа, а не двусмысленность.
            if conventional(short) {
                if let Some(frame) = self.frames.last_mut() {
                    frame.seeded.push(Rc::from(short));
                }
            }
        }
        Ok(())
    }

    /// Кладёт имена подключённого модуля в область видимости текущего файла.
    fn open(
        decl: &ast::ImportDecl,
        path: &str,
        signature: &mut Signature,
        seeded: &[Rc<str>],
    ) -> Result<(), ElabError> {
        // Квалифицированный доступ под коротким префиксом: `Map.insert` при
        // `import Data.Map as Map`. Псевдоним ставится на каждого объявленного
        // члена, а не на префикс, потому что искать его будут полным именем.
        let prefix = decl.prefix();
        if prefix != path {
            let head = format!("{path}.");
            for name in signature.names() {
                let Some(rest) = name.strip_prefix(&head) else {
                    continue;
                };
                let written = format!("{prefix}.{rest}");
                signature.scope_mut().alias(&written, &name);
            }
        }
        for opened in &decl.open {
            // Имя, уже положенное прелюдией, и открываемое отсюда - два разных
            // объявления под одним написанием. Выбирать между ними компилятор
            // не вправе (§4.4), и отказ стоит здесь, на строке импорта, где
            // автор его и починит.
            if seeded.iter().any(|it| **it == *opened.text) {
                return Err(ElabError::PreludeClash {
                    module: Rc::from(path),
                    name: Rc::clone(&opened.text),
                    span: opened.span,
                });
            }
            let full = format!("{path}.{}", opened.text);
            let Some(definition) = signature.lookup(&full) else {
                return Err(ElabError::NotExported {
                    module: Rc::from(path),
                    name: Rc::clone(&opened.text),
                    span: opened.span,
                });
            };
            // Семейство открывается вместе с конструкторами, эффект - вместе с
            // операциями. Правило то же, каким §4.8 поднимает их из тела
            // модуля, и довод тот же: представление семейства - это его
            // конструкторы. Перечислять их по одному §4.4 не требует - она
            // требует, чтобы имя приходило из названного модуля, а оно приходит.
            let sprouts: Vec<adamas_core::term::Name> = match &definition.kind {
                adamas_core::sig::DefinitionKind::Data { constructors, .. } => constructors.clone(),
                adamas_core::sig::DefinitionKind::Effect { operations, .. } => operations.clone(),
                _ => Vec::new(),
            };
            let declared: adamas_core::term::Name = Rc::from(full.as_str());
            signature.scope_mut().alias(&opened.text, &declared);
            for sprout in sprouts {
                let Some(short) = sprout.strip_prefix(&format!("{path}.")) else {
                    continue;
                };
                signature.scope_mut().alias(short, &sprout);
            }
        }
        Ok(())
    }
}

impl Importer for Loader<'_> {
    fn import(
        &mut self,
        decl: &ast::ImportDecl,
        span: Span,
        mut pass: Pass<'_>,
    ) -> Result<(), ElabError> {
        let path = decl.written();
        self.declare(&path, span, pass.reborrow())?;
        if let Some(frame) = self.frames.last_mut() {
            frame.imported.push(path.clone());
        }
        self.restrict(pass.signature);
        let seeded = self
            .frames
            .last()
            .map(|frame| frame.seeded.clone())
            .unwrap_or_default();
        Self::open(decl, &path, pass.signature, &seeded)
    }
}

/// Читает ли это имя сам компилятор (§4.3).
///
/// Список закрыт и совпадает с тем, что спрашивает
/// [`adamas_core::sig::Signature::convention`]: `Bool` с конструкторами,
/// классы представления. Только у них молчаливый выбор между прелюдным и
/// написанным даёт расхождение между проверкой типов и понижением.
fn conventional(name: &str) -> bool {
    use adamas_core::prim;
    matches!(
        name,
        prim::BOOL | prim::TRUE | prim::FALSE | prim::UNIT | prim::FLAT | prim::PRIMITIVE
    )
}

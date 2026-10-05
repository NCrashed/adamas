//! Что драйверу отвечает на вопрос «какая это программа»: вход, корни поиска
//! модулей, каталог под артефакты (§4.8, §7.1, §7.3).
//!
//! # Программа, а не файл
//!
//! Команды берут **входной** файл и разрешают его `import`'ы (§4.8): корень
//! поиска модулей - каталог этого файла, `Data.Map` - это
//! `<каталог>/Data/Map.adamas`.
//!
//! # Проект, а не файл
//!
//! Тем же аргументом принимается **каталог** проекта или путь к его
//! `adamas.toml`: тогда корни поиска берутся из манифеста, а git-зависимости
//! достаются и подключаются (§7.3, `adamas-pkg`).
//!
//! Написанный **файл** тоже ищет манифест - вверх по дереву, до ближайшего.
//! Решение это переигранное: сперва вверх не искалось вовсе, доводом «чужой
//! `adamas.toml` этажом выше молча меняет смысл проверки». Довод не выдержал
//! замера трека B: `adamas check tests/golden/project/Std/Order.adamas`
//! отвечал «модуль `Std.Base` не найден: искали `…/Std/Std/Base.adamas`», то
//! есть инструмент не проверял файл **собственного** проекта. Редактор тот же
//! корень берёт из `rootUri`; у терминала его взять неоткуда, кроме как из
//! манифеста. Корни при этом манифестные, а входом остаётся написанный файл -
//! спрашивали про него.

use std::path::{Path, PathBuf};

use adamas_core::source::SourceFile;
use anyhow::Context as _;

/// Открытая программа: где её вход, где её модули, куда класть артефакты.
pub(crate) struct Opened {
    /// Входной файл.
    pub(crate) entry: PathBuf,
    /// Файл тестового модуля. `None` - программа не проект, и `[package]` с
    /// полем `test` у неё нет.
    pub(crate) tests: Option<PathBuf>,
    /// Откуда берутся подключаемые модули.
    pub(crate) sources: Box<dyn adamas_elab::program::Sources>,
    /// Каталог под всё, что порождается сборкой.
    pub(crate) store: PathBuf,
    /// Имя, под которым кладётся собранный файл.
    pub(crate) artefact: String,
    /// С чем линковать: секция `[link]` манифеста (§5.3). У программы без
    /// манифеста пуста - остаётся стандартная библиотека C, и её подключают
    /// сами обе стороны.
    pub(crate) link: adamas_pkg::manifest::Link,
}

/// Что известно о программе после прохода.
pub(crate) struct Checked {
    /// Имя входного файла - им подписаны сообщения.
    pub(crate) name: String,
    /// Сколько файлов вошло в программу.
    pub(crate) files: usize,
    /// Сигнатура целиком.
    pub(crate) signature: adamas_core::sig::Signature,
    /// Дырки прохода: их читает мономорфизация.
    pub(crate) metas: adamas_core::meta::Metas,
    /// Что знает разрешение инстансов.
    pub(crate) instances: adamas_elab::class::Instances,
    /// Имена, объявленные прелюдией, - в счёт объявлений они не входят.
    pub(crate) prelude: std::collections::HashSet<adamas_core::term::Name>,
    /// Файлы программы с путями модулей: `None` - входной. По ним драйвер
    /// называет место отказа, случившегося после проверки (§10 вопрос 217).
    pub(crate) units: Vec<(Option<String>, SourceFile)>,
}

/// Откуда берутся входной файл и корни поиска модулей.
///
/// Три случая. Каталог или сам `adamas.toml` - проект целиком, и вход берётся
/// из манифеста. Файл **внутри** проекта - корни из манифеста, а входом
/// остаётся написанный файл. Файл вне всякого проекта - как раньше: корень
/// поиска есть его каталог.
///
/// # Errors
///
/// Манифест собран не так или зависимость не достаётся.
pub(crate) fn opened(path: &Path) -> anyhow::Result<Opened> {
    let named = if path.is_dir() {
        Some(path.to_path_buf())
    } else if path
        .file_name()
        .is_some_and(|it| it == adamas_pkg::manifest::MANIFEST)
    {
        Some(
            path.parent()
                .unwrap_or_else(|| Path::new("."))
                .to_path_buf(),
        )
    } else {
        None
    };
    let written = named.is_none().then(|| path.to_path_buf());
    let Some(dir) = named.or_else(|| enclosing(path)) else {
        let root = path.parent().unwrap_or_else(|| Path::new("."));
        return Ok(Opened {
            entry: path.to_path_buf(),
            tests: None,
            sources: Box::new(adamas_elab::program::Directory::new(root)),
            store: root.join(adamas_pkg::fetch::STORE),
            artefact: stem(path),
            link: adamas_pkg::manifest::Link::default(),
        });
    };

    let project = adamas_pkg::Project::open(&dir)?;
    // Достача - действие, и молчать о нём нельзя: сборка, впервые клонирующая
    // репозиторий, отличается от той, что взяла готовый чекаут, только
    // временем, и человеку это надо видеть.
    for dependency in &project.resolved {
        if dependency.refreshed {
            eprintln!("{}: достаю {}", dependency.canonical, dependency.rev);
        }
    }
    if project.relocked {
        eprintln!("{}: обновлён", adamas_pkg::lock::LOCKFILE);
    }
    Ok(Opened {
        entry: written.unwrap_or_else(|| project.entry_file()),
        tests: Some(project.manifest.test_file()),
        store: dir.join(adamas_pkg::fetch::STORE),
        artefact: project.manifest.name.clone(),
        link: project.manifest.link.clone(),
        sources: Box::new(project.sources),
    })
}

/// Проект, внутри которого лежит файл: ближайший `adamas.toml` вверх по дереву.
///
/// Путь приводится к абсолютному: без этого `adamas check main.adamas` смотрел
/// бы ровно в текущий каталог и никуда выше. Файла нет - искать нечего, и
/// отказ «не удалось прочитать» скажет об этом лучше.
fn enclosing(file: &Path) -> Option<PathBuf> {
    let full = std::fs::canonicalize(file).ok()?;
    let mut at = full.parent()?;
    loop {
        if at.join(adamas_pkg::manifest::MANIFEST).is_file() {
            return Some(at.to_path_buf());
        }
        at = at.parent()?;
    }
}

/// Имя артефакта у программы без манифеста: основа имени входного файла.
fn stem(path: &Path) -> String {
    path.file_stem()
        .map_or_else(|| "программа".to_owned(), |it| it.to_string_lossy().into())
}

/// Разбор, элаборация и проверка типов - общая половина всех команд.
///
/// Проход идёт по **программе**, а не по файлу: `import` подключает соседние
/// файлы, и корень их поиска даёт [`opened`] - каталог входного файла или
/// манифест проекта (§4.8, §7.3). Программа из одного файла проходит тем же
/// путём: подключать нечего, и область видимости у неё пуста.
///
/// Отказ печатается вместе с исходником **того** файла, которому принадлежит
/// его спан: позиция в чужом файле, нарисованная по входному, указывала бы на
/// случайную строку.
///
/// Элаборация при этом не в TCB - она отдаёт терм, корректность его
/// устанавливает `check` (§3).
///
/// # Errors
///
/// Файл не читается, программа не разбирается либо не проходит проверку.
pub(crate) fn checked(
    entry: &Path,
    sources: &dyn adamas_elab::program::Sources,
) -> anyhow::Result<Checked> {
    let program = analyzed(entry, sources)?;
    let name = program.units.first().map_or_else(
        || entry.display().to_string(),
        |it| it.file.name().to_owned(),
    );
    // Прелюдия подключается неявно (§4.4), и считать её файлом программы -
    // неправда: автор её не писал и в отчёте не ждёт. По той же причине её
    // объявления не входят в счёт ниже.
    let files = program
        .units
        .iter()
        .filter(|it| it.path.as_deref() != Some(adamas_elab::program::PRELUDE))
        .count();
    let signature = program
        .signature
        .ok_or_else(|| anyhow::anyhow!("{name}: проход не отдал сигнатуры"))?;
    Ok(Checked {
        name,
        files,
        signature,
        metas: program.metas,
        instances: program.instances,
        prelude: program.prelude.into_iter().collect(),
        units: program
            .units
            .into_iter()
            .map(|unit| (unit.path, unit.file))
            .collect(),
    })
}

/// Программа целиком - вместе с деревьями и исходниками каждого файла.
///
/// Отдельно от [`checked`] затем, что `doc` (§7.1) читает **написанное**:
/// порядок объявлений и комментарии живут в дереве и в тексте, а в сигнатуре
/// их нет. Печать отказов при этом одна на обоих - иначе два ответа на один
/// вопрос разъехались бы.
///
/// # Errors
///
/// Файл не читается, программа не разбирается либо не проходит проверку.
pub(crate) fn analyzed(
    entry: &Path,
    sources: &dyn adamas_elab::program::Sources,
) -> anyhow::Result<adamas_elab::program::Program> {
    let text = std::fs::read_to_string(entry)
        .with_context(|| format!("не удалось прочитать {}", entry.display()))?;
    let file = SourceFile::new(entry.display().to_string(), text);

    let program = adamas_elab::program::analyze(file, sources);
    // Все отказы разом, а не первый (§10 вопрос 177): восстановление на границе
    // определения доводит проход до конца файла, и печатать из трёх найденных
    // один значило бы вернуть читателю тот же цикл «правка - перезапуск -
    // следующая ошибка», ради которого вопрос и заводился.
    //
    // Пустой строкой между ними: у отказа своя каретка под своей строкой
    // исходника, и встык они читаются одним абзацем.
    let refused: Vec<String> = program
        .diagnostics
        .iter()
        .filter(|it| it.diagnostic.severity == adamas_elab::Severity::Error)
        .map(|it| program.rendered(it))
        .collect();
    if !refused.is_empty() {
        anyhow::bail!("{}", refused.join("\n\n"));
    }
    for diagnostic in &program.diagnostics {
        eprintln!("{}", program.rendered(diagnostic));
    }
    Ok(program)
}

/// Тело определения с подставленными аргументами уровня и row.
///
/// Параметры подставляются нулём и пустой row. Выбор назван: подъём даёт
/// row-параметр всякой написанной сигнатуре, поэтому требовать нулевой арности
/// значило бы не вычислять почти ничего, а вычисление идёт над одним
/// экземпляром - что и требуется, чтобы посмотреть на терм.
///
/// # Errors
///
/// Имени нет в сигнатуре либо у него нет тела.
pub(crate) fn body(
    signature: &adamas_core::sig::Signature,
    name: &str,
) -> anyhow::Result<adamas_core::term::Term> {
    use adamas_core::level::Level;
    use adamas_core::row::Row;
    use adamas_core::term::Term;

    let Some(definition) = signature.lookup(name) else {
        anyhow::bail!("определение `{name}` не найдено");
    };
    let Some(body) = &definition.body else {
        anyhow::bail!("у `{name}` нет тела: постулат вычислять нечем");
    };
    let levels: Vec<Level> = (0..definition.level_arity)
        .map(|_| Level::number(0))
        .collect();
    let rows: Vec<Row<Term>> = (0..definition.row_arity).map(|_| Row::empty()).collect();
    Ok(body.substitute_levels(&levels).substitute_rows(&rows))
}

/// Хендлер ввода-вывода, который ставится вокруг эффектной точки входа (§10
/// вопрос 12).
const IO_RUN: &str = "Std.IO.run";

/// Метки без аргументов, которые [`IO_RUN`] гасит целиком.
const IO_LABELS: [&str; 3] = ["Std.IO.Console", "Std.IO.Files", "Std.IO.Foreign"];

/// Отказ, который [`IO_RUN`] гасит наверху: `Except IOError`, и только с этим
/// аргументом.
const IO_EXCEPT: (&str, &str) = ("Std.Except.Except", "Std.IO.IOError");

/// Что исполнять и печатать ли ответ.
pub(crate) struct Entry {
    /// Терм: тело определения либо он же под хендлером `Std.IO.run`.
    pub(crate) term: adamas_core::term::Term,
    /// Печатать ли ответ. Ответ-единицу программа не вычисляла, а ради печати
    /// исполнялась: `MkUnit` под её выводом - шум.
    pub(crate) printed: bool,
}

/// Точка входа: [`body`], обёрнутое хендлером ввода-вывода, если тип того
/// просит.
///
/// `main : {Console} A` - приостановленное вычисление `(ω _ : Unit) -> {Console}
/// A`, и исполнить его значит погасить метки. Гасит их `Std.IO.run`, если
/// программа его подключила и row не несёт ничего сверх его меток; иначе терм
/// отдаётся как есть, и ответом будет функция - как было до хендлера.
///
/// Хвост row у написанной сигнатуры есть всегда - его даёт подъём (§3.4), - и
/// [`body`] подставляет вместо него пустую row: лишних меток он не добавит.
///
/// Аргумент типа `run` - кодомен приостановки, а живёт он под её связыванием.
/// Потому обёртка стоит под `let _ : Unit = MkUnit`: индекс ноль там значит то
/// же, что в кодомене, и сдвигать терм не нужно.
///
/// # Errors
///
/// Те же, что у [`body`].
pub(crate) fn entry(signature: &adamas_core::sig::Signature, name: &str) -> anyhow::Result<Entry> {
    use adamas_core::mult::Mult;
    use adamas_core::row::Tail;
    use adamas_core::term::Term;
    use adamas_core::visibility::Visibility;

    let written = body(signature, name)?;
    let unit = signature.unit();
    let is_unit = |ty: &Term| matches!(ty, Term::Const(head, ..) if &**head == unit);
    let ty = signature.lookup(name).map(|it| &it.ty);
    let wrapped = match ty {
        Some(Term::Pi(binder, _, domain, row, codomain))
            if binder.visibility == Visibility::Explicit
                && is_unit(domain)
                && !matches!(row.tail(), Some(Tail::Meta(_)))
                && !row.is_empty()
                && row.labels().iter().all(handled)
                && signature.lookup(IO_RUN).is_some() =>
        {
            Some(codomain)
        }
        _ => None,
    };
    let Some(answer) = wrapped else {
        return Ok(Entry {
            printed: !ty.is_some_and(is_unit),
            term: written,
        });
    };
    let made = signature
        .constructors(unit)
        .and_then(|it| it.first())
        .ok_or_else(|| anyhow::anyhow!("у единицы `{unit}` нет конструктора"))?;
    let run = reference(signature, IO_RUN).apply([(**answer).clone(), reference(signature, name)]);
    Ok(Entry {
        printed: !is_unit(answer),
        term: Term::Let(
            Mult::Many,
            "_".into(),
            std::rc::Rc::new(Term::constant(unit)),
            std::rc::Rc::new(Term::constant(made)),
            std::rc::Rc::new(run),
        ),
    })
}

/// Ссылка на определение с нулевыми уровнями и пустыми row - те же аргументы,
/// что [`body`] подставляет в тело.
///
/// Ссылка, а не тело: терм входа специализация нормализует, и `let _ = putStr
/// …` вставленного тела, чей результат не читается, ушёл бы вместе с выводом.
/// Определение понижается своим телом, со всеми его связываниями.
fn reference(signature: &adamas_core::sig::Signature, name: &str) -> adamas_core::term::Term {
    use adamas_core::level::Level;
    use adamas_core::row::Row;
    use adamas_core::term::{Args, Term};

    let (levels, rows) = signature
        .lookup(name)
        .map_or((0, 0), |it| (it.level_arity, it.row_arity));
    Term::Const(
        name.into(),
        (0..levels).map(|_| Level::number(0)).collect(),
        Args::rows((0..rows).map(|_| Row::empty())),
    )
}

/// Гасит ли [`IO_RUN`] метку: своя `Std.IO` без аргументов либо `Except IOError`.
fn handled(label: &adamas_core::row::Label<adamas_core::term::Term>) -> bool {
    use adamas_core::term::Term;

    if label.arguments.is_empty() {
        return IO_LABELS.contains(&&*label.name);
    }
    let (except, error) = IO_EXCEPT;
    &*label.name == except
        && matches!(label.arguments.as_slice(), [Term::Const(name, ..)] if &**name == error)
}

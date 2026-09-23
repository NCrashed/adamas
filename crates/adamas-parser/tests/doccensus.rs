//! Перепись комментариев над объявлениями корпуса: чем документируется
//! объявление (§7.1, `adamas doc`).
//!
//! Здесь живёт **замер**, на котором стоит запись в
//! `docs/phase9-w3-trackD-notes.md`, - чтобы довод проверялся прогоном, а не
//! памятью о прогоне.
//!
//! Два теста и они разного рода. `census` помечен `#[ignore]`: это счёт, а не
//! проверка, и числа его при всяком новом файле корпуса меняются законно.
//! `every_doc_marker_documents_something` - обычный.
//!
//! Его прежняя редакция держала утверждение «`-- |` в корпусе не написан ни
//! разу», и держала она **цену введения маркера**: переозначить нечего.
//! Маркер введён (волна 4, трек B), цена уплачена, и запрет писать `-- |`
//! означал бы теперь запрет документировать корпус. На его месте стоит
//! утверждение, которое несущее сегодня: **всякий написанный `-- |`
//! действительно что-то документирует.** Правило привязки
//! ([`adamas_parser::docs`]) требует, чтобы между блоком и объявлением не было
//! пустой строки, и промах здесь молчаливый - автор пишет документацию, а в
//! выводе `adamas doc` её нет.
//!
//! Счёт:
//! `cargo test -p adamas-parser --test doccensus -- --ignored --nocapture`

use std::path::{Path, PathBuf};

use adamas_parser::ast::{Decl, DeclKind};
use adamas_parser::token::TokenKind;

/// Корпус лежит в корне, а не в пакете: те же файлы читают несколько слоёв.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

/// Все `.adamas` корпуса в устойчивом порядке.
///
/// Нечитаемый каталог пропускается молча, а не роняет обход: пустой ответ
/// ловят сами тесты - обоим корпус нужен непустым.
fn fixtures() -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut stack = vec![corpus()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).into_iter().flatten().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "adamas") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Объявления всех уровней вложенности: смещение начала, само объявление,
/// глубина.
fn flatten<'a>(decls: &'a [Decl], out: &mut Vec<(usize, &'a Decl, usize)>, depth: usize) {
    for decl in decls {
        out.push((decl.span.start(), decl, depth));
        match &decl.kind {
            DeclKind::Module(module) => flatten(&module.members, out, depth + 1),
            DeclKind::Mutual(members) => flatten(members, out, depth + 1),
            DeclKind::Class(class) => flatten(&class.members, out, depth + 1),
            DeclKind::Resource(resource) => flatten(&resource.members, out, depth + 1),
            _ => {}
        }
    }
}

/// Места, к которым документация вправе привязаться.
///
/// Шире [`flatten`]: конструктор семейства и операция эффекта - не `Decl`, но
/// имена программы, и `adamas doc` документирует их наравне с прочими. Считай
/// их объявлениями - и корпус, документирующий конструкторы, читался бы как
/// корпус с висячими маркерами.
fn sites(decls: &[Decl], out: &mut Vec<adamas_core::source::Span>) {
    for decl in decls {
        out.push(decl.span);
        match &decl.kind {
            DeclKind::Data(data) => out.extend(data.constructors.iter().map(|it| it.span)),
            DeclKind::Effect(effect) => out.extend(effect.operations.iter().map(|it| it.span)),
            DeclKind::Module(module) => sites(&module.members, out),
            DeclKind::Mutual(members) => sites(members, out),
            DeclKind::Class(class) => sites(&class.members, out),
            DeclKind::Resource(resource) => sites(&resource.members, out),
            _ => {}
        }
    }
}

/// Как назвать объявление в распечатке.
fn label(decl: &Decl) -> String {
    match &decl.kind {
        DeclKind::Alias { name, .. } => format!("type {}", name.text),
        DeclKind::Signature { name, .. } => format!("sig {}", name.text),
        DeclKind::Clauses { name, .. } => format!("clauses {}", name.text),
        DeclKind::Data(data) => format!("data {}", data.name.text),
        DeclKind::Module(module) => format!("module {}", module.name.text),
        DeclKind::Class(class) => match &class.name {
            Some(name) => format!("instance {}", name.text),
            None => "class/instance".to_owned(),
        },
        DeclKind::Resource(resource) => format!("resource {}", resource.name.text),
        DeclKind::Effect(effect) => format!("effect {}", effect.name.text),
        DeclKind::Extern(ext) => format!("extern {}", ext.name.text),
        DeclKind::Import(_) => "import".to_owned(),
        DeclKind::Mutual(_) => "mutual".to_owned(),
        DeclKind::Fixity(_) => "fixity".to_owned(),
        DeclKind::Export(_) => "export".to_owned(),
    }
}

/// Всякий написанный `-- |` действительно что-то документирует.
///
/// Промах здесь молчаливый: правило привязки требует, чтобы между блоком и
/// объявлением не было пустой строки, и автор, поставивший её, документацию
/// пишет, а в выводе `adamas doc` не получает. Тест ловит ровно это - маркер,
/// не доставшийся ни одному объявлению корпуса.
///
/// Проверяется вместе с этим и сам лексер: блок, который перестал помечаться
/// [`adamas_parser::token::CommentKind::Doc`], не найдётся ни у одного
/// объявления, и тест покраснеет.
#[test]
fn every_doc_marker_documents_something() {
    let mut dangling = Vec::new();
    let mut documented = 0usize;
    let files = fixtures();
    assert!(!files.is_empty(), "корпус не найден: {:?}", corpus());
    for path in &files {
        let text = std::fs::read_to_string(path).expect("фикстура читается");
        let (Ok(tokens), Ok(module)) =
            (adamas_parser::tokenize(&text), adamas_parser::parse(&text))
        else {
            continue;
        };
        let written = tokens
            .comments
            .iter()
            .filter(|it| text[it.span.start()..it.span.end()].starts_with("-- |"))
            .count();
        if written == 0 {
            continue;
        }
        let mut places = Vec::new();
        sites(&module.decls, &mut places);
        let attached = places
            .iter()
            .filter(|span| adamas_parser::docs::attached(&text, &tokens.comments, **span).is_some())
            .count();
        documented += attached;
        if attached < written {
            dangling.push((path.clone(), written, attached));
        }
    }
    assert!(
        dangling.is_empty(),
        "маркер написан, а объявления не достался: {dangling:?}"
    );
    // Иначе счёт сходился бы и на корпусе, где маркера нет вовсе, - то есть
    // тест был бы зелен при выключенном лексере.
    assert!(
        documented > 0,
        "в корпусе не осталось ни одного документированного объявления"
    );
}

/// Счёт, а не проверка: сколько объявлений корпуса несут комментарий сверху.
///
/// Привязка комментария - к **следующему** токену, поэтому «комментарий над
/// объявлением» здесь значит «комментарий, привязанный к первому токену
/// объявления». Отдельно считается шапка файла: она привязана к первому
/// объявлению, но говорит о фикстуре, а не о нём.
#[test]
#[ignore = "счёт для docs/phase9-w3-trackD-notes.md, не проверка"]
fn census() {
    let files = fixtures();
    assert!(!files.is_empty(), "корпус не найден: {:?}", corpus());
    let (mut decls, mut commented, mut unparsed) = (0usize, 0usize, 0usize);
    let (mut comments, mut blocks, mut at_eof) = (0usize, 0usize, 0usize);
    let (mut glued, mut loose, mut header) = (0usize, 0usize, 0usize);

    for path in &files {
        let text = std::fs::read_to_string(path).expect("фикстура читается");
        let Ok(tokens) = adamas_parser::tokenize(&text) else {
            unparsed += 1;
            continue;
        };
        comments += tokens.comments.len();
        for comment in &tokens.comments {
            if text[comment.span.start()..comment.span.end()].starts_with("{-") {
                blocks += 1;
            }
            if tokens
                .tokens
                .get(comment.token as usize)
                .is_some_and(|token| token.kind == TokenKind::Eof)
            {
                at_eof += 1;
            }
        }
        let Ok(module) = adamas_parser::parse(&text) else {
            unparsed += 1;
            continue;
        };

        let mut flat = Vec::new();
        flatten(&module.decls, &mut flat, 0);
        decls += flat.len();

        for (start, decl, depth) in &flat {
            let hits: Vec<_> = tokens
                .comments
                .iter()
                .filter(|comment| {
                    tokens
                        .tokens
                        .get(comment.token as usize)
                        .is_some_and(|token| token.span.start() == *start)
                })
                .collect();
            let (Some(first), Some(last)) = (hits.first(), hits.last()) else {
                continue;
            };
            commented += 1;
            // Шапка файла: блок стоит в самом начале и привязан к первому
            // объявлению. Говорит она о файле, а не об объявлении.
            let is_header = *start == flat[0].0 && first.span.start() < 4;
            if is_header {
                header += 1;
            }
            // Прилегает ли блок: между его концом и объявлением нет пустой
            // строки. Таблица комментариев этого не несёт - только исходник.
            if text[last.span.end()..*start].contains("\n\n") {
                loose += 1;
            } else {
                glued += 1;
            }
            let body: Vec<_> = hits
                .iter()
                .map(|comment| text[comment.span.start()..comment.span.end()].replace('\n', " / "))
                .collect();
            println!(
                "{}\t{depth}\t{}\t{}\t{}",
                path.strip_prefix(corpus()).unwrap_or(path).display(),
                if is_header { "header" } else { "body" },
                label(decl),
                body.join(" / ")
            );
        }
    }

    println!("файлов: {}, не разобрано: {unparsed}", files.len());
    println!("объявлений: {decls}, с комментарием сверху: {commented}");
    println!("из них шапка файла: {header}");
    println!("прилегает: {glued}, отбито пустой строкой: {loose}");
    println!("комментариев: {comments}, блочных: {blocks}, перед Eof: {at_eof}");
}

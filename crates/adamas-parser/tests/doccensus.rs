//! Перепись комментариев над объявлениями корпуса: чем документируется
//! объявление (§7.1, `adamas doc`).
//!
//! Разновидности «док» у комментария нет, и трек D волны 3 Фазы 9 её не
//! вводил: форма комментария есть поверхность языка. Здесь живёт **замер**, на
//! котором стоит запись в `docs/phase9-w3-trackD-notes.md`, - чтобы довод
//! проверялся прогоном, а не памятью о прогоне.
//!
//! Два теста и они разного рода. `no_fixture_writes_a_doc_marker` - обычный:
//! он держит утверждение, на котором стоит рекомендация, - написания-кандидата
//! в корпусе нет, значит ввод маркера ни одного комментария не переозначит.
//! `census` помечен `#[ignore]`: это счёт, а не проверка, и числа его при
//! всяком новом файле корпуса меняются законно.
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

/// Написания-кандидаты в маркер документации в корпусе не встречаются.
///
/// На этом стоит вся цена ветки «отдельная разновидность»: вводя `-- |` или
/// `---`, мы не переозначиваем ни одного уже написанного комментария. Тест
/// покраснеет ровно тогда, когда кто-то начнёт этими написаниями
/// пользоваться, - и тогда цену надо пересчитать.
#[test]
fn no_fixture_writes_a_doc_marker() {
    let mut piped = Vec::new();
    let mut tripled = Vec::new();
    let files = fixtures();
    assert!(!files.is_empty(), "корпус не найден: {:?}", corpus());
    for path in files {
        let text = std::fs::read_to_string(&path).expect("фикстура читается");
        let Ok(tokens) = adamas_parser::tokenize(&text) else {
            continue;
        };
        for comment in &tokens.comments {
            let body = &text[comment.span.start()..comment.span.end()];
            if body.starts_with("-- |") {
                piped.push(path.clone());
            }
            if body.starts_with("---") {
                tripled.push(path.clone());
            }
        }
    }
    assert!(piped.is_empty(), "`-- |` уже написан: {piped:?}");
    assert!(tripled.is_empty(), "`---` уже написан: {tripled:?}");
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

//! LSP-сервер Adamas (§7.2, §9 Фаза 9).
//!
//! # Что умеет
//!
//! `initialize`, `textDocument/didOpen`, `didChange`, `didClose` и
//! `textDocument/publishDiagnostics` - те же отказы и предупреждения, что
//! печатает `adamas check`, на тех же местах.
//!
//! # Проход целиком, без инкрементального ядра
//!
//! §7.2 называет Salsa-подход, и на горизонте многофайловых проектов он
//! остаётся верным. Сегодня его не покупают: круг «правка -> диагностика» на
//! капстоуне в 944 строки идёт **42 мс** (release, лучшее из десяти) при
//! бюджете интерактивности порядка 100 мс. Сам `adamas check` на том же файле
//! идёт 36-41 мс, то есть весь счёт - это проверка типов, а протокол не стоит
//! ничего. Граф зависимостей за такие деньги не берут, и синхронный сервер на
//! потоках здесь ровно к месту - отменять нечего.
//!
//! Отсюда же `TextDocumentSyncKind::FULL`: клиент шлёт текст целиком, сервер
//! не ведёт инкрементальных правок буфера. Протокол это разрешает, а второй
//! путь применения правок был бы вторым местом, где текст может разойтись с
//! тем, что видит человек.
//!
//! # Текст сообщения берётся у драйвера
//!
//! Сообщение собирает [`adamas_elab::analyze`] - тот же вызов, что делает
//! `adamas check`. Свидетель совпадения - `crates/adamas-cli/tests/lsp.rs`: он
//! запускает драйвер процессом на всём корпусе отказов и собирает его вывод
//! обратно из того, что ушло бы в редактор.
//!
//! # Позиции
//!
//! Спаны компилятора байтовые, позиции LSP - в кодовых единицах, и
//! единица - предмет договорённости ([`position`]). Умолчание протокола -
//! UTF-16, и оно работает без всяких `general.positionEncodings` у клиента.

use std::collections::HashMap;

use adamas_core::source::SourceFile;
use lsp_server::{Connection, ErrorCode, Message, Notification, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{GotoDefinition, HoverRequest, Request as _};
use lsp_types::{
    DiagnosticRelatedInformation, DiagnosticSeverity, GotoDefinitionResponse, Hover, HoverContents,
    HoverProviderCapability, InitializeParams, InitializeResult, Location, MarkupContent,
    MarkupKind, OneOf, Position, PositionEncodingKind, PublishDiagnosticsParams,
    ServerCapabilities, ServerInfo, TextDocumentPositionParams, TextDocumentSyncCapability,
    TextDocumentSyncKind, Uri,
};

pub mod position;

/// Типы протокола. Ре-экспорт, чтобы у тех, кто зовёт [`diagnostics`], не
/// заводилась вторая запись версии `lsp-types` в своём манифесте.
pub use lsp_types;
pub use position::Encoding;

/// Имя, под которым диагностика показывается в редакторе.
const SOURCE: &str = "adamas";

/// Поднимает сервер на stdin/stdout и ведёт его до `shutdown`/`exit`.
///
/// # Errors
///
/// Обрыв канала, неразбираемые параметры `initialize`, отказ потоков ввода.
pub fn run() -> anyhow::Result<()> {
    let (connection, threads) = Connection::stdio();
    let served = handshake(&connection).and_then(|encoding| serve(&connection, encoding));
    // Соединение закрывается **до** ожидания потоков: поток записи живёт,
    // пока жив отправитель, и `join` при живом соединении не вернётся никогда.
    // Измерено: девять прогонов протокола висли на `wait` ровно здесь.
    drop(connection);
    threads.join()?;
    served
}

/// Рукопожатие: читает `initialize`, договаривается о кодировке, отвечает
/// возможностями.
fn handshake(connection: &Connection) -> anyhow::Result<Encoding> {
    let (id, params) = connection.initialize_start()?;
    let params: InitializeParams = serde_json::from_value(params)?;
    let encoding = negotiate(
        params
            .capabilities
            .general
            .and_then(|general| general.position_encodings)
            .as_deref(),
    );
    let result = InitializeResult {
        capabilities: capabilities(encoding),
        server_info: Some(ServerInfo {
            name: env!("CARGO_PKG_NAME").to_owned(),
            version: Some(env!("CARGO_PKG_VERSION").to_owned()),
        }),
    };
    connection.initialize_finish(id, serde_json::to_value(result)?)?;
    Ok(encoding)
}

/// Кодировка позиций по списку, объявленному клиентом.
///
/// Берётся **первая поддержанная в порядке клиента**, а не удобная серверу.
/// Порядок в списке - предпочтение клиента, и уважить его дешевле, чем
/// заставлять его пересчитывать: у нас перевод стоит один проход по строке в
/// любую сторону, у клиента он может стоить перекодирования буфера.
///
/// Списка нет или в нём нет ничего знакомого - UTF-16: умолчание протокола,
/// обязательное к поддержке обеими сторонами.
#[must_use]
pub fn negotiate(offered: Option<&[PositionEncodingKind]>) -> Encoding {
    offered
        .unwrap_or_default()
        .iter()
        .find_map(Encoding::of)
        .unwrap_or(Encoding::Utf16)
}

/// Что сервер умеет.
#[must_use]
pub fn capabilities(encoding: Encoding) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(encoding.kind()),
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        ..ServerCapabilities::default()
    }
}

/// Тип имени под курсором (§7.2, первая из названных там возможностей).
///
/// Текст ответа собирает [`adamas_elab::cursor::shown`] - та же функция, что
/// печатает `adamas check --type`. Второй записи типа нет, и это проверяется
/// прогоном: `crates/adamas-cli/tests/hover.rs` запускает драйвер процессом.
///
/// `None` - курсор не на имени либо типа у имени сегодня нет (локальное
/// связывание). Пустую подсказку слать нельзя: редактор нарисует пустое окно.
#[must_use]
pub fn hover(file: &SourceFile, position: Position, encoding: Encoding) -> Option<Hover> {
    let offset = position::offset(file, position, encoding)?;
    let analysis = adamas_elab::analyze(file.text());
    let module = analysis.module.as_ref()?;
    let found = adamas_elab::cursor::at(file.text(), module, offset)?;
    let value = adamas_elab::cursor::shown(analysis.signature.as_ref()?, &found)?;
    Some(Hover {
        // Простым текстом, а не разметкой: подсказка есть одна строка
        // `имя : тип`, и разметка в ней ничего не размечает. Ограждение кодом
        // потребовало бы договариваться о `contentFormat` с клиентом.
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::PlainText,
            value,
        }),
        range: Some(position::range(file, found.span, encoding)),
    })
}

/// Где объявлено имя под курсором - внутри этого же файла.
///
/// Ищется по **дереву**, а не по [`adamas_core::sig::Signature::origin`]:
/// таблица позиций заведена под DWARF и знает только определения с клаузами
/// (1230 имён из 3436 на корпусе), а дерево знает каждое объявление и живёт с
/// момента, когда текст разобрался. Отсюда же второе: переход работает на
/// буфере, который проверку типов не проходит.
///
/// Многофайловых проектов сегодня нет (§7.3, следующая волна), поэтому ответ
/// всегда указывает в тот же документ.
#[must_use]
pub fn definition(
    uri: &Uri,
    file: &SourceFile,
    position: Position,
    encoding: Encoding,
) -> Option<Location> {
    let offset = position::offset(file, position, encoding)?;
    let module = adamas_elab::analyze(file.text()).module?;
    let found = adamas_elab::cursor::at(file.text(), &module, offset)?;
    let span = found
        .binder
        .or_else(|| adamas_elab::cursor::declaration(&module, &found.text, &found.within))?;
    Some(Location {
        uri: uri.clone(),
        range: position::range(file, span, encoding),
    })
}

/// Диагностика файла в виде протокола.
///
/// Публичная, потому что это **та же** функция, которую зовёт цикл сервера:
/// проверять по ней и проверять сервер - одно и то же, и второго пути к
/// сообщению нет.
#[must_use]
pub fn diagnostics(uri: &Uri, file: &SourceFile, encoding: Encoding) -> Vec<lsp_types::Diagnostic> {
    adamas_elab::analyze(file.text())
        .diagnostics
        .iter()
        .map(|found| translate(uri, file, found, encoding))
        .collect()
}

/// Диагностика компилятора в диагностику протокола.
fn translate(
    uri: &Uri,
    file: &SourceFile,
    found: &adamas_elab::Diagnostic,
    encoding: Encoding,
) -> lsp_types::Diagnostic {
    let related: Vec<_> = found
        .related
        .iter()
        .map(|related| DiagnosticRelatedInformation {
            location: Location {
                uri: uri.clone(),
                range: position::range(file, related.span, encoding),
            },
            message: related.message.clone(),
        })
        .collect();
    lsp_types::Diagnostic {
        range: position::range(file, found.span, encoding),
        severity: Some(match found.severity {
            adamas_elab::Severity::Error => DiagnosticSeverity::ERROR,
            adamas_elab::Severity::Warning => DiagnosticSeverity::WARNING,
        }),
        source: Some(SOURCE.to_owned()),
        message: found.message(),
        related_information: (!related.is_empty()).then_some(related),
        ..lsp_types::Diagnostic::default()
    }
}

/// Главный цикл: уведомления меняют буфер и вызывают проверку, запросы пока
/// только закрывают сервер.
fn serve(connection: &Connection, encoding: Encoding) -> anyhow::Result<()> {
    // Ключ - текст URI, а не сам `Uri`: в `lsp-types` он несёт `Cell` с
    // разбором, то есть внутреннюю изменяемость, и ключом хеш-таблицы быть не
    // должен.
    let mut documents: HashMap<String, String> = HashMap::new();
    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    return Ok(());
                }
                connection
                    .sender
                    .send(Message::Response(answer(encoding, &documents, request)))?;
            }
            Message::Notification(note) => {
                // Уведомление, которое не разобралось, сервер не роняет:
                // упавший сервер уносит с собой подчёркивания во всех
                // открытых файлах, а причина - один кривой кадр. Обрыв канала
                // при этом всё равно закончит цикл: получатель закроется.
                if let Err(error) = handle(connection, encoding, &mut documents, &note) {
                    eprintln!(
                        "adamas-lsp: уведомление `{}` не обработано: {error}",
                        note.method
                    );
                }
            }
            // Ответов сервер не ждёт: запросов к клиенту он не шлёт.
            Message::Response(_) => {}
        }
    }
    Ok(())
}

/// Ответ на один запрос.
///
/// Запрос, которого нет среди объявленных возможностей, получает отказ, а не
/// молчание: молчание вешает клиента. Кривые параметры - тот же отказ по той
/// же причине, что кривое уведомление не роняет сервер.
fn answer(
    encoding: Encoding,
    documents: &HashMap<String, String>,
    request: lsp_server::Request,
) -> Response {
    let refuse = |message: String| {
        Response::new_err(
            request.id.clone(),
            ErrorCode::MethodNotFound as i32,
            message,
        )
    };
    let asked: Option<TextDocumentPositionParams> = match request.method.as_str() {
        HoverRequest::METHOD | GotoDefinition::METHOD => {
            match serde_json::from_value(request.params.clone()) {
                Ok(params) => Some(params),
                Err(error) => return refuse(format!("параметры не разобраны: {error}")),
            }
        }
        _ => None,
    };
    let Some(asked) = asked else {
        return refuse(format!("метод `{}` сервером не поддержан", request.method));
    };
    let uri = asked.text_document.uri;
    let Some(text) = documents.get(uri.as_str()) else {
        // Буфер не открыт: ответ «нечего показать», а не отказ - файл могли
        // закрыть, пока запрос летел.
        return Response::new_ok(request.id, serde_json::Value::Null);
    };
    let file = SourceFile::new(uri.as_str(), text.as_str());
    if request.method == HoverRequest::METHOD {
        Response::new_ok(request.id, hover(&file, asked.position, encoding))
    } else {
        Response::new_ok(
            request.id,
            definition(&uri, &file, asked.position, encoding).map(GotoDefinitionResponse::Scalar),
        )
    }
}

/// Одно уведомление.
fn handle(
    connection: &Connection,
    encoding: Encoding,
    documents: &mut HashMap<String, String>,
    note: &Notification,
) -> anyhow::Result<()> {
    match note.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: lsp_types::DidOpenTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            let document = params.text_document;
            documents.insert(document.uri.as_str().to_owned(), document.text);
            publish(
                connection,
                encoding,
                documents,
                &document.uri,
                Some(document.version),
            )?;
        }
        DidChangeTextDocument::METHOD => {
            let params: lsp_types::DidChangeTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            // Синхронизация полная, поэтому правка ровно одна и она - весь
            // текст. Пустой список правок оставляет буфер как был.
            if let Some(change) = params.content_changes.into_iter().next_back() {
                documents.insert(params.text_document.uri.as_str().to_owned(), change.text);
            }
            publish(
                connection,
                encoding,
                documents,
                &params.text_document.uri,
                Some(params.text_document.version),
            )?;
        }
        DidCloseTextDocument::METHOD => {
            let params: lsp_types::DidCloseTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            documents.remove(params.text_document.uri.as_str());
            // Закрытый файл оставил бы за собой подчёркивания в списке
            // проблем: очищает их пустой список, а не отсутствие сообщения.
            send(
                connection,
                &PublishDiagnosticsParams {
                    uri: params.text_document.uri,
                    diagnostics: Vec::new(),
                    version: None,
                },
            )?;
        }
        _ => {}
    }
    Ok(())
}

/// Проверяет буфер и шлёт его диагностику.
fn publish(
    connection: &Connection,
    encoding: Encoding,
    documents: &HashMap<String, String>,
    uri: &Uri,
    version: Option<i32>,
) -> anyhow::Result<()> {
    let Some(text) = documents.get(uri.as_str()) else {
        return Ok(());
    };
    let file = SourceFile::new(uri.as_str(), text.as_str());
    send(
        connection,
        &PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: diagnostics(uri, &file, encoding),
            version,
        },
    )
}

fn send(connection: &Connection, params: &PublishDiagnosticsParams) -> anyhow::Result<()> {
    connection
        .sender
        .send(Message::Notification(Notification::new(
            PublishDiagnostics::METHOD.to_owned(),
            params,
        )))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Encoding, negotiate};
    use lsp_types::PositionEncodingKind;

    #[test]
    fn utf16_is_the_default_without_a_capability() {
        assert_eq!(negotiate(None), Encoding::Utf16);
        assert_eq!(negotiate(Some(&[])), Encoding::Utf16);
    }

    #[test]
    fn an_unknown_encoding_falls_back_to_utf16() {
        let offered = [PositionEncodingKind::new("utf-7")];
        assert_eq!(negotiate(Some(&offered)), Encoding::Utf16);
    }

    #[test]
    fn the_client_order_decides() {
        let offered = [
            PositionEncodingKind::new("utf-7"),
            PositionEncodingKind::UTF8,
            PositionEncodingKind::UTF16,
        ];
        assert_eq!(negotiate(Some(&offered)), Encoding::Utf8);
        let offered = [PositionEncodingKind::UTF32, PositionEncodingKind::UTF8];
        assert_eq!(negotiate(Some(&offered)), Encoding::Utf32);
    }
}

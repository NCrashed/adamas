//! LSP-сервер Adamas (§7.2, §9 Фаза 9).
//!
//! # Что умеет
//!
//! `initialize`, `textDocument/didOpen`, `didChange`, `didClose` и
//! `textDocument/publishDiagnostics` - те же отказы и предупреждения, что
//! печатает `adamas check`, на тех же местах. Сверх того три возможности:
//! `textDocument/hover` — тип имени под курсором, первая из названных §7.2;
//! `textDocument/definition` внутри файла; `semanticTokens/full` — подсветка
//! от настоящего разбора, без второй грамматики ([`tokens`]).
//!
//! # Проект, а не файл
//!
//! Проверяется **программа**: буфер берётся входным файлом, его `import`'ы
//! разрешаются [`adamas_elab::program::analyze`], а тексты подключённых модулей
//! даёт [`project::Buffers`] - открытый буфер главнее диска. Отсюда и связь
//! между файлами: правка одного буфера перепроверяет всякий открытый буфер,
//! который его подключил. Кого подключил - видно из прошлого прохода
//! ([`Document::depends`]), нового обхода за этим не делается.
//!
//! # Проход целиком, без инкрементального ядра
//!
//! §7.2 называет Salsa-подход, и на горизонте больших проектов он остаётся
//! верным. Сегодня его не покупают, и обоснование - замер **на проекте**, а не
//! на файле (`docs/measurements/project-recheck/`). Круг «правка ->
//! диагностика» на `tests/golden/project` - 10 файлов, 328 строк, - release,
//! пол десяти кругов:
//!
//! | что правится | открыто буферов | круг |
//! |---|---|---|
//! | входной файл | 2 | **15,6 мс** |
//! | `Std/Base` (его подключают все) | 2 | 15,8 мс |
//! | `Std/Base` | 10 | 40,7 мс |
//!
//! Цена идёт с **кода**, а не с файлов: та же библиотека в двух файлах и в
//! десяти перепроверяется за одно и то же время с точностью до разброса.
//! Сто миллисекунд бюджета интерактивности набираются к ~2350 строкам проекта,
//! а самая большая программа языка сегодня - 944 строки. Кэш готовых сигнатур
//! за такие деньги не берут.
//!
//! Множитель у правки библиотечного модуля есть и назван: перепроверяется
//! каждый открытый буфер, который его подключил. При десяти окнах он даёт 2,6
//! прохода вместо одного - то есть в бюджет укладывается и он.
//!
//! Отсюда же `TextDocumentSyncKind::FULL`: клиент шлёт текст целиком, сервер
//! не ведёт инкрементальных правок буфера. Протокол это разрешает, а второй
//! путь применения правок был бы вторым местом, где текст может разойтись с
//! тем, что видит человек.
//!
//! Проход при этом **один на правку**, а не один на запрос: буфер хранит
//! дерево последней проверки, и подсветка берёт готовое. Считать заново
//! стоило бы 45,8 мс там, где покраска стоит 0,7.
//!
//! # Текст сообщения берётся у драйвера
//!
//! Сообщение собирает [`adamas_elab::program::analyze`] - тот же вызов, что
//! делает `adamas check`. Свидетель совпадения -
//! `crates/adamas-cli/tests/lsp.rs`: он запускает драйвер процессом на всём
//! корпусе отказов и собирает его вывод обратно из того, что ушло бы в
//! редактор.
//!
//! # Позиции
//!
//! Спаны компилятора байтовые, позиции LSP - в кодовых единицах, и
//! единица - предмет договорённости ([`position`]). Умолчание протокола -
//! UTF-16, и оно работает без всяких `general.positionEncodings` у клиента.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::str::FromStr as _;

use adamas_core::source::SourceFile;
use adamas_elab::program::{Program, Sources};
use lsp_server::{Connection, ErrorCode, Message, Notification, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{GotoDefinition, HoverRequest, Request as _, SemanticTokensFullRequest};
use lsp_types::{
    DiagnosticRelatedInformation, DiagnosticSeverity, GotoDefinitionResponse, Hover, HoverContents,
    HoverProviderCapability, InitializeParams, InitializeResult, Location, MarkupContent,
    MarkupKind, OneOf, Position, PositionEncodingKind, PublishDiagnosticsParams, SemanticTokens,
    SemanticTokensFullOptions, SemanticTokensOptions, SemanticTokensParams,
    SemanticTokensServerCapabilities, ServerCapabilities, ServerInfo, TextDocumentPositionParams,
    TextDocumentSyncCapability, TextDocumentSyncKind, Uri,
};

pub mod position;
pub mod project;
pub mod tokens;

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
    let served =
        handshake(&connection).and_then(|(encoding, roots)| serve(&connection, encoding, &roots));
    // Соединение закрывается **до** ожидания потоков: поток записи живёт,
    // пока жив отправитель, и `join` при живом соединении не вернётся никогда.
    // Измерено: девять прогонов протокола висли на `wait` ровно здесь.
    drop(connection);
    threads.join()?;
    served
}

/// Рукопожатие: читает `initialize`, договаривается о кодировке и корнях,
/// отвечает возможностями.
fn handshake(connection: &Connection) -> anyhow::Result<(Encoding, Vec<PathBuf>)> {
    let (id, params) = connection.initialize_start()?;
    let params: InitializeParams = serde_json::from_value(params)?;
    let roots = workspace(&params);
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
    Ok((encoding, roots))
}

/// Корни проекта, названные клиентом.
///
/// Нужны затем, что путь модуля пишется **от корня проекта**: `import Std.Base`
/// внутри `Std/Arith.adamas` указывает на `<корень>/Std/Base.adamas`, а не на
/// `<каталог буфера>/Std/Base.adamas`. Драйверу это не мешает - он берёт
/// корнем каталог входного файла, и входной файл лежит в корне, - а редактор
/// открывает **любой** файл проекта, в том числе лежащий глубже.
///
/// Корня нет - корнем становится каталог самого буфера: то же правило, что у
/// драйвера. Манифест (§7.3) заменит и то и другое собой.
fn workspace(params: &InitializeParams) -> Vec<PathBuf> {
    let folders = params
        .workspace_folders
        .iter()
        .flatten()
        .filter_map(|folder| project::path_of(&folder.uri));
    // `rootUri` спецификация объявила устаревшим в пользу `workspaceFolders`,
    // но шлют его до сих пор оба наших клиента, и читать его дешевле, чем
    // объяснять человеку, почему модуль не нашёлся.
    #[allow(deprecated, reason = "клиенты шлют `rootUri` и в 2026 году")]
    let legacy = params.root_uri.as_ref().and_then(project::path_of);
    folders.chain(legacy).collect()
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
        // Подсветка приходит от разбора, а не от второй грамматики
        // ([`tokens`]). Только `full`: по готовому дереву капстоун в 944
        // строки красится за 0,7 мс, и ни диапазон, ни дельта за такие деньги
        // не покупаются - у обоих своя арифметика, то есть своё место
        // разойтись.
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                legend: tokens::legend(),
                full: Some(SemanticTokensFullOptions::Bool(true)),
                range: Some(false),
                work_done_progress_options: lsp_types::WorkDoneProgressOptions::default(),
            },
        )),
        ..ServerCapabilities::default()
    }
}

/// Тип имени под курсором (§7.2, первая из названных там возможностей).
///
/// Текст ответа собирает [`adamas_elab::cursor::shown`] - та же функция, что
/// печатает `adamas check --type`. Второй записи типа нет, и это проверяется
/// прогоном: `crates/adamas-cli/tests/hover.rs` запускает драйвер процессом.
///
/// Проход идёт по **программе**: без разрешения импортов имя, пришедшее из
/// другого файла, сигнатуре неизвестно, и подсказка над ним молчала бы там, где
/// терминал печатает тип. Волна 2 Фазы 9 завела этим 137-ю фикстуру обратно в
/// корпусную сверку - `eval/prelude.adamas` выпадала из неё целиком.
///
/// `None` - курсор не на имени либо типа у имени сегодня нет (локальное
/// связывание). Пустую подсказку слать нельзя: редактор нарисует пустое окно.
#[must_use]
pub fn hover(
    file: &SourceFile,
    position: Position,
    encoding: Encoding,
    sources: &dyn Sources,
) -> Option<Hover> {
    let offset = position::offset(file, position, encoding)?;
    let text = file.text().to_owned();
    let program = adamas_elab::program::analyze(SourceFile::new(file.name(), text), sources);
    let module = program.units.first()?.module.as_ref()?;
    let found = adamas_elab::cursor::at(file.text(), module, offset)?;
    let value = adamas_elab::cursor::shown(program.signature.as_ref()?, &found)?;
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
/// Ответ указывает в **тот же** документ: имя, пришедшее из другого файла,
/// перехода сегодня не даёт. Проход поэтому только разбор - сигнатура здесь не
/// нужна, а стоила бы проверки типов всей программы.
#[must_use]
pub fn definition(
    uri: &Uri,
    file: &SourceFile,
    position: Position,
    encoding: Encoding,
) -> Option<Location> {
    let offset = position::offset(file, position, encoding)?;
    let module = adamas_parser::parse(file.text()).ok()?;
    let found = adamas_elab::cursor::at(file.text(), &module, offset)?;
    let span = found
        .binder
        .or_else(|| adamas_elab::cursor::declaration(&module, &found.text, &found.within))?;
    Some(Location {
        uri: uri.clone(),
        range: position::range(file, span, encoding),
    })
}

/// Диагностика файла в виде протокола - та, что относится к **нему самому**.
///
/// Публичная, потому что это **тот же** путь, каким идёт цикл сервера:
/// проверять по ней и проверять сервер - одно и то же, и второго пути к
/// сообщению нет.
///
/// Отказ, случившийся внутри подключённого модуля, сюда не попадает: его спан
/// живёт в чужом тексте, и нарисованный по этому файлу он подчеркнул бы
/// случайную строку. Сервер шлёт его под URI того файла ([`mine`] и рядом).
#[must_use]
pub fn diagnostics(
    uri: &Uri,
    file: &SourceFile,
    encoding: Encoding,
    sources: &dyn Sources,
) -> Vec<lsp_types::Diagnostic> {
    let text = file.text().to_owned();
    let program = adamas_elab::program::analyze(SourceFile::new(file.name(), text), sources);
    mine(uri, file, &program, encoding)
}

/// Диагностика входного файла по уже сделанному проходу.
///
/// Проход отделён от перевода в протокол ровно затем, чтобы сервер делал его
/// **один раз** на правку: подчёркивание и подсветка берутся из одной
/// [`Program`]. Порознь они стоили бы двух проверок типов.
#[must_use]
fn mine(
    uri: &Uri,
    file: &SourceFile,
    program: &Program,
    encoding: Encoding,
) -> Vec<lsp_types::Diagnostic> {
    program
        .diagnostics
        .iter()
        .filter(|located| located.unit == 0)
        .map(|located| translate(uri, file, &located.diagnostic, encoding))
        .collect()
}

/// Диагностика **подключённых** файлов, разложенная по их URI.
///
/// Файл, открытый в редакторе, сюда не попадает: у него есть свой проход, и он
/// же владеет своими подчёркиваниями. Иначе два прохода писали бы в один URI по
/// очереди, и подчёркивание мигало бы от того, какой из них был последним.
fn elsewhere(
    program: &Program,
    open: &HashMap<String, Document>,
    encoding: Encoding,
) -> BTreeMap<String, (Uri, Vec<lsp_types::Diagnostic>)> {
    let mut out: BTreeMap<String, (Uri, Vec<lsp_types::Diagnostic>)> = BTreeMap::new();
    for located in &program.diagnostics {
        if located.unit == 0 {
            continue;
        }
        let Some(unit) = program.units.get(located.unit) else {
            continue;
        };
        let file = Path::new(unit.file.name());
        if open.values().any(|it| it.path.as_deref() == Some(file)) {
            continue;
        }
        let Some(target) = project::uri_of(file) else {
            continue;
        };
        let found = translate(&target, &unit.file, &located.diagnostic, encoding);
        out.entry(target.as_str().to_owned())
            .or_insert_with(|| (target, Vec::new()))
            .1
            .push(found);
    }
    out
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

/// Открытый буфер: текст и то, что из него вышло на последней проверке.
///
/// Дерево хранится, потому что за правку его строят **один раз**: проверка
/// идёт на уведомлении, а запрос подсветки приходит следом и берёт готовое.
/// Иначе тот же капстоун проверялся бы дважды - 46 мс на подчёркивание и ещё
/// 46 на цвет, - при том, что сама покраска стоит 0,7 мс.
#[derive(Debug, Default)]
struct Document {
    /// Текст, как его прислал клиент.
    text: String,
    /// Файл, которым буфер лежит на диске. `None` - URI не про файл, и
    /// подключать такой буфер неоткуда.
    path: Option<PathBuf>,
    /// Дерево последней проверки. `None` - текст не разобрался.
    module: Option<adamas_parser::ast::Module>,
    /// Файлы, которые подтянул последний проход, - граф зависимостей, как его
    /// увидел компилятор. Правка любого из них меняет диагностику **этого**
    /// буфера, и отсюда сервер знает, кого перепроверять.
    ///
    /// Второго обхода за этим не делается: рёбра лежат в [`Program::units`],
    /// то есть в том же ответе, из которого берётся диагностика.
    depends: Vec<PathBuf>,
    /// URI, под которыми прошлый проход этого буфера опубликовал диагностику
    /// **чужого** файла. Хранятся, чтобы погасить их, когда отказ уйдёт:
    /// подчёркивание в файле, которого никто не открывал, само не исчезнет.
    published: Vec<String>,
}

impl Document {
    /// Буфер с этим текстом под этим URI.
    fn of(uri: &Uri, text: String) -> Self {
        Self {
            text,
            path: project::path_of(uri),
            module: None,
            depends: Vec::new(),
            published: Vec::new(),
        }
    }

    /// Новый текст в тот же буфер.
    ///
    /// Именно правка, а не замена: [`Self::published`] переживает её нарочно -
    /// это список чужих файлов, в которых прошлый проход поставил
    /// подчёркивание, и потеряв его, сервер уже не погасит их никогда.
    fn retext(&mut self, text: String) {
        self.text = text;
        self.module = None;
    }
}

/// Главный цикл: уведомления меняют буфер и вызывают проверку, запросы пока
/// только закрывают сервер.
fn serve(connection: &Connection, encoding: Encoding, roots: &[PathBuf]) -> anyhow::Result<()> {
    // Ключ - текст URI, а не сам `Uri`: в `lsp-types` он несёт `Cell` с
    // разбором, то есть внутреннюю изменяемость, и ключом хеш-таблицы быть не
    // должен.
    let mut documents: HashMap<String, Document> = HashMap::new();
    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    return Ok(());
                }
                // Подсветка идёт своим путём: спрашивают её не о позиции, а о
                // файле целиком, и берёт она готовое дерево. Всё прочее - в
                // [`answer`], и он же отклоняет незнакомый метод: возможности
                // объявлены в `initialize`, а молчание вешает клиента.
                let reply = if request.method == SemanticTokensFullRequest::METHOD {
                    highlight(encoding, &documents, request.id.clone(), &request.params)
                } else {
                    answer(encoding, roots, &documents, request)
                };
                connection.sender.send(Message::Response(reply))?;
            }
            Message::Notification(note) => {
                // Уведомление, которое не разобралось, сервер не роняет:
                // упавший сервер уносит с собой подчёркивания во всех
                // открытых файлах, а причина - один кривой кадр. Обрыв канала
                // при этом всё равно закончит цикл: получатель закроется.
                if let Err(error) = handle(connection, encoding, roots, &mut documents, &note) {
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
    roots: &[PathBuf],
    documents: &HashMap<String, Document>,
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
    let Some(document) = documents.get(uri.as_str()) else {
        // Буфер не открыт: ответ «нечего показать», а не отказ - файл могли
        // закрыть, пока запрос летел.
        return Response::new_ok(request.id, serde_json::Value::Null);
    };
    let file = SourceFile::new(uri.as_str(), document.text.as_str());
    if request.method == HoverRequest::METHOD {
        let sources = opened(document, documents, roots);
        Response::new_ok(request.id, hover(&file, asked.position, encoding, &sources))
    } else {
        Response::new_ok(
            request.id,
            definition(&uri, &file, asked.position, encoding).map(GotoDefinitionResponse::Scalar),
        )
    }
}

/// Ответ на `textDocument/semanticTokens/full`.
///
/// Буфер неизвестен - ответ пустой, а не отказ: клиент вправе спросить
/// подсветку у файла, уведомления о котором сервер ещё не получил, и отказ на
/// этом рисовался бы человеку ошибкой там, где её нет.
fn highlight(
    encoding: Encoding,
    documents: &HashMap<String, Document>,
    id: lsp_server::RequestId,
    params: &serde_json::Value,
) -> Response {
    let params: SemanticTokensParams = match serde_json::from_value(params.clone()) {
        Ok(params) => params,
        Err(error) => {
            return Response::new_err(id, ErrorCode::InvalidParams as i32, error.to_string());
        }
    };
    let uri = params.text_document.uri;
    let data = documents
        .get(uri.as_str())
        .map(|document| {
            let file = SourceFile::new(uri.as_str(), document.text.as_str());
            tokens::tokens(&file, document.module.as_ref(), encoding)
        })
        .unwrap_or_default();
    Response::new_ok(
        id,
        SemanticTokens {
            result_id: None,
            data,
        },
    )
}

/// Одно уведомление.
fn handle(
    connection: &Connection,
    encoding: Encoding,
    roots: &[PathBuf],
    documents: &mut HashMap<String, Document>,
    note: &Notification,
) -> anyhow::Result<()> {
    match note.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: lsp_types::DidOpenTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            let document = params.text_document;
            documents.insert(
                document.uri.as_str().to_owned(),
                Document::of(&document.uri, document.text),
            );
            refresh(
                connection,
                encoding,
                roots,
                documents,
                &document.uri,
                Some(document.version),
            )?;
        }
        DidChangeTextDocument::METHOD => {
            let params: lsp_types::DidChangeTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            let uri = params.text_document.uri;
            // Синхронизация полная, поэтому правка ровно одна и она - весь
            // текст. Пустой список правок оставляет буфер как был.
            if let Some(change) = params.content_changes.into_iter().next_back() {
                documents
                    .entry(uri.as_str().to_owned())
                    .and_modify(|document| document.retext(change.text.clone()))
                    .or_insert_with(|| Document::of(&uri, change.text));
            }
            refresh(
                connection,
                encoding,
                roots,
                documents,
                &uri,
                Some(params.text_document.version),
            )?;
        }
        DidCloseTextDocument::METHOD => {
            let params: lsp_types::DidCloseTextDocumentParams =
                serde_json::from_value(note.params.clone())?;
            let uri = params.text_document.uri;
            let gone = documents.remove(uri.as_str());
            // Закрытый файл оставил бы за собой подчёркивания в списке
            // проблем: очищает их пустой список, а не отсутствие сообщения.
            send(
                connection,
                &PublishDiagnosticsParams {
                    uri: uri.clone(),
                    diagnostics: Vec::new(),
                    version: None,
                },
            )?;
            for stale in gone.iter().flat_map(|it| &it.published) {
                if let Ok(target) = Uri::from_str(stale) {
                    clear(connection, &target)?;
                }
            }
            // Буфер закрыт - подключившие его теперь читают файл с диска, и
            // он мог разойтись с тем, что было в буфере.
            depending(documents, uri.as_str(), gone.and_then(|it| it.path))
                .into_iter()
                .try_for_each(|key| {
                    publish_one(connection, encoding, roots, documents, &key, None)
                })?;
        }
        _ => {}
    }
    Ok(())
}

/// Перепроверяет буфер и всех, кто его подключил.
///
/// Связь между файлами именно здесь: без второго прохода правка `Std/Base`
/// оставляла бы в зависящем буфере подчёркивание, снятое минуту назад, - или,
/// хуже, не ставила бы нового. Список зависящих известен из прошлых проходов
/// ([`Document::depends`]), а не из нового обхода.
fn refresh(
    connection: &Connection,
    encoding: Encoding,
    roots: &[PathBuf],
    documents: &mut HashMap<String, Document>,
    uri: &Uri,
    version: Option<i32>,
) -> anyhow::Result<()> {
    publish_one(
        connection,
        encoding,
        roots,
        documents,
        uri.as_str(),
        version,
    )?;
    let changed = documents.get(uri.as_str()).and_then(|it| it.path.clone());
    for key in depending(documents, uri.as_str(), changed) {
        // Версия у зависящего своя и не менялась: протокол разрешает её не
        // называть, а назвать чужую значило бы соврать клиенту.
        publish_one(connection, encoding, roots, documents, &key, None)?;
    }
    Ok(())
}

/// Открытые буферы, чей прошлый проход подтянул этот файл.
fn depending(
    documents: &HashMap<String, Document>,
    skip: &str,
    changed: Option<PathBuf>,
) -> Vec<String> {
    let Some(changed) = changed else {
        return Vec::new();
    };
    let mut found: Vec<String> = documents
        .iter()
        .filter(|(key, document)| key.as_str() != skip && document.depends.contains(&changed))
        .map(|(key, _)| key.clone())
        .collect();
    // Порядок буферов в хеш-таблице случаен, а порядок уведомлений виден
    // клиенту и прогону.
    found.sort();
    found
}

/// Тексты модулей для этого буфера: открытые буферы поверх диска.
///
/// Корень поиска - тот корень рабочего пространства, внутри которого лежит
/// буфер; самый **длинный** из подходящих, потому что вложенный проект
/// главнее объемлющего. Не назвал клиент ни одного - корнем становится каталог
/// буфера, как у драйвера.
fn opened<'a>(
    document: &Document,
    documents: &'a HashMap<String, Document>,
    roots: &[PathBuf],
) -> project::Buffers<'a> {
    let here = document.path.as_deref();
    let inside = here.and_then(|path| {
        roots
            .iter()
            .filter(|root| path.starts_with(root))
            .max_by_key(|root| root.as_os_str().len())
            .map(PathBuf::as_path)
    });
    let root = inside
        .or_else(|| here.and_then(Path::parent))
        .unwrap_or(Path::new("."));
    let open = documents
        .values()
        .filter_map(|it| Some((it.path.clone()?, it.text.as_str())))
        .collect();
    project::Buffers::new(root, open)
}

/// Проверяет один буфер, запоминает дерево с зависимостями и шлёт диагностику.
fn publish_one(
    connection: &Connection,
    encoding: Encoding,
    roots: &[PathBuf],
    documents: &mut HashMap<String, Document>,
    key: &str,
    version: Option<i32>,
) -> anyhow::Result<()> {
    let Ok(uri) = Uri::from_str(key) else {
        return Ok(());
    };
    let (program, found, foreign) = {
        let Some(document) = documents.get(key) else {
            return Ok(());
        };
        let file = SourceFile::new(key, document.text.as_str());
        let sources = opened(document, documents, roots);
        let program = adamas_elab::program::analyze(file, &sources);
        let file = SourceFile::new(key, document.text.as_str());
        let found = mine(&uri, &file, &program, encoding);
        let foreign = elsewhere(&program, documents, encoding);
        (program, found, foreign)
    };

    let depends: Vec<PathBuf> = program
        .units
        .iter()
        .skip(1)
        .map(|unit| PathBuf::from(unit.file.name()))
        .collect();
    let mut units = program.units;
    let module = units.first_mut().and_then(|unit| unit.module.take());
    let fresh: Vec<String> = foreign.keys().cloned().collect();

    let stale: Vec<String> = documents.get(key).map_or_else(Vec::new, |document| {
        document
            .published
            .iter()
            .filter(|it| !fresh.contains(it))
            .cloned()
            .collect()
    });
    if let Some(document) = documents.get_mut(key) {
        document.module = module;
        document.depends = depends;
        document.published = fresh;
    }

    for gone in &stale {
        if let Ok(target) = Uri::from_str(gone) {
            clear(connection, &target)?;
        }
    }
    for (target, diagnostics) in foreign.into_values() {
        send(
            connection,
            &PublishDiagnosticsParams {
                uri: target,
                diagnostics,
                version: None,
            },
        )?;
    }
    send(
        connection,
        &PublishDiagnosticsParams {
            uri,
            diagnostics: found,
            version,
        },
    )
}

/// Гасит подчёркивания в файле: пустой список, а не молчание.
fn clear(connection: &Connection, uri: &Uri) -> anyhow::Result<()> {
    send(
        connection,
        &PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: Vec::new(),
            version: None,
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

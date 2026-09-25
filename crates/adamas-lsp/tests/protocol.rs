//! Сервер гоняется по JSON-RPC - так, как его гоняет редактор.
//!
//! Проверяется **бинарь**, а не библиотека: между ними стоит рамка сообщений,
//! потоки stdin/stdout и рукопожатие, и всё это часть обещания «файл
//! открывается в редакторе». Клиент здесь свой, в сорок строк, и рамку он
//! читает сам - если каркас сервера однажды сменится, свидетель устоит.
//!
//! # Чего такой прогон **не** доказывает
//!
//! Что сервер ответил - ещё не что он ответил осмысленно. Поэтому ни одно
//! утверждение здесь не про наличие ответа: сверяются номер строки, номер
//! знака и текст, а числа записаны руками. Перевод позиций, ошибочный
//! одинаково в обе стороны, круговой проверке не виден - эти числа видят его.

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use serde_json::{Value, json};

/// Фикстура корпуса, на которой байт, знак и кодовая единица UTF-16 дают три
/// разных числа.
const FIXTURE: &str = "position-past-multibyte.adamas";

/// URI буфера. С диском не связан: текст сервер получает уведомлением.
const URI: &str = "file:///corpus/position-past-multibyte.adamas";

/// Строка отказа в фикстуре, 0-based.
const LINE: u64 = 19;

/// Первая строка сообщения - та же, что печатает терминал.
const HEADLINE: &str = "ожидалась функция, получено значение типа `Nat`";

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden")
}

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
mod client {
    use super::{BufRead, BufReader, Child, ChildStdin, ChildStdout, Command, Read, Stdio, Write};
    use super::{Value, json};

    /// Клиент LSP на пайпах к бинарю сервера.
    pub(crate) struct Client {
        child: Child,
        stdin: ChildStdin,
        stdout: BufReader<ChildStdout>,
        next: i64,
        /// Диагностика, прочитанная по пути к ответам на запросы, по URI.
        seen: super::BTreeMap<String, Value>,
        /// Запросы **сервера к клиенту**, прочитанные по тому же пути.
        ///
        /// Запрос у сервера один - `workspace/inlayHint/refresh`, - и виден он
        /// только так: ответа на него нет, а без записи здесь он утёк бы в
        /// цикл чтения молча.
        asked: Vec<String>,
    }

    impl Client {
        /// Поднимает сервер и делает рукопожатие.
        ///
        /// `encodings` - список из `general.positionEncodings`; `None` значит,
        /// что клиент возможности не объявил вовсе, и это умолчание протокола.
        pub(crate) fn start(encodings: Option<&[&str]>) -> (Self, Value) {
            Self::start_in(None, encodings)
        }

        /// То же, но клиент объявляет, что умеет перерисовывать подсказки.
        ///
        /// Возможность объявляется отдельным клиентом, а не всеми: сервер
        /// обязан молчать, когда её нет, и проверяется это тем же способом -
        /// прогоном без неё.
        pub(crate) fn start_refreshing(root: Option<&str>) -> Self {
            Self::spawn(root, None, true).0
        }

        /// То же, но клиент называет корень рабочего пространства.
        ///
        /// Корень нужен, когда буфер лежит **глубже** входного файла: путь
        /// модуля пишется от корня проекта, и `import Std.Base` внутри
        /// `Std/Arith.adamas` без корня искался бы в `Std/Std/`.
        pub(crate) fn start_in(root: Option<&str>, encodings: Option<&[&str]>) -> (Self, Value) {
            Self::spawn(root, encodings, false)
        }

        fn spawn(root: Option<&str>, encodings: Option<&[&str]>, refresh: bool) -> (Self, Value) {
            let mut child = Command::new(env!("CARGO_BIN_EXE_adamas-lsp"))
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::inherit())
                .spawn()
                .unwrap();
            let stdin = child.stdin.take().unwrap();
            let stdout = BufReader::new(child.stdout.take().unwrap());
            let mut client = Self {
                child,
                stdin,
                stdout,
                next: 0,
                seen: super::BTreeMap::new(),
                asked: Vec::new(),
            };
            let general = match encodings {
                Some(list) => json!({ "positionEncodings": list }),
                None => Value::Null,
            };
            let workspace = if refresh {
                json!({ "inlayHint": { "refreshSupport": true } })
            } else {
                Value::Null
            };
            let result = client.request(
                "initialize",
                &json!({
                    "processId": Value::Null,
                    "rootUri": root.map_or(Value::Null, |it| json!(it)),
                    "capabilities": { "general": general, "workspace": workspace },
                }),
            );
            client.notify("initialized", &json!({}));
            (client, result)
        }

        /// Запрос и его `result`.
        pub(crate) fn request(&mut self, method: &str, params: &Value) -> Value {
            let answer = self.raw_request(method, params);
            assert!(
                answer.get("error").is_none(),
                "сервер отказал на `{method}`: {answer}"
            );
            answer["result"].clone()
        }

        /// Запрос и ответ целиком - вместе с `error`, если сервер отказал.
        pub(crate) fn raw_request(&mut self, method: &str, params: &Value) -> Value {
            self.next += 1;
            let id = self.next;
            self.write(&json!({
                "jsonrpc": "2.0",
                "id": id,
                "method": method,
                "params": params,
            }));
            loop {
                let message = self.read();
                if message.get("id").and_then(Value::as_i64) == Some(id) {
                    return message;
                }
            }
        }

        /// Уведомление без ответа.
        pub(crate) fn notify(&mut self, method: &str, params: &Value) {
            self.write(&json!({
                "jsonrpc": "2.0",
                "method": method,
                "params": params,
            }));
        }

        /// Открывает буфер и ждёт его диагностику.
        pub(crate) fn open(&mut self, uri: &str, text: &str) -> Value {
            self.notify(
                "textDocument/didOpen",
                &json!({
                    "textDocument": {
                        "uri": uri,
                        "languageId": "adamas",
                        "version": 1,
                        "text": text,
                    }
                }),
            );
            self.diagnostics(uri)
        }

        /// Переписывает буфер целиком и ждёт его диагностику.
        pub(crate) fn change(&mut self, uri: &str, version: i64, text: &str) -> Value {
            self.edit(uri, version, text);
            self.diagnostics(uri)
        }

        /// Переписывает буфер целиком и **не** ждёт ничего: правка одного
        /// файла шлёт диагностику нескольких, и ждать её надо [`Self::settled`].
        pub(crate) fn edit(&mut self, uri: &str, version: i64, text: &str) {
            self.notify(
                "textDocument/didChange",
                &json!({
                    "textDocument": { "uri": uri, "version": version },
                    "contentChanges": [{ "text": text }],
                }),
            );
        }

        /// Подсказка над позицией.
        pub(crate) fn hover(&mut self, uri: &str, line: u64, character: u64) -> Value {
            self.request("textDocument/hover", &Self::at(uri, line, character))
        }

        /// Переход к определению с позиции.
        pub(crate) fn definition(&mut self, uri: &str, line: u64, character: u64) -> Value {
            self.request("textDocument/definition", &Self::at(uri, line, character))
        }

        /// Подсказки видимого куска буфера.
        pub(crate) fn inlay(&mut self, uri: &str, from: u64, upto: u64) -> Value {
            self.request(
                "textDocument/inlayHint",
                &json!({
                    "textDocument": { "uri": uri },
                    "range": {
                        "start": { "line": from, "character": 0 },
                        "end": { "line": upto, "character": 0 },
                    },
                }),
            )
        }

        /// Запросы сервера к клиенту, пришедшие **до сих пор**.
        pub(crate) fn asked(&mut self) -> Vec<String> {
            std::mem::take(&mut self.asked)
        }

        fn at(uri: &str, line: u64, character: u64) -> Value {
            json!({
                "textDocument": { "uri": uri },
                "position": { "line": line, "character": character },
            })
        }

        /// Вся диагностика, посланная сервером **до сих пор**, по URI.
        ///
        /// Сервер синхронен и однопоточен: всё, что он послал из-за
        /// уведомления, лежит в потоке раньше ответа на следующий запрос.
        /// Отсюда прогон, который **не виснет**: не пришедшая диагностика
        /// видна отсутствием ключа, а не молчанием потока. Ждать её в цикле
        /// значило бы получить вместо провала висящий тест - проверено
        /// мутантом, снимающим перепроверку зависящих.
        pub(crate) fn settled(&mut self) -> super::BTreeMap<String, Value> {
            let answer = self.raw_request(
                "textDocument/semanticTokens/full",
                &json!({ "textDocument": { "uri": "file:///settle.adamas" } }),
            );
            assert!(answer.get("error").is_none(), "{answer}");
            std::mem::take(&mut self.seen)
        }

        /// Ближайший `publishDiagnostics` для этого URI.
        pub(crate) fn diagnostics(&mut self, uri: &str) -> Value {
            loop {
                let message = self.read();
                if message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
                    && message["params"]["uri"] == json!(uri)
                {
                    return message["params"]["diagnostics"].clone();
                }
            }
        }

        /// Сколько резидентной памяти держит сам сервер, в килобайтах.
        ///
        /// Читается у **процесса сервера**, а не у процесса теста: буферы
        /// живут там, и мерить своё потребление значило бы мерить клиента.
        /// Поле `resident` из `/proc/<pid>/statm` - в страницах.
        pub(crate) fn resident(&self) -> u64 {
            let statm = std::fs::read_to_string(format!("/proc/{}/statm", self.child.id()))
                .expect("Linux: у процесса есть statm");
            let pages: u64 = statm
                .split_whitespace()
                .nth(1)
                .expect("второе поле statm - резидентные страницы")
                .parse()
                .expect("страницы - число");
            pages * 4
        }

        /// Закрывает сервер и ждёт его кода возврата.
        pub(crate) fn stop(mut self) {
            self.request("shutdown", &Value::Null);
            self.notify("exit", &Value::Null);
            let status = self.child.wait().unwrap();
            assert!(status.success(), "сервер вышел с {status}");
        }

        /// Рамка наружу.
        fn write(&mut self, message: &Value) {
            let body = serde_json::to_vec(message).unwrap();
            write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
            self.stdin.write_all(&body).unwrap();
            self.stdin.flush().unwrap();
        }

        /// Рамка внутрь: заголовки ASCII, тело - ровно столько байтов, сколько
        /// обещано. Считать тело знаками нельзя - `Content-Length` в байтах.
        fn read(&mut self) -> Value {
            let mut length = None;
            loop {
                let mut line = String::new();
                let read = self.stdout.read_line(&mut line).unwrap();
                assert!(read > 0, "сервер закрыл поток посреди сообщения");
                let trimmed = line.trim_end_matches(['\r', '\n']);
                if trimmed.is_empty() {
                    break;
                }
                if let Some(value) = trimmed.strip_prefix("Content-Length:") {
                    length = Some(value.trim().parse::<usize>().unwrap());
                }
            }
            let length = length.expect("в заголовке обязана быть длина");
            let mut body = vec![0u8; length];
            self.stdout.read_exact(&mut body).unwrap();
            let message: Value = serde_json::from_slice(&body).unwrap();
            // Диагностика запоминается **здесь**, а не там, где её ждут: одна
            // правка шлёт её сразу по нескольким файлам, и та, которой в этот
            // раз не ждали, иначе пропадала бы из виду.
            if message.get("method").and_then(Value::as_str)
                == Some("textDocument/publishDiagnostics")
            {
                let uri = message["params"]["uri"].as_str().unwrap_or_default();
                self.seen
                    .insert(uri.to_owned(), message["params"]["diagnostics"].clone());
            }
            // Запрос сервера к клиенту: есть и `method`, и `id`. Ответа на него
            // клиент здесь не шлёт - результата у `inlayHint/refresh` нет.
            if let (Some(method), Some(_)) = (
                message.get("method").and_then(Value::as_str),
                message.get("id"),
            ) {
                self.asked.push(method.to_owned());
            }
            message
        }
    }

    impl Drop for Client {
        fn drop(&mut self) {
            let _ = self.child.kill();
        }
    }
}

use client::Client;

#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn fixture(name: &str) -> String {
    std::fs::read_to_string(corpus().join("errors").join(name)).unwrap()
}

/// Рукопожатие: сервер называет кодировку и способ синхронизации.
#[test]
fn initialize_answers_with_capabilities() {
    let (client, result) = Client::start(None);
    assert_eq!(
        result["capabilities"]["positionEncoding"],
        json!("utf-16"),
        "умолчание протокола"
    );
    assert_eq!(
        result["capabilities"]["textDocumentSync"],
        json!(1),
        "1 - синхронизация целым текстом"
    );
    assert_eq!(result["capabilities"]["hoverProvider"], json!(true));
    assert_eq!(result["capabilities"]["definitionProvider"], json!(true));
    assert_eq!(result["serverInfo"]["name"], json!("adamas-lsp"));
    client.stop();
}

/// Диагностика приходит на `didOpen`, и стоит она там, где написано руками.
///
/// 19 - номер строки; 18 и 32 - границы подчёркивания в кодовых единицах
/// UTF-16. Байтами те же границы были бы 26 и 40, знаками - 17 и 31.
#[test]
fn a_diagnostic_lands_past_multibyte_text() {
    let (mut client, _) = Client::start(None);
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(
        diagnostics.as_array().map(Vec::len),
        Some(1),
        "{diagnostics}"
    );
    let found = &diagnostics[0];
    assert_eq!(
        found["range"]["start"],
        json!({ "line": LINE, "character": 18 })
    );
    assert_eq!(
        found["range"]["end"],
        json!({ "line": LINE, "character": 32 })
    );
    assert_eq!(found["severity"], json!(1), "1 - Error");
    assert_eq!(found["source"], json!("adamas"));
    assert_eq!(
        found["message"],
        json!(format!("{HEADLINE}\n  путь: тело `двойка`")),
        "текст - тот же, что печатает терминал, вместе с маршрутом"
    );
    client.stop();
}

/// Та же позиция в байтах, когда клиент попросил UTF-8.
#[test]
fn utf8_moves_the_column_to_bytes() {
    let (mut client, result) = Client::start(Some(&["utf-8", "utf-16"]));
    assert_eq!(result["capabilities"]["positionEncoding"], json!("utf-8"));
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(
        diagnostics[0]["range"],
        json!({
            "start": { "line": LINE, "character": 26 },
            "end": { "line": LINE, "character": 40 },
        })
    );
    client.stop();
}

/// И в знаках, когда UTF-32.
#[test]
fn utf32_moves_the_column_to_characters() {
    let (mut client, result) = Client::start(Some(&["utf-32"]));
    assert_eq!(result["capabilities"]["positionEncoding"], json!("utf-32"));
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(
        diagnostics[0]["range"],
        json!({
            "start": { "line": LINE, "character": 17 },
            "end": { "line": LINE, "character": 31 },
        })
    );
    client.stop();
}

/// Неизвестная кодировка - UTF-16: сервер не вправе взять то, чего клиент не
/// понимает.
#[test]
fn an_unknown_encoding_falls_back() {
    let (mut client, result) = Client::start(Some(&["utf-7"]));
    assert_eq!(result["capabilities"]["positionEncoding"], json!("utf-16"));
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(diagnostics[0]["range"]["start"]["character"], json!(18));
    client.stop();
}

/// Правка перепроверяет файл: ошибка уходит и возвращается.
#[test]
fn a_change_rechecks_the_buffer() {
    let broken = fixture(FIXTURE);
    let fixed = broken.replace("Succ Zero Zero", "Succ Zero");
    assert_ne!(broken, fixed, "правка обязана что-то менять");

    let (mut client, _) = Client::start(None);
    assert_eq!(client.open(URI, &broken).as_array().map(Vec::len), Some(1));

    let clean = client.change(URI, 2, &fixed);
    assert_eq!(
        clean,
        json!([]),
        "исправленный буфер обязан гасить подчёркивание"
    );

    let again = client.change(URI, 3, &broken);
    assert_eq!(again[0]["range"]["start"]["character"], json!(18));
    client.stop();
}

/// Отказ разбора - тоже диагностика, и позиция у него своя.
#[test]
fn a_parse_error_is_published_too() {
    let (mut client, _) = Client::start(None);
    let diagnostics = client.open(URI, "двойка = (\n");
    assert_eq!(
        diagnostics.as_array().map(Vec::len),
        Some(1),
        "{diagnostics}"
    );
    assert_eq!(diagnostics[0]["range"]["start"]["line"], json!(0));
    assert_eq!(diagnostics[0]["severity"], json!(1));
    client.stop();
}

/// Закрытый буфер гасит свои подчёркивания.
#[test]
fn closing_clears_the_diagnostics() {
    let (mut client, _) = Client::start(None);
    assert_eq!(
        client.open(URI, &fixture(FIXTURE)).as_array().map(Vec::len),
        Some(1)
    );
    client.notify(
        "textDocument/didClose",
        &json!({ "textDocument": { "uri": URI } }),
    );
    assert_eq!(client.diagnostics(URI), json!([]));
    client.stop();
}

/// Токены ответа в читаемом виде: `строка:знак+длина вид`.
///
/// Ответ - плоский список пятёрок с **дельтами**, и разворачивается он здесь
/// вручную: тем же кодом, каким собирается, проверять нечего.
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn unpack(legend: &Value, answer: &Value) -> Vec<String> {
    let data = answer["data"].as_array().expect("список пятёрок");
    assert_eq!(data.len() % 5, 0, "пятёрки не сошлись: {}", data.len());
    let names = legend["tokenTypes"].as_array().expect("легенда");
    let (mut line, mut start) = (0u64, 0u64);
    let mut out = Vec::new();
    for chunk in data.chunks_exact(5) {
        let numbers: Vec<u64> = chunk.iter().map(|it| it.as_u64().unwrap()).collect();
        line += numbers[0];
        start = if numbers[0] == 0 {
            start + numbers[1]
        } else {
            numbers[1]
        };
        let face = names[usize::try_from(numbers[3]).unwrap()]
            .as_str()
            .unwrap();
        out.push(format!("{line}:{start}+{} {face}", numbers[2]));
    }
    out
}

/// Сервер объявляет подсветку и называет свою легенду.
#[test]
fn initialize_announces_the_legend() {
    let (client, result) = Client::start(None);
    let provider = &result["capabilities"]["semanticTokensProvider"];
    assert_eq!(provider["full"], json!(true), "{provider}");
    assert_eq!(provider["range"], json!(false));
    let types = provider["legend"]["tokenTypes"]
        .as_array()
        .expect("легенда - список");
    for face in ["keyword", "comment", "type", "enumMember", "function"] {
        assert!(types.contains(&json!(face)), "{face} нет в {types:?}");
    }
    assert_eq!(
        provider["legend"]["tokenModifiers"],
        json!(["declaration"]),
        "признак объявления - бит 0"
    );
    client.stop();
}

/// Подсветка приходит от разбора, и разные конструкции получают разные виды.
///
/// Числа записаны руками. Дельты считаются **разностями** колонок, поэтому
/// многобайтовый текст между двумя токенами одной строки их и различает:
/// `{- 😀 -}` занимает 8 единиц UTF-16 при 10 байтах, и `Succ` за ним стоит на
/// 18-й единице при 26-м байте.
#[test]
fn semantic_tokens_come_from_the_parse() {
    let (mut client, result) = Client::start(None);
    let legend = result["capabilities"]["semanticTokensProvider"]["legend"].clone();
    client.open(URI, &fixture(FIXTURE));
    let answer = client.request(
        "textDocument/semanticTokens/full",
        &json!({ "textDocument": { "uri": URI } }),
    );
    let tokens = unpack(&legend, &answer);
    assert_eq!(
        tokens[tokens.len() - 6..],
        [
            format!("{LINE}:0+6 function"),
            format!("{LINE}:7+1 operator"),
            format!("{LINE}:9+8 comment"),
            format!("{LINE}:18+4 enumMember"),
            format!("{LINE}:23+4 enumMember"),
            format!("{LINE}:28+4 enumMember"),
        ],
        "последняя строка фикстуры"
    );
    // Различение, а не наличие: ответ из одних `variable` был бы ответом.
    let faces: std::collections::BTreeSet<&str> = tokens
        .iter()
        .map(|it| it.rsplit(' ').next().unwrap_or_default())
        .collect();
    assert!(
        faces.len() >= 5,
        "видов в ответе слишком мало: {faces:?} - подсветка одного цвета не подсветка"
    );
    client.stop();
}

/// Та же подсветка в байтах, когда клиент попросил UTF-8: колонка и длина
/// меряются одной единицей, и обе уезжают вместе.
#[test]
fn utf8_moves_the_token_columns() {
    let (mut client, result) = Client::start(Some(&["utf-8"]));
    let legend = result["capabilities"]["semanticTokensProvider"]["legend"].clone();
    client.open(URI, &fixture(FIXTURE));
    let answer = client.request(
        "textDocument/semanticTokens/full",
        &json!({ "textDocument": { "uri": URI } }),
    );
    let tokens = unpack(&legend, &answer);
    assert_eq!(
        tokens[tokens.len() - 6..],
        [
            format!("{LINE}:0+12 function"),
            format!("{LINE}:13+1 operator"),
            format!("{LINE}:15+10 comment"),
            format!("{LINE}:26+4 enumMember"),
            format!("{LINE}:31+4 enumMember"),
            format!("{LINE}:36+4 enumMember"),
        ]
    );
    client.stop();
}

/// Правка перекрашивает: сломанный текст отдаёт только слой лексики, и имена
/// возвращаются, когда текст снова разбирается.
///
/// Это же свидетель того, что сервер не отдаёт дерево прошлой правки: он его
/// хранит, чтобы не проверять файл дважды.
#[test]
fn a_change_repaints_the_buffer() {
    let (mut client, result) = Client::start(None);
    let legend = result["capabilities"]["semanticTokensProvider"]["legend"].clone();
    let whole = "data Nat where\n  Zero : Nat\n\nnil : Nat\nnil = Zero\n";
    let broken = "data Nat where\n  Zero : Nat\n\nnil : Nat\nnil = (Zero\n";

    client.open(URI, whole);
    let painted = unpack(
        &legend,
        &client.request(
            "textDocument/semanticTokens/full",
            &json!({ "textDocument": { "uri": URI } }),
        ),
    );
    assert_eq!(
        painted[painted.len() - 3..],
        ["4:0+3 function", "4:4+1 operator", "4:6+4 enumMember"]
    );

    client.change(URI, 2, broken);
    let bare = unpack(
        &legend,
        &client.request(
            "textDocument/semanticTokens/full",
            &json!({ "textDocument": { "uri": URI } }),
        ),
    );
    assert_eq!(
        bare,
        [
            "0:0+4 keyword",
            "0:9+5 keyword",
            "1:7+1 operator",
            "3:4+1 operator",
            "4:4+1 operator"
        ],
        "разбора нет - имён нет, а ключевые слова и знаки на месте"
    );

    client.change(URI, 3, whole);
    let again = unpack(
        &legend,
        &client.request(
            "textDocument/semanticTokens/full",
            &json!({ "textDocument": { "uri": URI } }),
        ),
    );
    assert_eq!(again, painted, "починенный текст красится как прежде");
    client.stop();
}

/// Подсветка буфера, о котором сервер не знает, пуста, а не отказ.
#[test]
fn tokens_of_an_unknown_buffer_are_empty() {
    let (mut client, _) = Client::start(None);
    let answer = client.request(
        "textDocument/semanticTokens/full",
        &json!({ "textDocument": { "uri": "file:///corpus/never-opened.adamas" } }),
    );
    assert_eq!(answer["data"], json!([]));
    client.stop();
}

/// Кривой URI - отказ с `InvalidParams`, а не молчание и не паника.
///
/// Врозь от [`a_malformed_request_is_refused`]: там негодны **параметры**
/// запроса и отказ приходит методом, здесь параметры разобраны, а негоден
/// адрес, и код отказа другой.
#[test]
fn a_malformed_uri_is_refused() {
    let (mut client, _) = Client::start(None);
    let answer = client.raw_request(
        "textDocument/semanticTokens/full",
        &json!({ "textDocument": { "uri": "не URI" } }),
    );
    assert_eq!(answer["error"]["code"], json!(-32602), "{answer}");
    client.stop();
}

/// Непонятый запрос получает отказ, а не молчание: молчание вешает клиента,
/// а объявлено сервером пока только то, что он умеет.
#[test]
fn an_unsupported_request_is_refused() {
    let (mut client, _) = Client::start(None);
    let answer = client.raw_request("textDocument/completion", &json!({}));
    assert_eq!(
        answer["error"]["code"],
        json!(-32601),
        "MethodNotFound: {answer}"
    );
    client.stop();
}

/// Запрос с негодными параметрами получает отказ, а не молчание и не падение.
#[test]
fn a_malformed_request_is_refused() {
    let (mut client, _) = Client::start(None);
    let answer = client.raw_request("textDocument/hover", &json!({ "position": 7 }));
    assert_eq!(answer["error"]["code"], json!(-32601), "{answer}");
    // Сервер жив: следующий запрос обслуживается.
    client.open(URI, &fixture(FIXTURE));
    assert_eq!(
        client.hover(URI, LINE, 18)["contents"]["value"],
        json!(SUCC)
    );
    client.stop();
}

/// Тип конструктора, как его печатает компилятор.
const SUCC: &str = "Succ : (1 _ : Nat) -> Nat";

/// Подсказка стоит **после** неASCII-текста на своей строке.
///
/// 18 - номер знака `Succ` в кодовых единицах UTF-16; байтами он 26, знаками
/// 17. Числа записаны руками: сервер, считающий колонку байтами, на этом
/// запросе покажет не `Succ`, а то, что стоит на 26-й единице, - и это `Zero`
/// ниже. Обе половины перевода проверяются здесь сразу: колонка запроса идёт
/// в смещение, а `range` ответа - обратно.
#[test]
fn a_hover_lands_past_multibyte_text() {
    let (mut client, _) = Client::start(None);
    client.open(URI, &fixture(FIXTURE));

    let hover = client.hover(URI, LINE, 18);
    assert_eq!(hover["contents"]["kind"], json!("plaintext"));
    assert_eq!(hover["contents"]["value"], json!(SUCC));
    assert_eq!(
        hover["range"],
        json!({
            "start": { "line": LINE, "character": 18 },
            "end": { "line": LINE, "character": 22 },
        }),
        "подсвечивается само имя"
    );

    // 26 - та самая колонка, которую байтовый счёт принял бы за `Succ`.
    assert_eq!(
        client.hover(URI, LINE, 26)["contents"]["value"],
        json!("Zero : Nat"),
        "на 26-й единице UTF-16 стоит `Zero`, а байтами там было бы `Succ`"
    );
    client.stop();
}

/// Два разных имени дают два разных ответа, а пустое место - никакого.
#[test]
fn a_hover_answers_by_what_is_under_it() {
    let (mut client, _) = Client::start(None);
    client.open(URI, &fixture(FIXTURE));

    // 14,5 - имя семейства в `data Nat where`.
    assert_eq!(
        client.hover(URI, 14, 5)["contents"]["value"],
        json!("Nat : Type 0")
    );
    // 15,2 - конструктор `Zero`.
    assert_eq!(
        client.hover(URI, 15, 2)["contents"]["value"],
        json!("Zero : Nat")
    );
    assert_ne!(
        client.hover(URI, 15, 2)["contents"]["value"],
        client.hover(URI, 16, 2)["contents"]["value"],
        "`Zero` и `Succ` не могут отвечать одинаково"
    );
    // 19,6 - пробел за `двойка`: под курсором имени нет.
    assert_eq!(client.hover(URI, LINE, 6), json!(null), "пустое место");
    // Строка комментария целиком - тоже пустое место.
    assert_eq!(client.hover(URI, 0, 10), json!(null), "комментарий");
    client.stop();
}

/// Тип приходит и с буфера, который проверку **не проходит**.
///
/// Это и есть обычное состояние окна: слово дописывается посередине. `Succ`
/// объявлен выше места отказа, и показать его тип нечему помешать; `двойка`,
/// на которой проход остановился, типа не имеет.
#[test]
fn a_hover_survives_a_refusal() {
    let (mut client, _) = Client::start(None);
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(
        diagnostics.as_array().map(Vec::len),
        Some(1),
        "буфер сломан"
    );
    assert_eq!(
        client.hover(URI, LINE, 18)["contents"]["value"],
        json!(SUCC)
    );
    assert_eq!(
        client.hover(URI, LINE, 0),
        json!(null),
        "`двойка` не объявилась: типа у неё нет"
    );
    client.stop();
}

/// Переход к определению внутри файла: имя ведёт к своему объявлению.
#[test]
fn a_definition_points_inside_the_file() {
    let (mut client, _) = Client::start(None);
    client.open(URI, &fixture(FIXTURE));

    // `Succ` в теле -> строка конструктора, 16,2..16,6.
    assert_eq!(
        client.definition(URI, LINE, 18),
        json!({
            "uri": URI,
            "range": {
                "start": { "line": 16, "character": 2 },
                "end": { "line": 16, "character": 6 },
            },
        })
    );
    // `двойка` клаузы -> её сигнатура строкой выше. Отказ переходу не помеха:
    // место объявления знает дерево, а не сигнатура.
    assert_eq!(
        client.definition(URI, LINE, 0)["range"],
        json!({
            "start": { "line": 18, "character": 0 },
            "end": { "line": 18, "character": 6 },
        })
    );
    // `Nat` в типе конструктора -> строка `data Nat where`.
    assert_eq!(
        client.definition(URI, 16, 9)["range"]["start"],
        json!({ "line": 14, "character": 5 })
    );
    assert_eq!(
        client.definition(URI, LINE, 6),
        json!(null),
        "с пустого места идти некуда"
    );
    client.stop();
}

/// Связывание, **заслоняющее** определение того же имени.
///
/// Это и есть случай, на котором врёт дешёвый hover, «посмотреть имя в
/// сигнатуре»: на корпусе таких заслонений 37. Здесь параметр клаузы назван
/// так же, как определение выше, и над ним не должно быть ни типа
/// определения, ни перехода к нему.
///
/// Имена кириллические намеренно: у них байт вдвое больше, чем единиц UTF-16,
/// и колонка, записанная руками, различает счёт.
#[test]
fn a_local_binding_shadows_a_definition_of_the_same_name() {
    const SOURCE: &str = "data Nat where\n  Zero : Nat\n  Succ : Nat -> Nat\n\n\
                          один : Nat\nодин = Succ Zero\n\n\
                          повтор : Nat -> Nat\nповтор Zero = Zero\nповтор один = Succ один\n";
    let (mut client, _) = Client::start(None);
    assert_eq!(client.open(URI, SOURCE), json!([]), "программа принята");

    // 4,0 - определение `один`; 9,7 - одноимённый параметр клаузы; 9,19 - его
    // использование.
    assert_eq!(
        client.hover(URI, 4, 0)["contents"]["value"],
        json!("один : Nat")
    );
    assert_eq!(client.hover(URI, 9, 7), json!(null), "связывание, не имя");
    assert_eq!(
        client.hover(URI, 9, 19),
        json!(null),
        "заслонённое имя не отдаёт чужой тип"
    );
    let binder = json!({
        "start": { "line": 9, "character": 7 },
        "end": { "line": 9, "character": 11 },
    });
    assert_eq!(
        client.definition(URI, 9, 19)["range"],
        binder,
        "переход ведёт к связыванию, а не к определению выше"
    );
    assert_eq!(client.definition(URI, 9, 7)["range"], binder);

    // Имя группы клауз написано на каждой, а в дереве лежит однажды.
    assert_eq!(
        client.hover(URI, 9, 0)["contents"]["value"],
        json!("повтор : (ω _ : Nat) -> {| e0} Nat"),
        "имя второй клаузы - то же определение"
    );
    assert_eq!(
        client.definition(URI, 9, 0)["range"],
        json!({
            "start": { "line": 7, "character": 0 },
            "end": { "line": 7, "character": 6 },
        }),
        "вторая клауза ведёт к сигнатуре"
    );
    client.stop();
}

/// Копия корпусного проекта во временном каталоге.
///
/// Копия, а не сам корпус: прогон правит файлы, а файлы репозитория ему не
/// принадлежат. Правятся при этом **буферы**, и на диск после копирования не
/// пишется ничего - иначе свидетель «правка буфера видна зависящему» держался
/// бы на файловой системе, а не на сервере.
#[allow(
    clippy::unwrap_used,
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение, и падать он должен громко"
)]
fn copied(name: &str) -> PathBuf {
    let from = corpus().join("project");
    let to = std::env::temp_dir().join(format!("adamas-lsp-{name}"));
    let _ = std::fs::remove_dir_all(&to);
    std::fs::create_dir_all(to.join("Std")).unwrap();
    for entry in std::fs::read_dir(&from).unwrap() {
        let path = entry.unwrap().path();
        if path.is_file() {
            std::fs::copy(&path, to.join(path.file_name().unwrap())).unwrap();
        }
    }
    for entry in std::fs::read_dir(from.join("Std")).unwrap() {
        let path = entry.unwrap().path();
        std::fs::copy(&path, to.join("Std").join(path.file_name().unwrap())).unwrap();
    }
    to
}

/// URI файла проекта. Пустой `relative` даёт URI самого корня.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: путь без URI означает сломанное окружение"
)]
fn addressed(root: &Path, relative: &str) -> String {
    let path = if relative.is_empty() {
        root.to_path_buf()
    } else {
        root.join(relative)
    };
    adamas_lsp::project::uri_of(&path)
        .expect("путь проекта переводится в URI")
        .as_str()
        .to_owned()
}

/// Правка одного файла меняет диагностику того, кто его подключил.
///
/// Свидетель различает по построению: `times` в `main.adamas` **не объявлен**,
/// он берётся из `Std/Arith.adamas`, и без разрешения имён между файлами эта
/// программа не проверяется вовсе. Правится при этом буфер, а не файл: на
/// диске всё время лежит исходный текст, поэтому подчёркивание в `main` может
/// прийти только от того, что сервер читает открытые буферы.
///
/// Проверяется **содержание**, а не факт прихода: «диагностика пришла» зелено
/// и когда пришла не та. Сверяются текст сообщения и место, а после отката -
/// что список стал пуст.
///
/// Правок две, потому что через границу файлов идут две разные вещи. Первая
/// уносит имя из экспортируемых - её ловит разрешение имён. Вторая меняет
/// **тип**: модуль остаётся цел, а тело зависящего перестаёт сходиться, и в
/// сообщении стоит тип из чужого файла.
#[test]
fn an_edit_in_a_module_moves_the_dependents_diagnostic() {
    let root = copied("dependents");
    let main = addressed(&root, "main.adamas");
    let arith = addressed(&root, "Std/Arith.adamas");
    let main_text = std::fs::read_to_string(root.join("main.adamas")).expect("вход читается");
    let arith_text =
        std::fs::read_to_string(root.join("Std/Arith.adamas")).expect("модуль читается");

    let (mut client, _) = Client::start_in(Some(&addressed(&root, "")), None);
    assert_eq!(client.open(&main, &main_text), json!([]), "проект принят");
    assert_eq!(client.open(&arith, &arith_text), json!([]), "модуль принят");
    client.settled();

    // Имя уезжает из подключённого модуля. Сам модуль от этого в порядке -
    // ломается **зависящий**, и в этом весь смысл прогона.
    let renamed = arith_text.replace("times", "multiply");
    assert_ne!(renamed, arith_text, "правка обязана что-то менять");
    client.edit(&arith, 2, &renamed);
    let after = client.settled();
    assert_eq!(after.get(&arith), Some(&json!([])), "сам модуль цел");

    let broken = after
        .get(&main)
        .expect("правка модуля обязана перепроверить зависящий буфер");
    assert_eq!(broken.as_array().map(Vec::len), Some(1), "{broken}");
    assert_eq!(
        broken[0]["message"],
        json!("модуль `Std.Arith` не объявляет `times`"),
        "{broken}"
    );
    assert_eq!(
        broken[0]["range"],
        json!({
            "start": { "line": 14, "character": 24 },
            "end": { "line": 14, "character": 29 },
        }),
        "подчёркнуто `times` в списке открытых имён входного файла"
    );

    // Вторая правка - **типом**, а не списком имён: у `times` появляется
    // третий параметр, модуль от этого цел, а тело зависящего перестаёт
    // сходиться. Через границу файлов идёт, стало быть, не только перечень
    // экспортируемых имён, но и сам тип.
    let widened = arith_text.replace(
        "times : Nat -> Nat -> Nat\ntimes Zero m = Zero\ntimes (Succ k) m = plus m (times k m)",
        "times : Nat -> Nat -> Nat -> Nat\ntimes Zero m k = Zero\n\
         times (Succ j) m k = plus m (times j m k)",
    );
    assert_ne!(widened, arith_text, "правка обязана что-то менять");
    client.edit(&arith, 3, &widened);
    let typed = client.settled();
    assert_eq!(typed.get(&arith), Some(&json!([])), "сам модуль цел");
    let mismatch = typed
        .get(&main)
        .expect("правка типа обязана перепроверить зависящий буфер");
    assert_eq!(mismatch.as_array().map(Vec::len), Some(1), "{mismatch}");
    assert!(
        mismatch[0]["message"].as_str().is_some_and(|it| {
            it.starts_with(
                "несовпадение типов: ожидался `Std.Base.Nat`, \
                 получен `(ω _ : Std.Base.Nat) -> Std.Base.Nat`",
            )
        }),
        "{mismatch}"
    );
    assert_eq!(
        mismatch[0]["range"]["start"]["line"],
        json!(42),
        "подчёркнут список `main`, а не строка импорта"
    );

    // Откат буфера гасит подчёркивание там же.
    client.edit(&arith, 4, &arith_text);
    let back = client.settled();
    assert_eq!(
        back.get(&main),
        Some(&json!([])),
        "откат правки обязан снимать подчёркивание с зависящего: {back:?}"
    );
    client.stop();
}

/// Отказ внутри подключённого модуля подчёркивается **в нём**, а не во входном
/// файле: спан живёт в чужом тексте, и нарисованный по входному он указал бы на
/// случайную строку.
#[test]
fn a_refusal_inside_a_module_is_underlined_in_that_module() {
    let root = copied("inside");
    let main = addressed(&root, "main.adamas");
    let logic = addressed(&root, "Std/Logic.adamas");
    let main_text = std::fs::read_to_string(root.join("main.adamas")).expect("вход читается");

    // Модуль ломается **на диске** и открытым буфером не является: иначе его
    // диагностику публиковал бы его собственный проход.
    let path = root.join("Std/Logic.adamas");
    let text = std::fs::read_to_string(&path).expect("модуль читается");
    std::fs::write(&path, text.replace("not True = False", "not True = Zero"))
        .expect("модуль пишется");

    let (mut client, _) = Client::start_in(Some(&addressed(&root, "")), None);
    assert_eq!(
        client.open(&main, &main_text),
        json!([]),
        "во входном файле подчёркивать нечего: отказ живёт в чужом тексте"
    );

    let sent = client.settled();
    let there = sent
        .get(&logic)
        .expect("отказ подключённого модуля обязан дойти до его файла");
    assert_eq!(there.as_array().map(Vec::len), Some(1), "{there}");
    assert_eq!(
        there[0]["range"],
        json!({
            "start": { "line": 7, "character": 11 },
            "end": { "line": 7, "character": 15 },
        }),
        "подчёркнут `Zero` в `Std/Logic.adamas`, а не строка входного файла"
    );
    assert_eq!(
        there[0]["message"],
        json!("имя `Zero` не найдено"),
        "{there}"
    );

    // Починка гасит подчёркивание в файле, которого никто не открывал: само
    // оно не исчезнет.
    std::fs::write(&path, &text).expect("модуль пишется");
    client.edit(&main, 2, &format!("{main_text}-- правка\n"));
    let fixed = client.settled();
    assert_eq!(fixed.get(&main), Some(&json!([])));
    assert_eq!(fixed.get(&logic), Some(&json!([])), "{fixed:?}");
    client.stop();
}

/// Пол десяти кругов «правка -> диагностика всех, кого она касается».
#[allow(
    clippy::expect_used,
    reason = "заготовка стенда: отказ здесь означает сломанное окружение"
)]
fn floor(client: &mut Client, uri: &str, text: &str, from: i64, expect: &[&str]) -> u128 {
    let mut best = std::time::Duration::MAX;
    for round in 0..10 {
        let written = format!("{text}-- {round}\n");
        let started = std::time::Instant::now();
        client.edit(uri, from + round, &written);
        let sent = client.settled();
        best = best.min(started.elapsed());
        for awaited in expect {
            assert_eq!(
                sent.get(*awaited),
                Some(&json!([])),
                "не дождались буфера {awaited} - мерится половина круга"
            );
        }
    }
    best.as_micros()
}

/// Круг «правка -> диагностика» на проекте. Зовётся руками: величина требует
/// тихой машины.
///
/// ```text
/// cargo test --release -p adamas-lsp --test protocol -- --ignored --nocapture
/// ```
///
/// Мерится то, чего ждёт человек: от `didChange` до `publishDiagnostics`
/// последнего буфера, которого правка касается. Три точки, потому что цена у
/// них разная: правка входного файла стоит одного прохода по программе, а
/// правка библиотечного модуля - по проходу на **каждый** открытый буфер,
/// который его подключил, и множитель растёт с числом открытых окон.
#[test]
#[ignore = "стенд времени: величина требует тихой машины"]
#[allow(
    clippy::expect_used,
    reason = "заготовка стенда: отказ здесь означает сломанное окружение"
)]
fn what_a_round_costs_on_a_project() {
    let root = copied("round");
    let main = addressed(&root, "main.adamas");
    let base = addressed(&root, "Std/Base.adamas");
    let main_text = std::fs::read_to_string(root.join("main.adamas")).expect("вход читается");
    let base_text = std::fs::read_to_string(root.join("Std/Base.adamas")).expect("модуль читается");

    let (mut client, _) = Client::start_in(Some(&addressed(&root, "")), None);
    assert_eq!(client.open(&main, &main_text), json!([]));
    assert_eq!(client.open(&base, &base_text), json!([]));
    client.settled();

    let alone = floor(&mut client, &main, &main_text, 100, &[&main]);
    eprintln!("правка входного файла, два буфера: {alone} мкс");

    let pair = floor(&mut client, &base, &base_text, 200, &[&base, &main]);
    eprintln!("правка `Std/Base`, два буфера: {pair} мкс");

    // Все десять окон разом - худший случай: `Std/Base` подключён всеми, и
    // каждый из них перепроверяется целиком.
    let mut awaited = vec![main.clone(), base.clone()];
    for entry in std::fs::read_dir(root.join("Std")).expect("каталог библиотеки") {
        let path = entry.expect("файл библиотеки").path();
        let uri = adamas_lsp::project::uri_of(&path).expect("путь переводится в URI");
        if uri.as_str() == base {
            continue;
        }
        let text = std::fs::read_to_string(&path).expect("модуль читается");
        client.open(uri.as_str(), &text);
        awaited.push(uri.as_str().to_owned());
    }
    client.settled();
    let borrowed: Vec<&str> = awaited.iter().map(String::as_str).collect();
    let all = floor(&mut client, &base, &base_text, 300, &borrowed);
    eprintln!("правка `Std/Base`, десять буферов: {all} мкс");
    client.stop();
}

/// Чего стоит открытый буфер - памятью и кругом перерисовки.
///
/// Зовётся руками рядом с [`what_a_round_costs_on_a_project`] и по той же
/// причине: обе величины требуют тихой машины.
///
/// ```text
/// cargo test --release -p adamas-lsp --test protocol -- --ignored --nocapture
/// ```
///
/// Мерится **капстоун** (944 строки) в десяти буферах: волна 1 Фазы 9 решила
/// хранить дерево разбора замером, а не вкусом, и всякое новое поле буфера
/// обязано назвать свою цену тем же способом. Резидентная память читается у
/// процесса сервера, круг - тот же, что у проекта: от `didChange` до
/// `publishDiagnostics`.
#[test]
#[ignore = "стенд памяти: величина требует тихой машины"]
#[allow(
    clippy::expect_used,
    reason = "заготовка стенда: отказ здесь означает сломанное окружение"
)]
fn what_a_buffer_costs_in_memory() {
    const BUFFERS: usize = 10;
    let text = std::fs::read_to_string(corpus().join("eval").join("interpreter.adamas"))
        .expect("капстоун читается");

    let (mut client, _) = Client::start(None);
    let empty = client.resident();
    eprintln!("сервер без буферов: {empty} КиБ");

    let mut uris = Vec::with_capacity(BUFFERS);
    for at in 0..BUFFERS {
        let uri = format!("file:///corpus/capstone-{at}.adamas");
        client.open(&uri, &text);
        uris.push(uri);
        if at == 0 {
            client.settled();
            let one = client.resident();
            eprintln!("один буфер: {one} КиБ (+{} КиБ)", one - empty);
        }
    }
    client.settled();
    let all = client.resident();
    eprintln!(
        "{BUFFERS} буферов: {all} КиБ (+{} КиБ, то есть {} КиБ на буфер)",
        all - empty,
        (all - empty) / BUFFERS as u64
    );

    let first = uris.first().expect("буферы открыты").clone();
    let round = floor(&mut client, &first, &text, 100, &[&first]);
    eprintln!("круг перерисовки капстоуна при {BUFFERS} буферах: {round} мкс");
    client.stop();
}

/// Кривое уведомление не уносит с собой открытые файлы.
///
/// Сервер держит буферы всех окон сразу; упасть на одном кадре значит погасить
/// подчёркивания везде. Проверяется тем, что после негодного `didOpen` сервер
/// отвечает на годный.
#[test]
fn a_malformed_notification_does_not_kill_the_server() {
    let (mut client, _) = Client::start(None);
    // `version` строкой вместо числа: клиент так писать не должен, но сервер
    // живёт не потому, что клиент безупречен.
    client.notify(
        "textDocument/didOpen",
        &json!({
            "textDocument": {
                "uri": URI,
                "languageId": "adamas",
                "version": "не число",
                "text": "",
            }
        }),
    );
    let diagnostics = client.open(URI, &fixture(FIXTURE));
    assert_eq!(diagnostics[0]["range"]["start"]["character"], json!(18));
    client.stop();
}

/// Буфер, у которого подсказка стоит **после** многобайтового текста той же
/// строки.
///
/// Последняя строка существенна: `wrap n = ` и `{- 😀 -} ` дают до `MkPair`
/// **20 байтов, 18 кодовых единиц UTF-16 и 17 знаков**. Три разных числа одной
/// позиции различают все три прочтения сразу, а на латинице любая поломка
/// перевода невидима.
const HINTED: &str = "\
data Nat where
  Zero : Nat
  Succ : Nat -> Nat

data Pair where
  MkPair : Nat -> Nat -> Pair

wrap : Nat -> Pair
wrap n = {- 😀 -} MkPair n n
";

/// URI буфера подсказок. С диском не связан.
const HINTED_URI: &str = "file:///corpus/hinted.adamas";

/// Подсказка приходит по протоколу и стоит там, где написано руками.
///
/// Проверяется **содержание**: подпись, её части и адрес, куда ведёт щелчок.
/// «Сервер ответил списком» зелено и тогда, когда список бессмыслен.
#[test]
fn an_inlay_hint_lands_past_multibyte_text() {
    let (mut client, result) = Client::start(None);
    assert_eq!(result["capabilities"]["inlayHintProvider"], json!(true));
    assert_eq!(client.open(HINTED_URI, HINTED), json!([]));

    let hints = client.inlay(HINTED_URI, 0, 20);
    assert_eq!(hints.as_array().map(Vec::len), Some(2), "{hints}");

    // Статус над объявлением: подпись частями, и щелчок по слову `куча` ведёт
    // туда, где определение аллоцирует.
    assert_eq!(hints[0]["position"], json!({ "line": 7, "character": 0 }));
    assert_eq!(hints[0]["label"][0]["value"], json!("куча"));
    assert_eq!(
        hints[0]["label"][0]["location"]["range"],
        json!({
            "start": { "line": 8, "character": 18 },
            "end": { "line": 8, "character": 28 },
        }),
        "адрес звена - в кодовых единицах UTF-16"
    );
    assert_eq!(hints[0]["label"][1]["value"], json!(": "));
    assert_eq!(hints[0]["label"][2]["value"], json!("MkPair"));

    // Место внутри тела - само построение, и стоит оно за эмодзи.
    assert_eq!(hints[1]["position"], json!({ "line": 8, "character": 18 }));
    assert_eq!(hints[1]["label"], json!("куча"));
    client.stop();
}

/// Байтами те же две позиции, когда клиент попросил UTF-8.
///
/// Прогон различает **счёт**, а не наличие: перевод, ошибочный одинаково в обе
/// стороны, круговой проверке не виден, а записанным руками числам - виден.
#[test]
fn utf8_moves_the_hint_to_bytes() {
    let (mut client, _) = Client::start(Some(&["utf-8"]));
    assert_eq!(client.open(HINTED_URI, HINTED), json!([]));
    let hints = client.inlay(HINTED_URI, 0, 20);
    assert_eq!(hints[1]["position"], json!({ "line": 8, "character": 20 }));
    assert_eq!(
        hints[0]["label"][0]["location"]["range"]["start"],
        json!({ "line": 8, "character": 20 })
    );
    client.stop();
}

/// И знаками, когда UTF-32.
#[test]
fn utf32_moves_the_hint_to_characters() {
    let (mut client, _) = Client::start(Some(&["utf-32"]));
    assert_eq!(client.open(HINTED_URI, HINTED), json!([]));
    let hints = client.inlay(HINTED_URI, 0, 20);
    assert_eq!(hints[1]["position"], json!({ "line": 8, "character": 17 }));
    client.stop();
}

/// Окно клиента ограничивает ответ и по протоколу тоже.
#[test]
fn the_window_reaches_the_server() {
    let (mut client, _) = Client::start(None);
    assert_eq!(client.open(HINTED_URI, HINTED), json!([]));
    let hints = client.inlay(HINTED_URI, 8, 9);
    assert_eq!(hints.as_array().map(Vec::len), Some(1), "{hints}");
    assert_eq!(hints[0]["position"], json!({ "line": 8, "character": 18 }));
    client.stop();
}

/// Буфер, о котором сервер не знает, подсказок не даёт и отказом не отвечает.
#[test]
fn an_unknown_buffer_gets_an_empty_list() {
    let (mut client, _) = Client::start(None);
    assert_eq!(client.inlay("file:///nowhere.adamas", 0, 10), json!([]));
    client.stop();
}

/// Правка **чужого** файла просит клиента перерисовать подсказки.
///
/// Подчёркивание зависящего буфера сервер обновляет сам, а подсказку - не
/// может: её рисует клиент, и перезапрашивает он её по правке того документа,
/// который показывает. Цепочка вины пересекает границу файла, поэтому правка
/// библиотеки меняет подсказку в окне, которого никто не трогал.
///
/// Свидетель различает по построению: без правки чужого файла просьбы быть не
/// должно, и это проверяется тем же прогоном.
#[test]
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn editing_a_dependency_asks_the_client_to_redraw_hints() {
    let root = copied("refresh");
    let main = addressed(&root, "main.adamas");
    let base = addressed(&root, "Std/Base.adamas");
    let main_text = std::fs::read_to_string(root.join("main.adamas")).expect("вход читается");
    let base_text = std::fs::read_to_string(root.join("Std/Base.adamas")).expect("модуль читается");

    let mut client = Client::start_refreshing(Some(&addressed(&root, "")));
    client.open(&main, &main_text);
    client.open(&base, &base_text);
    client.settled();
    client.asked();

    // Правка входного файла: зависящих у него нет, и просить нечего - клиент
    // сам перезапросит подсказки того документа, который правили.
    client.edit(&main, 2, &format!("{main_text}-- правка\n"));
    client.settled();
    assert_eq!(
        client.asked(),
        Vec::<String>::new(),
        "у входного файла зависящих нет"
    );

    // Правка библиотеки: `main` её подключает, и его подсказки устарели.
    client.edit(&base, 2, &format!("{base_text}-- правка\n"));
    client.settled();
    assert_eq!(
        client.asked(),
        vec!["workspace/inlayHint/refresh".to_owned()],
        "правка библиотеки обязана попросить перерисовку"
    );
    client.stop();
}

/// Чего стоит перерисовка подсказок - кругом запроса и числом подсказок.
///
/// Зовётся руками рядом с прочими стендами и по той же причине: величина
/// требует тихой машины.
///
/// ```text
/// cargo test --release -p adamas-lsp --test protocol -- --ignored --nocapture
/// ```
///
/// Мерятся два окна, и разница между ними - предмет: `inlayHint` спрашивают по
/// **видимому** куску, и клиент шлёт его на каждую прокрутку. Если цена не
/// зависит от окна, значит платится она обходом сигнатуры целиком, и это надо
/// знать числом, а не предполагать.
///
/// Снято 2026-09-23 на капстоуне (944 строки, release): **окно в 40 строк - 50
/// мкс**, файл целиком - 1598 мкс при 249 подсказках. Прокрутка поэтому стоит
/// на три порядка меньше круга правки (42 мс), а от окна цена зависит, то есть
/// платится она не обходом всего подряд.
#[test]
#[ignore = "стенд времени: величина требует тихой машины"]
#[allow(
    clippy::expect_used,
    reason = "заготовка стенда: отказ здесь означает сломанное окружение"
)]
fn what_a_hint_costs() {
    let text = std::fs::read_to_string(corpus().join("eval").join("interpreter.adamas"))
        .expect("капстоун читается");
    let uri = "file:///corpus/capstone.adamas";
    let (mut client, _) = Client::start(None);
    client.open(uri, &text);
    client.settled();

    let mut round = |from: u64, upto: u64, what: &str| {
        let mut best = std::time::Duration::MAX;
        let mut count = 0;
        for _ in 0..20 {
            let started = std::time::Instant::now();
            let hints = client.inlay(uri, from, upto);
            best = best.min(started.elapsed());
            count = hints.as_array().map_or(0, Vec::len);
        }
        eprintln!("{what}: {} мкс, подсказок {count}", best.as_micros());
    };
    round(0, 40, "окно в 40 строк");
    round(0, 1000, "файл целиком (944 строки)");
    client.stop();
}

/// Клиент, не объявивший возможность, просьбы не получает.
///
/// Спецификация разрешает запрос только объявившему; отдельный прогон потому,
/// что «сервер молчит» неотличимо от «сервер сломан», пока рядом нет прогона,
/// где он говорит.
#[test]
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn a_client_without_the_capability_is_not_asked() {
    let root = copied("silent");
    let main = addressed(&root, "main.adamas");
    let base = addressed(&root, "Std/Base.adamas");
    let main_text = std::fs::read_to_string(root.join("main.adamas")).expect("вход читается");
    let base_text = std::fs::read_to_string(root.join("Std/Base.adamas")).expect("модуль читается");

    let (mut client, _) = Client::start_in(Some(&addressed(&root, "")), None);
    client.open(&main, &main_text);
    client.open(&base, &base_text);
    client.settled();
    client.asked();

    client.edit(&base, 2, &format!("{base_text}-- правка\n"));
    client.settled();
    assert_eq!(
        client.asked(),
        Vec::<String>::new(),
        "возможность не объявлена - запроса быть не должно"
    );
    client.stop();
}

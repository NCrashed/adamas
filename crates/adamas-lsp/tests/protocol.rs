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
    }

    impl Client {
        /// Поднимает сервер и делает рукопожатие.
        ///
        /// `encodings` - список из `general.positionEncodings`; `None` значит,
        /// что клиент возможности не объявил вовсе, и это умолчание протокола.
        pub(crate) fn start(encodings: Option<&[&str]>) -> (Self, Value) {
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
            };
            let general = match encodings {
                Some(list) => json!({ "positionEncodings": list }),
                None => Value::Null,
            };
            let result = client.request(
                "initialize",
                &json!({
                    "processId": Value::Null,
                    "rootUri": Value::Null,
                    "capabilities": { "general": general },
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
            self.notify(
                "textDocument/didChange",
                &json!({
                    "textDocument": { "uri": uri, "version": version },
                    "contentChanges": [{ "text": text }],
                }),
            );
            self.diagnostics(uri)
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
            serde_json::from_slice(&body).unwrap()
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

/// Непонятый запрос получает отказ, а не молчание: молчание вешает клиента,
/// а объявлено сервером пока только то, что он умеет.
#[test]
fn an_unsupported_request_is_refused() {
    let (mut client, _) = Client::start(None);
    let answer = client.raw_request("textDocument/hover", &json!({}));
    assert_eq!(
        answer["error"]["code"],
        json!(-32601),
        "MethodNotFound: {answer}"
    );
    client.stop();
}

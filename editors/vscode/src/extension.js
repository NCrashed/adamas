// Расширение VS Code: поднять `adamas-lsp` и отдать ему буферы `.adamas`.
//
// Обычный JS, без TypeScript и без шага сборки. Причина не в нелюбви к типам:
// шаг сборки означает, что проверяется одно (собранный `out/`), а читается и
// правится другое (`src/`), и разойтись они могут молча. Файл здесь один, и он
// же едет в `.vsix`.
//
// Клиент - `vscode-languageclient`, а не свой разбор кадров. Свой был бы второй
// записью спецификации: синхронизация документа, согласование кодировки позиций,
// перезапуск после падения сервера, отмена запросов. Треки B (семантические
// токены) и D (hover) добавляются к нему объявлением возможности, а не новым
// кодом транспорта.

const { workspace } = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

/** @type {import('vscode-languageclient/node').LanguageClient | undefined} */
let client;

/** Имя бинаря сервера: настройка расширения, иначе поиск в `PATH`. */
function serverCommand() {
  const configured = workspace.getConfiguration("adamas").get("server.path");
  return typeof configured === "string" && configured.length > 0
    ? configured
    : "adamas-lsp";
}

/**
 * @param {import('vscode').ExtensionContext} context
 */
async function activate(context) {
  client = new LanguageClient(
    "adamas",
    "Adamas Language Server",
    // `TransportKind.stdio`, и это не умолчание: `transport` со значением `1` -
    // это `ipc`, при котором сервер молчит, а редактор показывает пустой файл
    // без единого подчёркивания. Проверено прогоном: `COUNT=0` при живом
    // сервере и разобранном языке.
    { command: serverCommand(), transport: TransportKind.stdio },
    {
      // Схема `untitled` наравне с `file`: текст сервер получает уведомлением,
      // и ненаписанному на диск буферу диагностика нужна ровно так же. Путь у
      // такого буфера сервер не выведет, поэтому подключать модули он не
      // сможет - но это ровно то, чего от ненаписанного файла и ждут.
      documentSelector: [
        { scheme: "file", language: "adamas" },
        { scheme: "untitled", language: "adamas" },
      ],
      outputChannelName: "Adamas",
    },
  );
  await client.start();
  context.subscriptions.push(client);
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };

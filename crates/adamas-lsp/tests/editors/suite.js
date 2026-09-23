// Драйвер прогона VS Code. Запускается `crates/adamas-lsp/tests/editors.rs`
// через `--extensionTestsPath`, то есть **внутри** extension host'а настоящего
// редактора: `vscode` здесь - тот самый модуль, который видит расширение.
//
// Печатает строки `КЛЮЧ=значение`, ничего не утверждая. Все сверки - в тесте:
// утверждение, живущее в драйвере, легко сделать зелёным, не заметив.
//
// Колонки VS Code меряет кодовыми единицами UTF-16 и хранит их так же, поэтому
// сверять одни только числа было бы кругом. `underlined` разрывает круг: это
// текст, который редактор **сам** вырезал из своего буфера по полученному
// диапазону. Диапазон, посчитанный байтами, вырежет не то слово.

const vscode = require("vscode");

const EXTENSION = "adamas-lang.adamas";

function say(key, value) {
  console.log(key + "=" + value);
}

async function settle(uri, want) {
  const deadline = Date.now() + 60000;
  for (;;) {
    const found = vscode.languages.getDiagnostics(uri);
    if (want(found) || Date.now() > deadline) {
      return found;
    }
    await new Promise((resume) => setTimeout(resume, 50));
  }
}

function report(prefix, document, found) {
  say(prefix + "COUNT", found.length);
  for (const d of found) {
    say(
      prefix + "DIAG",
      JSON.stringify({
        line: d.range.start.line,
        start: d.range.start.character,
        end: d.range.end.character,
        severity: d.severity,
        source: d.source,
        message: d.message,
        underlined: document.getText(d.range),
      }),
    );
  }
}

async function run() {
  const extension = vscode.extensions.getExtension(EXTENSION);
  say("FOUND", Boolean(extension));
  if (extension) {
    say("FROM", extension.extensionPath);
    try {
      await extension.activate();
      say("ACTIVE", extension.isActive);
    } catch (error) {
      // Расширение без `node_modules` падает именно здесь, и молчать об этом
      // нельзя: снаружи это выглядело бы как «сервер не ответил».
      say("ACTIVATION_FAILED", String(error));
    }
  }

  const uri = vscode.Uri.file(process.env.ADAMAS_FIXTURE);
  const document = await vscode.workspace.openTextDocument(uri);
  await vscode.window.showTextDocument(document);
  say("LANGUAGE", document.languageId);

  report("", document, await settle(uri, (found) => found.length > 0));

  // Ненаписанный на диск буфер: схема `untitled`, файла нет вовсе. Сервер
  // путей не знает, текст получает уведомлением - значит, диагностика обязана
  // прийти и сюда. Текст тот же, поэтому и позиции те же.
  const fresh = await vscode.workspace.openTextDocument({
    language: "adamas",
    content: document.getText(),
  });
  await vscode.window.showTextDocument(fresh);
  say("UNTITLED_SCHEME", fresh.uri.scheme);
  report(
    "UNTITLED_",
    fresh,
    await settle(fresh.uri, (found) => found.length > 0),
  );

  // Круг «правка -> диагностика». Правка идёт через API редактора, то есть тем
  // же путём, что правка руками: `didChange` уходит серверу, ответ гасит
  // подчёркивание.
  const broken = "Succ Zero Zero";
  const at = document.getText().lastIndexOf(broken);
  const edit = new vscode.WorkspaceEdit();
  edit.replace(
    uri,
    new vscode.Range(
      document.positionAt(at),
      document.positionAt(at + broken.length),
    ),
    "Succ Zero",
  );
  say("EDITED", await vscode.workspace.applyEdit(edit));
  report("AFTER_", document, await settle(uri, (found) => found.length === 0));

  // Подсказки §5.1 на починенном буфере. Включать их VS Code не требует -
  // хватает объявленной сервером возможности, - и это ровно та разница с
  // Neovim, ради которой прогон стоит в обоих редакторах.
  //
  // `executeInlayHintProvider` идёт через клиента расширения, то есть через
  // настоящий запрос `textDocument/inlayHint`.
  const shown = await vscode.commands.executeCommand(
    "vscode.executeInlayHintProvider",
    uri,
    new vscode.Range(0, 0, document.lineCount, 0),
  );
  say("INLAY_COUNT", shown.length);
  for (const item of shown) {
    const label = Array.isArray(item.label)
      ? item.label.map((piece) => piece.value).join("")
      : item.label;
    say(
      "INLAY",
      JSON.stringify({
        line: item.position.line,
        column: item.position.character,
        label: label,
        // Текст от места подсказки до конца строки, вырезанный **редактором**
        // по его собственному счёту колонок.
        after: document.getText(
          new vscode.Range(
            item.position,
            document.lineAt(item.position.line).range.end,
          ),
        ),
      }),
    );
  }
}

module.exports = { run };

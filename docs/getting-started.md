# Быстрый старт: от нуля до работающей программы

Как на машине с этим репозиторием завести проект на Adamas, прогнать его
всеми командами драйвера и получить диагностику в редакторе. Сборка самого
компилятора и правила PR — в [`CONTRIBUTING.md`](../CONTRIBUTING.md); здесь
компилятор используется, а не разрабатывается.

## 1. Собрать бинарники

```sh
cd /путь/к/adamas
nix develop --command bash -c 'cargo build --release -p adamas-cli -p adamas-lsp'
```

Появятся `target/release/adamas` (драйвер) и `target/release/adamas-lsp`
(language server). На время сессии их удобно положить в `PATH`:

```sh
export PATH="/путь/к/adamas/target/release:$PATH"
```

## 2. Завести проект

```sh
adamas new ~/hello-adamas
cd ~/hello-adamas
```

Раскладка (§7.1, §7.3):

```text
hello-adamas/
  adamas.toml        манифест: одна секция [package]
  .gitignore         скрывает .adamas/ — кеш зависимостей и артефакты сборки
  src/Main.adamas    вход программы
  src/Test.adamas    её тесты
```

Заготовка — настоящая программа: `Main.adamas` объявляет унарные наты,
`plus` с линейным аргументом и `main`, который считает; `Test.adamas`
подключает вход как модуль и сверяет ответы. Имя пакета берётся из
последнего сегмента пути, другое задаёт `--name`.

## 3. Прогнать команды

```sh
adamas check .              # разобрать, элаборировать, проверить типы
adamas check . --type main  # напечатать объявленный тип имени — то же, что hover
adamas eval .               # посчитать main интерпретатором
adamas run .                # собрать в исполняемый файл и запустить
adamas run . --backend llvm # то же через цепочку LLVM вместо порождённого C
adamas test .               # каждое test*-определение типа Bool обязано дать True
adamas build .              # только собрать; путь к бинарю печатается
```

`build` и `run` зовут `cc` (а с `--backend llvm` — `llvm-as`, `opt`, `llc`),
и эти инструменты есть только в dev-окружении. Либо работайте изнутри
`nix develop`, либо оборачивайте один вызов:

```sh
nix develop /путь/к/adamas --command bash -c 'adamas run ~/hello-adamas'
```

`check`, `eval` и `test` внешних инструментов не зовут и работают где угодно.

## 4. Второй файл — второй модуль

Файл — это модуль (§4.8). Положите рядом `src/Arith.adamas`:

```adamas
import Main (Nat, Zero, Succ, plus)

triple : Nat -> Nat
triple n = plus n (plus n n)
```

и он подключается из любого другого файла проекта через
`import Arith (triple)` — ровно так `Test.adamas` уже подключает `Main`.

## 5. Прелюдия

Автоматически прелюдия не подключается — всегда явный `import`: приставленная
неявно, она легла бы в те же неквалифицированные имена, что и сам модуль
(`crates/adamas-elab/src/decl.rs`). Поэтому заготовка из `adamas new`
объявляет свои `Nat` и `plus` сама.

Своего пакета у прелюдии пока нет — она живёт библиотекой тестового корпуса,
и практический путь сегодня — копия файла в проект:

```sh
mkdir -p src/Std
cp /путь/к/adamas/tests/golden/eval/Std/Prelude.adamas src/Std/
```

Дальше в любом файле — импорт открытым списком; семейство данных открывается
вместе с конструкторами, `Nat` в списке даёт и `Zero`, и `Succ`:

```adamas
import Std.Prelude (Nat, plus, List, length, mapList)
```

Внутри — 297 строк research-уровня: `Bool`/`Nat`/`Maybe`/`List`, классы с
суперклассами, комбинаторы. Это не стандартная библиотека в полном смысле, и
приватности у копии нет: всё, что в файле, видно любому, кто напишет путь
(§10, вопрос 180). Путь «как задумано» — git-зависимость в `adamas.toml`
(§7.3): ключ `[dependencies]` — префикс путей модулей, и `Std.Prelude`
приезжает из чекаута названного репозитория; он заработает, когда прелюдия
получит свой пакет.

## 6. Диагностика в редакторе

Оба плагина — клиенты к одному `adamas-lsp` и показывают те же ошибки, что
печатает `adamas check`, на точной позиции. Подсветки синтаксиса пока нет.
Подробности и Neovim — в [`editors/README.md`](../editors/README.md).

Быстрый путь для VS Code — запуск расширения из исходников:

```sh
cd /путь/к/adamas/editors/vscode && npm ci
code --extensionDevelopmentPath="/путь/к/adamas/editors/vscode" ~/hello-adamas
```

Сервер ищется в `PATH` под именем `adamas-lsp`. Если `code` запущен не из
shell'а с выставленным `PATH`, задайте абсолютный путь в настройках:

```json
"adamas.server.path": "/путь/к/adamas/target/release/adamas-lsp"
```

Проверка, что сервер живой, — сломать программу: замените в `Main.adamas`
`double n = plus n n` на `double n = plus n m`, и подчёркивание появится
ровно на `m`, с тем же текстом, что выдал бы `adamas check`.

Поставить расширение насовсем, а не в dev-режиме:

```sh
cd /путь/к/adamas/editors/vscode
npx @vscode/vsce package
code --install-extension adamas-0.0.0.vsix
```

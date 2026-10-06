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

### Установить насовсем

Через профиль Nix ставятся оба бинарника сразу, в `~/.nix-profile/bin`:

```sh
nix profile add /путь/к/adamas         # в старых Nix: nix profile install
nix profile upgrade adamas             # после git pull
```

Через `cargo install` бинарник попадает в `~/.cargo/bin`, и этот каталог
должен быть в `PATH`:

```sh
cd /путь/к/adamas
nix develop --command bash -c 'cargo install --locked --path crates/adamas-cli'
nix develop --command bash -c 'cargo install --locked --path crates/adamas-lsp'
```

`adamas-lsp` после любого из способов работает и вне `nix develop`. У `adamas`
есть разница. Сборка через Nix зашивает в бинарник полный путь к C-компилятору,
и `adamas build`/`run` работают из любого окружения. После `cargo install` в
бинарнике остаётся просто `gcc`, поэтому вне dev-shell нужен `gcc` в `PATH`
или путь к компилятору в `ADAMAS_CC`. LLVM-бэкенд в обоих случаях ищет
`llvm-as` и соседние утилиты в `PATH` или в каталоге из `ADAMAS_LLVM_BIN`.

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

Заготовка — настоящая программа. `Main.adamas` объявляет `greeting` над
текстом, `triangle` над числом и `main`, который печатает оба:

```adamas
import Std.IO (Console, putLine)

greeting : String -> String
greeting name = "Привет, " <> name <> "!"

triangle : UInt64 -> UInt64
triangle n = if n == 0 then 0 else n + triangle (n - 1)

main : {Console} Unit
main =
  putLine (greeting "мир")
  putLine ("1 + 2 + ... + 10 = " <> show (triangle 10))
```

`Test.adamas` подключает вход как модуль и сверяет ответы. Имя пакета
берётся из последнего сегмента пути, другое задаёт `--name`.

## 3. Прогнать команды

```sh
adamas check .              # разобрать, элаборировать, проверить типы
adamas check . --type main  # напечатать объявленный тип имени — то же, что hover
adamas eval .               # исполнить main интерпретатором
adamas run .                # собрать в исполняемый файл и запустить
adamas run . --backend llvm # то же через цепочку LLVM вместо порождённого C
adamas test .               # каждое test*-определение типа Bool обязано дать True
adamas build .              # только собрать; путь к бинарю печатается в stderr
adamas doc Std.IO           # интерфейс вшитого модуля
```

`eval` и `run` печатают одно и то же:

```text
Привет, мир!
1 + 2 + ... + 10 = 55
```

`main`, чей тип несёт метки `Std.IO`, исполняется сам, и stdout целиком
принадлежит программе: служебная строка `run` — «собрано в …» — уходит в
stderr. `main` без меток (`main : UInt64`) печатает свой ответ, ответ `Unit`
не печатается.

`build` и `run` зовут `cc` (а с `--backend llvm` — `llvm-as`, `opt`, `llc`),
и эти инструменты есть только в dev-окружении. Либо работайте изнутри
`nix develop`, либо оборачивайте один вызов:

```sh
nix develop /путь/к/adamas --command bash -c 'adamas run ~/hello-adamas'
```

`check`, `eval`, `test` и `doc` внешних инструментов не зовут и работают где
угодно.

## 4. Второй файл — второй модуль

Файл — это модуль (§4.8). Положите рядом `src/Text.adamas`:

```adamas
-- | Приветствие громче.
shout : String -> String
shout s = s <> "!!!"
```

и он подключается из любого другого файла проекта через
`import Text (shout)` — ровно так `Test.adamas` уже подключает `Main`.

## 5. Прелюдия и стандартная библиотека

**Прелюдия** вшита в компилятор и подключается сама, без импорта (§4.4):
`Bool`, `Unit`, `Option` (`None`/`Some`), `Result` (`Err`/`Ok`), `String`,
арифметика `+`, `-`, `*` над примитивными числами (`Int8` … `UInt64`,
`Float32`, `Float64`), сравнения `==`, `<` и соседи, `&&` и `||`, склейка
текста `<>` и `show` для целых и `Bool`. Свой `Bool` или свой `show` в
файле заслоняет прелюдный — как всякое своё имя.

**Стандартная библиотека** вшита так же, но подключается **явным** импортом:

| Модуль | Что в нём |
|---|---|
| `Std.IO` | консоль (`putStr`, `putLine`, `readLine`) и файлы (`reading`, `writing`, `appending`) |
| `Std.Except` | обрыв ошибкой: `Except e` с `throw`, `attempt` — ошибка значением |

Интерфейс любого из них — `adamas doc Std.IO`, `adamas doc Std.Except`,
`adamas doc Prelude`. Свой файл проекта на том же пути (`src/Std/IO.adamas`)
сильнее вшитого.

## 6. Ввод-вывод: консоль и файлы

Метка в типе говорит, что функция делает с миром, и только это: `{Console}`
печатает и читает консоль, а файла не тронет. Операции без аргументов
исполняются там, где нужен их ответ:

```adamas
import Std.IO (Console, putLine, readLine)

counted : UInt64 -> {Console} UInt64
counted n = case readLine of
  None -> n
  Some _line -> counted (n + 1)

main : {Console} Unit
main =
  let n = counted 0
  putLine ("строк: " <> show n)
```

```sh
printf 'a\nb\nc\n' | adamas run lines.adamas    # строк: 3
```

`readLine` у конца ввода отвечает `None`; пустая строка — это `Some ""`.

**Файл** читается и пишется внутри области: `reading path k` открывает его и
исполняет `k`, а внутри `k` строки отдаёт `nextLine`; `writing` и `appending`
— то же для `emit` и `emitLine`. Файл закрывается на выходе из `k`, в том
числе на обрыве. Колбэк вправе печатать в консоль и открывать второй файл —
так файл копируется:

```adamas
import Std.IO (Console, Files, IOError, Reading, Writing, reading, writing, nextLine, emitLine)
import Std.Except (Except)

copying : UInt64 -> {Reading, Writing} UInt64
copying n = case nextLine of
  None -> n
  Some s ->
    emitLine s
    copying (n + 1)

into : {Reading, Files, Except IOError} UInt64
into = writing "out.txt" (copying 0)

main : {Console, Files, Except IOError} UInt64
main = reading "in.txt" into
```

Отказ — `Except IOError` (`CannotOpen`, `CannotWrite`). Никем не пойманный,
он печатается в stderr — `ошибка: не открывается файл in.txt` — и кончает
программу кодом 1; поймать его можно `attempt` из `Std.Except`.

Смысл операциям задаёт хендлер, а не объявление: тест вправе исполнить ту же
программу своим хендлером `Console` — с заготовленным вводом и без консоли.
Пример — `tests/golden/eval/console-scripted.adamas`.

## 7. Диагностика в редакторе

Оба плагина — клиенты к одному `adamas-lsp` и показывают те же ошибки, что
печатает `adamas check`, на точной позиции. Подсветки синтаксиса пока нет.
Подробности и Neovim — в [`editors/README.md`](../editors/README.md).

Быстрый путь для VS Code — запуск расширения из исходников:

```sh
cd /путь/к/adamas/editors/vscode && npm ci
code --extensionDevelopmentPath="/путь/к/adamas/editors/vscode" ~/hello-adamas
```

Сервер ищется в `PATH` под именем `adamas-lsp`; как поставить его насовсем,
сказано в [разделе 1](#установить-насовсем). Если `code` запущен не из
shell'а с выставленным `PATH` (например, из меню рабочего стола), задайте
абсолютный путь в пользовательских настройках:

```json
"adamas.server.path": "/путь/к/adamas/target/release/adamas-lsp"
```

Проверка, что сервер живой, — сломать программу: замените в `Main.adamas`
`name <> "!"` на `nam <> "!"`, и подчёркивание появится ровно на `nam`, с
тем же текстом, что выдал бы `adamas check`.

Поставить расширение насовсем, а не в dev-режиме:

```sh
cd /путь/к/adamas/editors/vscode
npx @vscode/vsce package
code --install-extension adamas-0.0.0.vsix
```

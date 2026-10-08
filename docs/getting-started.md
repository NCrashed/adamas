# Getting started: from zero to a running program

How to set up an Adamas project on a machine with this repository, run it
through every driver command and get diagnostics in an editor. Building the
compiler itself and the rules for pull requests are in
[`CONTRIBUTING.md`](../CONTRIBUTING.md); here the compiler is used, not
developed.

## 1. Build the binaries

```sh
cd /path/to/adamas
nix develop --command bash -c 'cargo build --release -p adamas-cli -p adamas-lsp'
```

This produces `target/release/adamas` (the driver) and
`target/release/adamas-lsp` (the language server). For the session it is
convenient to put them on `PATH`:

```sh
export PATH="/path/to/adamas/target/release:$PATH"
```

### Install permanently

A Nix profile installs both binaries at once, into `~/.nix-profile/bin`:

```sh
nix profile add /path/to/adamas         # on older Nix: nix profile install
nix profile upgrade adamas              # after git pull
```

With `cargo install` the binary goes to `~/.cargo/bin`, and that directory
must be on `PATH`:

```sh
cd /path/to/adamas
nix develop --command bash -c 'cargo install --locked --path crates/adamas-cli'
nix develop --command bash -c 'cargo install --locked --path crates/adamas-lsp'
```

After either way `adamas-lsp` works outside `nix develop` too. `adamas`
differs. A Nix build bakes the full path of the C compiler into the binary,
and `adamas build`/`run` work from any environment. After `cargo install` the
binary keeps a bare `gcc`, so outside the dev shell `gcc` must be on `PATH`, or
the compiler's path must be in `ADAMAS_CC`. In both cases the LLVM backend
looks for `llvm-as` and its neighbours on `PATH` or in the directory given by
`ADAMAS_LLVM_BIN`.

Messages follow the user's locale: `ADAMAS_LANG`, then `LC_ALL`,
`LC_MESSAGES` and `LANG`; Russian and English are available, English is the
fallback.

## 2. Create a project

```sh
adamas new ~/hello-adamas
cd ~/hello-adamas
```

The layout (§7.1, §7.3):

```text
hello-adamas/
  adamas.toml        the manifest: a single [package] section
  .gitignore         hides .adamas/ - the dependency cache and build artefacts
  src/Main.adamas    the program's entry
  src/Test.adamas    its tests
```

The template is a real program. `Main.adamas` declares `greeting` over text,
`triangle` over a number, and a `main` that prints both:

```adamas
import Std.IO (Console, putLine)

greeting : String -> String
greeting name = "Hello, " <> name <> "!"

triangle : UInt64 -> UInt64
triangle n = if n == 0 then 0 else n + triangle (n - 1)

main : {Console} Unit
main =
  putLine (greeting "world")
  putLine ("1 + 2 + ... + 10 = " <> show (triangle 10))
```

`Test.adamas` imports the entry as a module and checks the answers. The
package name is taken from the last segment of the path; `--name` sets
another one.

## 3. Run the commands

```sh
adamas check .              # parse, elaborate, check types
adamas check . --type main  # print the declared type of a name - the same as hover
adamas eval .               # run main with the interpreter
adamas run .                # build an executable and run it
adamas run . --backend llvm # the same through the LLVM pipeline instead of generated C
adamas test .               # every test* definition of type Bool must give True
adamas build .              # only build; the path to the binary is printed on stderr
adamas doc Std.IO           # the interface of a built-in module
```

`eval` and `run` print the same thing:

```text
Hello, world!
1 + 2 + ... + 10 = 55
```

A `main` whose type carries `Std.IO` labels runs by itself, and stdout belongs
to the program entirely: the service line of `run` - "built into …" - goes to
stderr. A `main` without labels (`main : UInt64`) prints its answer; an answer
of type `Unit` is not printed.

`build` and `run` call `cc` (and, with `--backend llvm`, `llvm-as`, `opt` and
`llc`), and these tools exist only in the dev environment. Either work inside
`nix develop`, or wrap a single call:

```sh
nix develop /path/to/adamas --command bash -c 'adamas run ~/hello-adamas'
```

`check`, `eval`, `test` and `doc` call no external tools and work anywhere.

## 4. A second file is a second module

A file is a module (§4.8). Put `src/Text.adamas` next to the entry:

```adamas
-- | A louder greeting.
shout : String -> String
shout s = s <> "!!!"
```

and any other file of the project imports it with `import Text (shout)` -
exactly the way `Test.adamas` already imports `Main`.

## 5. The prelude and the standard library

The **prelude** is built into the compiler and comes in by itself, without an
import (§4.4): `Bool`, `Unit`, `Option` (`None`/`Some`), `Result`
(`Err`/`Ok`), `String`, `Nat`, `List` (`[1, 2]`, `::`, `++`, `map`, `filter`,
`foldl`, `foldr`, `length`, `reverse`, `lookup`, `zip`), `NonEmpty`, the
arithmetic `+`, `-`, `*`, `/` and `%` over the primitive numbers (`Int8` …
`UInt64`, `Float32`, `Float64`), the comparisons `==`, `<` and their
neighbours, `&&` and `||`, text concatenation `<>` and `show` for integers and
`Bool`. Your own `Bool` or `show` in a file shadows the prelude's - like any
name of your own.

Integer division needs a proof that the divisor is not zero, and the compiler
finds it: by computation for a literal (`x / 2`), from the branch of a check
for a variable (`if d == 0 then 0 else n / d`), or from a constraint of the
enclosing function (`{d /= 0} =>`). Without any of them, `n / d` is refused
with the missing fact named.

The **standard library** is built in the same way, but comes in by an
**explicit** import:

| Module | What it holds |
|---|---|
| `Std.IO` | the console (`putStr`, `putLine`, `readLine`) and files (`reading`, `writing`, `appending`) |
| `Std.Except` | stopping with an error: `Except e` with `throw`, `attempt` - an error as a value |

The interface of any of them is `adamas doc Std.IO`, `adamas doc Std.Except`,
`adamas doc Prelude`. A file of your project at the same path
(`src/Std/IO.adamas`) is stronger than the built-in one.

## 6. Input and output: the console and files

A label in a type says what a function does to the world, and only that:
`{Console}` prints to and reads the console, and will not touch a file.
Operations without arguments are performed where their answer is needed:

```adamas
import Std.IO (Console, putLine, readLine)

counted : UInt64 -> {Console} UInt64
counted n = case readLine of
  None -> n
  Some _line -> counted (n + 1)

main : {Console} Unit
main =
  let n = counted 0
  putLine ("lines: " <> show n)
```

```sh
printf 'a\nb\nc\n' | adamas run lines.adamas    # lines: 3
```

At the end of input `readLine` answers `None`; an empty line is `Some ""`.

A **file** is read and written inside a scope: `reading path k` opens it and
runs `k`, and inside `k` the lines are handed out by `nextLine`; `writing` and
`appending` are the same for `emit` and `emitLine`. The file is closed on the
exit from `k`, including an abrupt one. The callback may print to the console
and open a second file - this is how a file is copied:

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

A failure is `Except IOError` (`CannotOpen`, `CannotWrite`). Caught by nobody,
it is printed to stderr and ends the program with exit code 1; `attempt` from
`Std.Except` catches it. The text the program itself prints is not localized
yet and is Russian: `ошибка: не открывается файл in.txt` ("error: cannot open
file in.txt").

The meaning of operations is given by a handler, not by the declaration: a
test may run the same program with its own `Console` handler - with prepared
input and no console. An example is
`tests/golden/eval/console-scripted.adamas`.

## 7. Diagnostics in the editor

Both plugins are clients of the same `adamas-lsp` and show the same errors
that `adamas check` prints, at the exact position. There is no syntax
highlighting yet. Details and Neovim are in
[`editors/README.md`](../editors/README.md).

The quick path for VS Code is running the extension from source:

```sh
cd /path/to/adamas/editors/vscode && npm ci
code --extensionDevelopmentPath="/path/to/adamas/editors/vscode" ~/hello-adamas
```

The server is looked up on `PATH` under the name `adamas-lsp`; how to install
it permanently is said in [section 1](#install-permanently). If `code` was not
started from a shell with that `PATH` set (for example, from a desktop menu),
give the absolute path in the user settings:

```json
"adamas.server.path": "/path/to/adamas/target/release/adamas-lsp"
```

To check that the server is alive, break the program: in `Main.adamas`
replace `name <> "!"` with `nam <> "!"`, and the underline appears exactly on
`nam`, with the same text that `adamas check` would give.

To install the extension permanently rather than in development mode:

```sh
cd /path/to/adamas/editors/vscode
npx @vscode/vsce package
code --install-extension adamas-0.0.0.vsix
```

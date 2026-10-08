# Contributing

## Language

The outer layer of the project - `README.md`, `adamas-concept.md`,
`docs/getting-started.md`, the examples in `docs/examples/`, this file - is
written in English. The working language of the project is Russian: the
design document `adamas-design.md` with its decision log, the phase plans and
track notes in `docs/`, and the comments in the code. `adamas-concept.md` is
the English summary of the design; section numbers (§) everywhere refer to the
design document. Compiler messages are localized: Russian and English, chosen
by the user's locale.

## Environment

The canonical way is the Nix flake:

```sh
nix develop
```

It provides the toolchain from `rust-toolchain.toml` plus `cargo-insta`
(snapshot tests), `cargo-nextest` (the test runner) and `cargo-mutants`
(mutation testing of critical paths).

Plus **two** LLVM toolchains: the regular one on `PATH` and the minimum
supported one, whose directory is in `ADAMAS_LLVM_MIN_BIN` (the regular one is
in `ADAMAS_LLVM_BIN`). The binding to LLVM is textual, so the backend needs the
`llvm-as`, `opt` and `llc` binaries, not the library; the second toolchain is
not a luxury but a check of the rule "generate a conservative subset of IR" -
it is run on the minimum version the same way MSRV is checked
(`crates/adamas-codegen/tests/llvm.rs`). Without Nix both variables must be set
by hand, otherwise the tools are looked up on `PATH`, and their absence fails
the test.

Plus **two editors**, there for the same reason as the second LLVM toolchain:
the witness "an `.adamas` file opens and the underline is in its place" is a
run of a real editor headless, not a screenshot. `ADAMAS_NVIM` names `nvim`,
`ADAMAS_VSCODE` the VSCodium Electron binary, `ADAMAS_VSCODE_CLI` its CLI
wrapper (it installs the `.vsix`), `ADAMAS_VSCE` the packager. The extension's
dependencies are installed by `npm ci` in `editors/vscode`; entering the dev
shell does it by itself. When a tool is missing, the variable is set to
`absent`, and the run says so; a variable not set at all fails the test
(`crates/adamas-lsp/tests/editors.rs`).

Plus `git` - the package manager (§7.3) works with it: `adamas-pkg` calls it
as a subprocess to fetch a dependency by URL and commit. Unlike LLVM and the
editors, it deliberately has no variable: `git` here is the user's tool, not a
witness, and it is taken from `PATH` - the same way it will be taken by anyone
who builds an Adamas project. The fetching tests
(`crates/adamas-cli/tests/project.rs`) do not pass without it; they need no
network - the source is created by `git init` next to them and addressed by
`file://`.

`nix build` builds both binaries in release and runs the tests in an isolated
sandbox. **CI does not check this path** - Nix takes no part there at all - so
run it by hand: before a release and whenever a crate with system dependencies
is added (it will need `buildInputs`).

Without Nix rustup is enough: it fetches the version and components from
`rust-toolchain.toml` by itself. The toolchain version is set in exactly one
place - that file; both the flake and CI read it.

MSRV (`workspace.package.rust-version`, duplicated in `clippy.toml`) is 1.85,
exactly what `clap` and `proptest` require. Raising it is a deliberate
decision, not a side effect of `cargo update`: if updating a dependency drags
the MSRV along, either stay on the previous version of the dependency or raise
the MSRV in a separate commit with an entry in the decision log. `Cargo.lock`
is committed, and CI calls cargo with `--locked`, so nothing can drift
silently.

## Checks before a commit

```sh
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace --lib --bins --tests
cargo test --workspace --benches
cargo test --workspace --doc
```

Tests run through `nextest`: every test is its own process, and the run lasts
as long as the longest test, not the sum of the tests of one binary.
Benchmarks are a separate command: criterion binaries do not answer `--list`
in the nextest format. A plain `cargo test --workspace --all-targets` passes
too, only slower.

This is exactly what CI runs (`.github/workflows/ci.yml`), plus a build on
macOS aarch64 and the MSRV check. In CI benchmarks are only built and run
once - see below.

## Repository layout

```
adamas-design.md              the source of truth on design (in Russian)
adamas-concept.md             its summary for an outside reader (in English)
crates/adamas-core/           the core: core language, type checker
crates/adamas-parser/         the surface language: lexer, layout, parser
crates/adamas-elab/           surface language to core terms; outside the TCB
crates/adamas-interp/         running core terms: a machine with handlers
crates/adamas-codegen/        backend IR, Perceus, two emitters: C and LLVM
crates/adamas-runtime/        the runtime in C: objects, regions, fibers, RC
crates/adamas-pkg/            the project manifest, git dependencies, the lock file
crates/adamas-l10n/           message catalogs and the user's language
crates/adamas-cli/            the `adamas` driver
crates/adamas-lsp/            the LSP server: diagnostics, hover, hints
crates/adamas-warmup-stlc/    the Phase 0 training STLC+HM; the core does not depend on it
editors/nvim/                 the Neovim plugin
editors/vscode/               the VS Code extension
docs/getting-started.md       from zero to a running program
docs/examples/                Adamas code examples, part of the gate
docs/measurements/            measurements: conditions, spread, how to reproduce
docs/reading-notes/           notes on papers
tests/golden/                 language fixtures shared by several crates
.github/workflows/            CI and benchmarks
```

Rust integration tests live in `crates/<crate>/tests/`, benchmarks in
`crates/<crate>/benches/`: cargo picks these directories up only inside a
package, and at the root of a virtual workspace they would be dead weight. The
root `tests/golden/` is not Rust code but data (see `tests/golden/README.md`).

## Tests

- Unit tests of pure functions - inline `#[cfg(test)] mod tests`.
- Integration tests - `crates/<crate>/tests/`. A file is named after the
  feature (`source_location.rs`, `cli_check.rs`) and collects its scenarios;
  functions have no `test_` prefix, the attribute already plays its role.
  Every file in `tests/` is a separate crate with its own linking, so there is
  no file per scenario.
- Snapshot tests (`insta`) - for the output of the type checker and
  elaboration. Updating: `cargo insta review` (or `cargo insta test
  --accept`). `*.snap.new` files are not committed.
- Property-based tests (`proptest`) - for core algorithms: the parser's round
  trip, normalization, resolution of positions.
- A built program prints the block counters (`блоков выдано N, живо M`,
  "N blocks issued, M alive") only under `ADAMAS_STATS`: the leak and reuse
  witnesses live on them. The suite and the benchmarks get the variable from
  `.cargo/config.toml`; a binary started by hand does not.

For type-theory-heavy code prefer property and snapshot tests to bespoke unit
tests: the latter easily start testing the implementation instead of the
specification.

## Benchmarks

```sh
cargo bench --workspace
```

CI checks only that they build and runs them once (`cargo bench -- --test`).
The bench `adamas-codegen/benches/native.rs` measures the §6 line against a
Rust neighbour, and a single `cargo bench` gives a number for it that will not
repeat tomorrow: the conditions of validity - five runs, pinning to a core,
`--noplot --discard-baseline` - are listed in the bench's header, under the
"Методика" (method) section. The recorded numbers are in
`docs/measurements/workload-gap/`: the gap with the Rust neighbour on the
track Z workloads, the conditions, the commands to reproduce and what each
line was checked against for meaning.
There is no history of measurements and no publication of it: the core
(`nbe`, `check`), parsing (`pipeline`) and the driver (`startup`) have
benchmarks, but there is nowhere to keep their series yet. The condition for
raising it - the first core benchmark - is met; the workflow itself waits for
a decision on where the series lives. The one-off numbers of the warm-up are
recorded in `docs/warmup-retrospective.md`.

## Code style

- `cargo fmt --check` and `cargo clippy -- -D warnings` must pass.
- Modules of 200-500 lines; when one grows, split it.
- `pub` only where needed; everything else `pub(crate)` or private.
- Domain errors inside the compiler are `thiserror` enums, `anyhow` in the CLI
  layer. Diagnostics for the language's user are a separate infrastructure
  with spans (§7.4), not the same error types.
- Text for the language's user is not written in the code as a string: it
  lives in the catalogs `crates/adamas-l10n/locales/{ru,en}/*.ftl`, and the
  code calls `adamas_l10n::tr!("id", arg = …)`, in a `thiserror` attribute
  `#[error("{}", adamas_l10n::tr!("id", arg = .field))]`. A new message is
  written into both catalogs at once; `cargo test -p adamas-l10n` checks that
  the catalogs name the same things and that every `tr!` in the code is in
  them. A number that selects the form of a word is passed as
  `adamas_l10n::count(n)`.
- User errors do not panic. `panic!` is only for an internal invariant. This
  is enforced by `clippy::unwrap_used` / `expect_used` (allowed in tests).
- Profile before optimizing. The type checker must be fast from the first
  line, but guesses about what exactly is slow are usually wrong.

## The design document

`adamas-design.md` is the specification. Code that contradicts it is not
accepted: first a discussion and an edit of the document, then the
implementation.

Every significant design change comes with an entry in the decision log
(§13): the date `YYYY-MM-DD`, the affected sections, what was / what became /
the reasoning, the rejected alternatives with their reasons.

Open questions are collected in §10 - before deciding a contested small
question, check whether it is recorded there.

## Commits and pull requests

Conventional commits: `feat:`, `fix:`, `refactor:`, `test:`, `docs:`,
`chore:`. The first line is up to 72 characters. The body says what and why,
not a retelling of the diff, with a reference to the design sections:
`Implements §3.2 (predicative universes)`.

A pull request description has three parts: **What / Why / How to check**.
Plus links to the affected sections and a list of what was deliberately left
for later.

Large changes are decomposed: one commit is one logical unit.
Implementation, formatting and unrelated cleanup are not mixed.

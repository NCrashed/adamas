# Adamas

A research-level prototype of a functional programming language: dependent
types and linearity in one system (Quantitative Type Theory), algebraic effects
with handlers, structured concurrency on stack-segment fibers, Perceus
reference counting with FBIP, memory regions and SIMD as first-class
constructs.

The goal is to show that systems-friendly semantics is reachable without
"dropping down to C": one language for applied functional code, systems
programming, and type-heavy research.

**Stage: phases 0–8 are done; phase 9, the toolchain, is under way.** A program
travels the whole path — text, tree, core terms, type checking — and then runs
three ways: `adamas eval` interprets it, and `adamas build` compiles it through
either backend, C or LLVM. All three must answer the *same thing*, and a
disagreement fails the build: that contract is checked on every gate run over
182 of the 183 corpus programs. The one program neither backend takes returns a
function, and printing one is a question about the language, not about a
backend.

The largest program so far is a playable Asteroids on SDL2
([`demo/asteroids/`](demo/asteroids/)): about 900 lines of Adamas calling SDL
through the C FFI, with records, flat arrays, and entities indexed by the set of
components they carry. `adamas run` inside that directory starts it.

See the [roadmap](adamas-design.md#9-roadmap) — 10 phases, ~3–5 years to a
research-grade prototype.

Note on language: the design document, the code comments and the compiler's
diagnostics are in Russian. This README is the English entry point.

## Hello, world

```adamas
import Std.IO (Console, putLine)

main : {Console} Unit
main = putLine "Hello, world"
```

```sh
adamas run hello.adamas      # compiles through C and runs
adamas eval hello.adamas     # the same through the interpreter
```

`{Console}` in the type says what `main` does to the world, and only that: it
prints, it does not touch files. A `main` whose type carries labels from
`Std.IO` runs under the library's handler, so the program prints itself and
the driver adds nothing to standard output.

Counting the lines on standard input reads an operation and recurses; the
prelude brings `String`, `<>`, `show` and `==` without an import:

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

Files are read and written inside a scope that closes them on every exit,
including an error: `reading "in.txt" k` answers `nextLine` with the file's
lines inside `k`, `writing` and `appending` do the same for `emit`. A failure
is `Except IOError`; nobody catching it means a message on standard error and
exit code 1. `adamas doc Std.IO` prints the module's interface.

Both programs are [`docs/examples/hello.adamas`](docs/examples/hello.adamas) and
[`docs/examples/lines.adamas`](docs/examples/lines.adamas), checked and run by the gate. To
build the `adamas` binary, see [Building](#building); to start a project with
tests, [`docs/getting-started.md`](docs/getting-started.md).

## Examples

Every example below is checked and run by the current compiler.

### Everyday code

Records, operators from the prelude, `if`, and a C function called directly:

```adamas
type Ship = {x : Int32, y : Int32, dir : Int32}

extern "C" pure fn cos : Float64 -> Float64

-- | Nearest integer, half away from zero.
rounded : Float64 -> Int32
rounded v = if v < 0.0 then float64ToInt32 (v - 0.5) else float64ToInt32 (v + 0.5)

-- | Cosine of a sixteenth of a turn, scaled by 256.
dirX : Int32 -> Int32
dirX d = rounded (cos (int32ToFloat64 d * 0.39269908169872414) * 256.0)

step : Ship -> Ship
step s = {s | x = s.x + dirX s.dir}

main : Int32
main =
  let moved = step (step {x = 0, y = 0, dir = 1})
  if moved.x > 400 && moved.y == 0 then moved.x else 0
```

This answers `474`. A foreign call carries the `Foreign` effect, so physics
written through `cos` would stop being pure; `pure` after the ABI string is the
author's claim that it is, taken on trust like the signature itself. `Ship`
has only primitive fields, so both backends keep it flat: the program allocates
nothing on the heap.

### Dependent types

Indices live in types, so the impossible case has no branch and no runtime
check:

```adamas
data Vect : Nat -> Type where
  Nil : Vect Zero
  Cons : (0 n : Nat) -> Bool -> Vect n -> Vect (Succ n)

-- Total by construction: `Vect (Succ n)` rules out the empty vector, so
-- `head` has one clause and cannot fail.
head : (0 n : Nat) -> Vect (Succ n) -> Bool
head n (Cons k x xs) = x
```

The `0` on `n` is a multiplicity: the index is erased and does not exist at
runtime. Multiplicities are part of the type system, not an annotation on the
side — `0` for erased, `1` for linear, `ω` for unrestricted.

### Resources: closed exactly once, on every path

```adamas
resource File where
  Open : File
  closeFile : (1 h : File) -> {Log} Bool
  closeFile h =
    note 9
    True

-- The handle is not mentioned again, so the compiler inserts `closeFile` at
-- the end of the scope. Nothing is written by hand.
work : File -> {Log} Bool
work h =
  note 1
  True
```

Running it prints `[1, 9]` — the body, then the destructor. The same holds when
the computation is abandoned by an effect that never resumes: unwinding finds
the destructor and runs it there.

Using the handle twice is a type error, underlined at the second use:

```adamas
twice : File -> Bool
twice h = andL (closeFile h) (closeFile h)
--                                      ^ `h` объявлена с кратностью 1, а использована ω
```

### Algebraic effects

A signature says what a computation may do before anyone runs it:

```adamas
effect State where
  get : Nat
  put : Nat -> Unit

counter : {State} Nat
counter =
  let a : Nat = get
  put (a + 1)
  let b : Nat = get
  a + b
```

A call whose result nobody reads is written as a line of its own; a `let` whose
name is never read draws a warning.

The handler carries the state itself. `state s0` declares the initial value,
`state` inside a branch means the current one, and `resume` takes two arguments
— the answer and the state to continue with:

```adamas
total : Nat
total = handle counter with
  state 10
  return v -> v
  get -> resume state state
  put x -> resume MkUnit x
```

This evaluates to `21` — that is `10 + 11`. Handlers are deep: a handler
reinstalls itself on the continuation of an operation that passed it by, and
`mask` sends an operation past the nearest handler of its label when that is
what you mean.

### Structured concurrency

Fibers are segments of the same stack: yielding moves pointers, nothing is
copied. No new syntax is needed — the author declares an effect and writes the
types, and the machine supplies the bodies:

```adamas
effect Async where
  suspend : Unit
  spawnDetached : ({Async, Log} Unit) -> Unit

withNursery : ({Async, Log} Unit) -> {Log} Unit

worker : Nat -> {Async, Log} Unit
worker tag =
  note tag
  suspend
  note (Succ tag)

program : {Async, Log} Unit
program =
  spawnDetached (worker 1)
  worker 3
```

The trace is `[3, 1, 4, 2]`: both workers mark, yield, and finish in turn. The
nursery awaits everyone — structured concurrency in the Trio sense. A resource
held inside a task is closed even when the nursery is abandoned from the
outside, and `drop` on an unawaited task cancels its fiber.

## What works today

```
crates/adamas-core        QTT core: terms, evaluation, type checking,
                          clause compilation, totality, universes
crates/adamas-parser      lexer, significant indentation, parser, printer
crates/adamas-elab        surface language into core terms; outside the TCB
crates/adamas-interp      execution with effect handlers, resources, fibers
crates/adamas-codegen     backend IR carrying multiplicity and uniqueness,
                          Perceus insertion, and two emitters: C and LLVM
crates/adamas-runtime     the C runtime: objects, regions, fibers, atomic RC
crates/adamas-pkg         the project manifest, git dependencies, lockfile
crates/adamas-cli         the `adamas` driver: `new`, `check`, `build`, `run`,
                          `fmt`, `doc`, `test` and `eval`, over a single file
                          or a project
crates/adamas-lsp         the language server: diagnostics, hover, go to
                          definition, semantic tokens and inlay hints
crates/adamas-warmup-stlc a phase-0 exercise: STLC + HM, standalone
```

Roughly 173k lines of Rust, 5.6k lines of C in the runtime, and 1700 tests. What
the language accepts is visible in [`tests/golden/`](tests/golden/): 411
fixtures — programs that must be accepted, programs that must be refused with a
recorded message, and programs whose value is recorded too.

Beyond the examples above: type classes with superclasses, default methods
(checked once in the class, expanded in each instance) and
multiplicity-polymorphic methods; modules, signatures, functors, sealing and
implicit functor parameters; propositional equality with `subst` and `sym`,
decidability, and proof irrelevance through truncation; a 600-line prelude
(numeric classes and operators, `Eq` and `Ord` with `==`, `<` and friends,
short-circuit `&&` and `||`, `String` with `<>` and `Show`) and a 942-line interpreter for a small object
language, both written in Adamas and run by `adamas eval`.

The toolchain has caught up with the compiler: `adamas fmt` rewrites a file to
its canonical form through the same printer the parser owns, `adamas doc`
prints the interface a module exports, and the language server shows what the
compiler knows but the text does not say — where a definition allocates and the
chain that leads there, which cell a construction reuses, where a resource is
taken and where its destructor will be inserted, and which label a handler
discharges.

Diagnostics speak about the program rather than the elaborator: a refusal is
underlined at the use that caused it — the second `resume`, the branch of a
`case`, the implicit argument nobody could infer — and types in the message are
printed as values, not as the internal lambdas that solved them. Accepted
programs get warnings for a `let`, lambda or branch binding that is never read,
and for an imported name that is never used; a name starting with `_` is read
as "unused on purpose".

Elaboration is a separate crate because it is not in the trusted base: it
produces an ordinary core term, and `check` establishes its correctness.

## Two backends, and what measuring them showed

Between the core and either emitter sits one representation that carries
multiplicity and uniqueness explicitly, so the LLVM backend is a second
*emitter*, not a second compiler — a test reads both emitters and fails if
either reaches for a core term. The C backend goes through gcc; the LLVM one
writes textual `.ll` and hands it to `llvm-as`, `opt` and `llc`, which keeps the
toolchain unpinned to an LLVM major at the cost of about 6% of backend time.

Both take the same 155 of 156 corpus programs. Where they differ is speed, and
the numbers are in [`docs/measurements/`](docs/measurements/) with the command
that reproduces each row:

| workload | LLVM against C |
|---|---|
| scalar arithmetic | 1.00 |
| allocation-heavy symbolic code | 0.98 |
| FBIP loop | 0.92 |
| pass over a flat `Float32` column | 0.87 |
| the same pass, `Simd 8 Float32` window | **0.61** |

The phase was argued for on two mechanisms — aliasing facts from QTT, and
collapsing reference-count traffic after inlining. **Measurement rejected both.**
Six aliasing metadata were tried and every one earned zero instructions; the
only exception found later was `align` on a vector access, which changes the
instruction (`movaps` for `movups`) without changing the time. The RC pass finds
no collapsible pair at all on these workloads. What the gap above comes from is
inlining and, on the last two rows, the freedom a backend has when a program
touches memory — not from the representation being richer.

What the phase did buy is guarantees rather than speed: `musttail` makes the
tail-call promise a property of the backend instead of a build flag, DWARF steps
through `.adamas` lines, floating-point contraction is forbidden in the IR
itself, and `Simd` reaches memory.

The warm-up is an exercise from phase 0, not part of the compiler — the core
does not depend on it. What it taught is in
[`docs/warmup-retrospective.md`](docs/warmup-retrospective.md).

## Documents

| Document | What is inside |
|---|---|
| [`adamas-concept.md`](adamas-concept.md) | The design distilled for an outside reader: the thesis, the principles, the core mechanisms and what already runs — without the coordination sections. In Russian. Start here if you want the language rather than the project. |
| [`adamas-design.md`](adamas-design.md) | The design document — the single source of truth for design decisions, together with the open questions and the decision log. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | How to build, how to run the checks, the rules for code and commits. |
| [`docs/getting-started.md`](docs/getting-started.md) | From nothing to a running program: `adamas new`, every driver command, a second module, the prelude, diagnostics in the editor. In Russian, like the rest of `docs/`. |
| [`docs/reading-notes/`](docs/reading-notes/) | Notes on the key papers (QTT, Perceus, effect handlers). |
| [`tests/golden/`](tests/golden/) | Adamas programs the compiler accepts today, with their expected output. |
| [`docs/examples/`](docs/examples/) | Six programs: the hello world and line counter from above, then four chosen for what makes the language *different* — multiplicities, effects, regions, FFI. Each is checked, run against a recorded answer, documented and kept canonical by the gate. |
| [`demo/asteroids/`](demo/asteroids/) | Asteroids on SDL2: the largest program in the repository, and the one that drives what the language fixes next. Needs SDL2 (the Nix shell has it); `adamas run` in that directory. |
| [`docs/phase*-plan.md`](docs/) | How each phase is cut into tracks: what parallelises, what does not, and what counts as done. Alongside them, one notes file per track with what was measured and what the measurement rejected. |
| [`docs/measurements/`](docs/measurements/) | Every performance claim in this README, with its conditions, its spread, and one command per row. Where a number was retracted, the retraction is there too. |

A quick way into the design: §1–2 (vision and principles) → §3 (semantic core)
→ §4.1 (syntax). Contested details live in §10.

## Building

With Nix (the toolchain and dev tools come along):

```sh
nix develop
cargo test --workspace --all-targets
```

Without Nix you need rustup — the version and components are taken from
`rust-toolchain.toml` automatically:

```sh
cargo test --workspace --all-targets
```

Try an example:

```sh
cargo run -p adamas-cli -- run docs/examples/hello.adamas
echo -e "a\nb" | cargo run -q -p adamas-cli -- eval docs/examples/lines.adamas
```

To start a project of your own instead, see
[`docs/getting-started.md`](docs/getting-started.md).

## License

Dual-licensed, at your option:

- MIT ([`LICENSE-MIT`](LICENSE-MIT))
- Apache License 2.0 ([`LICENSE-APACHE`](LICENSE-APACHE))

Unless you state otherwise, any contribution intentionally submitted for
inclusion in this project is licensed on the same terms, without any additional
conditions.

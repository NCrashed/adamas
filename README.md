| [`docs/examples/`](docs/examples/) | Illustrations of forms the implementation has not reached yet. |
| [`docs/phase6-plan.md`](docs/phase6-plan.md) | How phase 6 is cut into tracks: what parallelises, what does not, and what counts as done. |
# Adamas

A research-level prototype of a functional programming language: dependent
types and linearity in one system (Quantitative Type Theory), algebraic effects
with handlers, structured concurrency on stack-segment fibers, Perceus
reference counting with FBIP, memory regions and SIMD as first-class
constructs.

The goal is to show that systems-friendly semantics is reachable without
"dropping down to C": one language for applied functional code, systems
programming, and type-heavy research.

**Stage: phases 0–5 are done.** A program travels the whole path — text, tree,
core terms, type checking, execution: `adamas check` type-checks it and `adamas
eval` runs it, effects and all. Phase 6 is codegen through C with Perceus. See
the [roadmap](adamas-design.md#9-roadmap) — 10 phases, ~3–5 years to a
research-grade prototype.

Note on language: the design document, the code comments and the compiler's
diagnostics are in Russian. This README is the English entry point.

## Examples

Every example below is checked and run by the current compiler.

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

Using the handle twice is a type error, and the message names the reason:

```adamas
twice : File -> Bool
twice h = andL (closeFile h) (closeFile h)
--        `h` объявлена с кратностью 1, а использована ω
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
  let u : Unit = put (a + 1)
  let b : Nat = get
  a + b
```

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
  let a : Unit = note tag
  let s : Unit = suspend
  note (Succ tag)

program : {Async, Log} Unit
program =
  let u : Unit = spawnDetached (worker 1)
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
crates/adamas-cli         the `adamas` driver: `check` and `eval`
crates/adamas-lsp         a stub; the language server is a later phase
crates/adamas-warmup-stlc a phase-0 exercise: STLC + HM, standalone
```

Roughly 70k lines of Rust and 900 tests. What the language accepts is visible
in [`tests/golden/`](tests/golden/): 118 fixtures — programs that must be
accepted, programs that must be refused with a recorded message, and programs
whose value is recorded too.

Beyond the examples above: type classes with superclasses, defaults and
multiplicity-polymorphic methods; modules, signatures, functors, sealing and
implicit functor parameters; propositional equality with `subst` and `sym`,
decidability, and proof irrelevance through truncation; a 297-line prelude and
a 473-line interpreter for a small object language, both written in Adamas and
run by `adamas eval`.

Elaboration is a separate crate because it is not in the trusted base: it
produces an ordinary core term, and `check` establishes its correctness.

The warm-up is an exercise from phase 0, not part of the compiler — the core
does not depend on it. What it taught is in
[`docs/warmup-retrospective.md`](docs/warmup-retrospective.md).

## Documents

| Document | What is inside |
|---|---|
| [`adamas-design.md`](adamas-design.md) | The design document — the single source of truth for design decisions, together with the open questions and the decision log. |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | How to build, how to run the checks, the rules for code and commits. |
| [`docs/reading-notes/`](docs/reading-notes/) | Notes on the key papers (QTT, Perceus, effect handlers). |
| [`tests/golden/`](tests/golden/) | Adamas programs the compiler accepts today, with their expected output. |
| [`docs/examples/`](docs/examples/) | Illustrations of forms the implementation has not reached yet. |

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
cargo run -p adamas-cli -- check tests/golden/eval/state.adamas
cargo run -p adamas-cli -- eval tests/golden/eval/state.adamas main
```

## License

Dual-licensed, at your option:

- MIT ([`LICENSE-MIT`](LICENSE-MIT))
- Apache License 2.0 ([`LICENSE-APACHE`](LICENSE-APACHE))

Unless you state otherwise, any contribution intentionally submitted for
inclusion in this project is licensed on the same terms, without any additional
conditions.

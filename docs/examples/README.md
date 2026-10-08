# Adamas code examples

Six programs. The first two are where one starts: printing and counting the
lines of input. The other four show what makes the language **different** —
not what is easier to write:

| File | About |
|---|---|
| `hello.adamas` | the first program: `main : {Console} Unit` prints through `Std.IO` (§3.4, §4.4) |
| `lines.adamas` | counting input lines: `case readLine of`, text concatenation and `show` from the prelude (§4.3, §4.4) |
| `multiplicity.adamas` | multiplicities `0`/`1`/`ω`, erased indices, a resource with an automatic destructor (§3.2, §3.3) |
| `effects.adamas` | algebraic effects: the row in the type, the handler decides the meaning, one computation under two handlers (§3.4) |
| `regions.adamas` | a region as a label in the type: a reference does not outlive its block (§3.6) |
| `ffi.adamas` | a level-1 foreign symbol, the boundary marked by its own effect (§5.3) |

Each reads top to bottom: the header says how it differs from Haskell, OCaml
or Rust, and then comes the code with `-- |` documentation blocks.

Section numbers (§) refer to the design document, `adamas-design.md`; it is
written in Russian, and [`adamas-concept.md`](../../adamas-concept.md) is its
summary in English.

## They are checked by running

Every example is part of the gate (`crates/adamas-cli/tests/examples.rs`) and
passes four checks: `adamas check`, `adamas eval` with a **recorded answer**,
`adamas doc` (an example must be documented) and `adamas fmt --check`.

This lifts the condition under which the directory used to stay empty: an
unchecked copy of §4 drifts from the original the faster the longer it is. The
cost was measured on a neighbouring stack — the §5.3 examples were corrected
seven times during Phase 8, and every divergence was found by running, not by
eye. The condition was lifted not by an argument but by a run: these examples
have no way left to rot silently.

To see an example's documentation:

```sh
adamas doc docs/examples/effects.adamas
```

## Where else things live

`tests/golden/` is the corpus: programs, refusals and evaluations, each under
a snapshot. It is written for the compiler and reads as a list of cases; this
directory is written for a person and reads as text.

The syntax is not duplicated here — there is one source of truth, §4 of the
design. §4.1 is the basic syntax, effects and handlers; §4.2 records; §4.4 the
prelude, operators and fixities; §4.8 modules and ordered scoping. An example
that diverges from §4 is a bug in the example.

# Adamas - the concept of the language

> A summary of the design document for an outside reader: what this language
> is, what it stands on, what it looks like and what of it already works. The
> coordination sections, the decision log and the list of open questions stay
> in `adamas-design.md` (written in Russian) - here are only the decisions
> themselves and their reasoning.

---

## 1. The thesis

Functional clarity and systems control are one semantics, not two languages in
one.

Adamas is a research prototype of a statically typed functional language with
a predictable cost model, dependent types, linearity and algebraic effects. It
aims at the clarity of Haskell and OCaml and at systems programming in the
spirit of Rust and Zig at the same time, and on principle does not separate
these worlds, but shows that a design honest to both sides is possible.

One semantics for all tasks: QTT + resources + region memory + effects is a
coherent system, not "a feature for one class and a crutch for another".

## 2. Who it is for

Programmers who know Haskell, Rust, OCaml or Idris and want to see what comes
out of synthesizing their strengths without the historical baggage. This is
not "a language for everyone" - it is a language laboratory with
production-oriented semantics.

Three classes of tasks covered by one core:

- **Applied functional code.** Data pipelines, parsers and interpreters,
  symbolic processing, business logic with effects.
- **Systems programming.** Hot loops, zero-allocation paths, SIMD workloads,
  embedded, network dataplanes - where today one goes to Rust or C.
- **Type-heavy research.** Dependently typed libraries, DSLs with
  compile-time checks, protocol-correct code, formal verification of
  properties on proof terms.

**What the project does not do.** It does not replace an existing language in
production. It does not cover the whole surface of an industrial language: no
complete standard library and no backends for every architecture. It does not
aim at full formal verification of the compiler itself. WebAssembly and GPU
offload are not goals of the prototype, but the design has been checked for
compatibility with them.

## 3. Six principles

1. **A predictable cost model.** Looking at the code, the programmer
   understands its order of execution and its allocations without a
   profiler. No hidden laziness, no implicit allocations.
2. **An honest type.** The type of a function reflects what it does: effects
   in the type, linearity in the type, totality in the type when declared.
3. **Erasure as first-class.** What only static checking needs is physically
   absent from the compiled code. No "virtual tax" on type safety.
4. **Discipline over freedom.** Between flexibility and predictability,
   predictability is chosen. This language is harder to write and easier to
   understand.
5. **Pragmatic theory.** From type theory one takes what pays off in
   practice. This is not building Coq and not building Agda.
6. **Systems code is first-class.** There is no need to go to another language
   for zero-alloc loops, SIMD, direct FFI or control over memory. Region
   memory, SIMD types and the direct C ABI are part of the language, not
   crutches on top.

---

## 4. The semantic core

### 4.1 Strict evaluation

Strict evaluation order by default; `Lazy a` for memoized deferred
computations is constructed explicitly. This removes a class of bugs with
space leaks, makes the order predictable, simplifies interop with the C ABI
and allows aggressive inlining without loss of semantics. The price is named:
elegant lazy programs need explicit constructs.

Laziness by default is the main architectural difference from Haskell, and it
was rejected deliberately: the dominant class of bugs there is tied precisely
to unexpected laziness.

### 4.2 Quantitative Type Theory

The core is based on QTT (Atkey 2018, implemented in Idris 2). Three
multiplicities:

| Multiplicity | Meaning | Consequence |
|---|---|---|
| `0` | the value exists only during checking | erased before execution |
| `1` | used exactly once | linearity, resources |
| `ω` | any number of times | ordinary code, the default |

One notion instead of three mechanisms: dependent types without a runtime cost
(erased arguments), linear types as a special case, ordinary functions as the
default.

Universes are predicative (`Type : Type 1 : ...`). An impredicative `Type`
gives Girard's paradox and with it the possibility to prove `False`, which
destroys the principle of the honest type; the practical need for polymorphic
library code is covered by universe polymorphism, where the elaborator infers
the levels.

Effect rows are a separate sort next to `Type` and `Level`, built after its
pattern: a closed language of expressions, a normal form, decidable equality,
multiplicity `0`. Rows are erased on a par with levels; the runtime remnant of
an effect is an evidence vector introduced by lowering.

### 4.3 Linearity, erasure, resources

Linearity is not attached from the side - it is multiplicity `1` from the
core, and erasure is not an optimization but part of the semantics.

On top of this stands the **resource type**: a binding of such a type is
linear by construction, and the destructor is called by the compiler on exit
from the scope - on **every** exit, including the one where the computation is
cut short by an effect. The destructor's row is an obligation of the holder:
if closing produces an effect, it is written in its type, and the resource
cannot be closed silently.

### 4.4 Effects: row polymorphism and handlers

Effects are row-polymorphic, processed by handlers and compiled by the
evidence translation scheme (Leijen 2017, Xie et al. 2020). They replace
monad transformer stacks entirely.

The row stands in the type **next to the answer**: `{Ask, Log} Nat` means
"yields a `Nat` and may ask and record on the way". A combination is written
with a comma, and adding a second label rewrites nothing. What an operation
means is decided by the handler, not by the declaration - so the same
computation under two handlers gives two different answers without a single
edit.

A handler may not call `resume` - then the computation is cut short, and the
answer is what the branch wrote. This is how an abort is expressed: neither
exceptions nor a special form are needed. `handleMulti` calls `resume` several
times - backtracking, parser combinators, nondeterminism.

### 4.5 Modules and implicits

One system in which ML modules with functors and type classes are two points
on one scale. The core holds one construct (a module is a named set of types
and values with an optional signature), and the surface gives different
keywords for different cases.

Ascription by a signature is either transparent (`: Sig` - conformance is
checked, the representation is visible) or sealing (`:> Sig` - checked and
hidden: a name the signature does not mention cannot be written from outside
at all).

Global coherence of type classes as the default is rejected - scoped implicits
instead; global uniqueness stays available as an opt-in per class.

### 4.6 Region memory

The main memory management strategy is Perceus. Where zero-alloc loops,
isolated allocations, a specific alignment or explicit control over placement
are needed, **regions** are introduced: a pluggable mechanism of alternative
allocators, where a region is a resource with a strategy, and allocation in it
goes through an effect.

A reference `Ref r a` is tied to its region by a label in the type, and it
cannot outlive it. This is held not by a separate rule but by two mechanisms
already present: the label is bound in the domain of whoever opens the region,
so the answer of the body may not mention it; and the allocation effect cannot
be discharged bypassing the opener, because the operations are lifted from a
sealed module.

### 4.7 Verification of properties

Formal verification is a first-class but optional capability, and at the
start it needs no additional infrastructure: properties are expressed as
types, proofs as programs of multiplicity `0`, that is, erased ones. This is a
direct consequence of QTT and totality, not a separate machine.

---

## 5. What it looks like

### 5.1 What today's compiler checks

The examples below are taken from `docs/examples/` and cut down to the point.
Everything shown is accepted by today's compiler and checked by running; the
files it is taken from are part of the gate in full - they are checked,
evaluated with a recorded answer and compared against the formatter's canon.

**The first program and counting input lines** - the `{Console}` label says
what `main` does to the world, and a `main` with it runs by itself:

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

**An effect, its row and two handlers over one computation:**

```adamas
effect Ask where
  ask : Int64

-- The row `{Ask}` in the type is not decoration: type checking will not let
-- `twice` be called from where `Ask` is not discharged.
twice : {Ask} Int64
twice = ask + ask

-- A constant answer: 7 + 7.
constant : Int64
constant = handle twice with
  return v -> v
  ask -> resume 7

-- The same computation, another handler, another answer. `twice` is not
-- rewritten by a single line.
silent : Int64
silent = handle twice with
  return v -> v
  ask -> resume 0

-- A handler may not call `resume`: the computation is cut short. This is how
-- an abort is written - without exceptions and without a special form.
aborted : Int64
aborted = handle twice with
  return v -> v
  ask -> -1
```

**A resource the compiler closes on every exit:**

```adamas
resource Handle where
  Acquire : Handle
  closeHandle : (1 h : Handle) -> {Log} Bool
  closeHandle h =
    note 9
    True

-- The multiplicity `1` on `h` is not written and not needed: a binding of a
-- resource type is linear by construction. `use h h` cannot be written.
use : Handle -> {Log} Bool
use h =
  note 1
  True
```

**An erased index:**

```adamas
data Vect : Nat -> Type where
  VNil : Vect 0
  VCons : (0 n : Nat) -> Int64 -> Vect n -> Vect (Succ n)

-- `head 0 VNil` cannot be written: the type demands `Succ n`. There is no
-- branch for the empty vector at all - unification of the indices makes it
-- impossible, not "uncovered".
head : (0 n : Nat) -> Vect (Succ n) -> Int64
head n (VCons k x xs) = x
```

### 5.2 What is designed

Sketches from the design document. The form is not final, and part of these
constructs the compiler does not accept yet.

```adamas
-- A resource with automatic cleanup and a row variable lifted by itself
withFile : String -> (File -> {IO} a) -> {IO, Except IOError} a
withFile path k =
  let h = openFile path
  k h
  -- h is closed on exit from the scope, including an abort through Except

-- A parameterized handler: the handler itself carries the state
runState : s -> ({State s} a) -> (s, a)
runState s0 prog = handle prog with
  return v -> (s0, v)
  get -> resume s0 s0
  put s' -> runState s' (resume ())

-- Multi-shot: backtracking
runNondet : ({Nondet} a) -> List a
runNondet prog = handleMulti prog with
  return v -> [v]
  choose -> resume True ++ resume False

-- Classes with superclasses and defaults
class Applicative f when Functor f where
  pure : a -> f a
  ap   : f (a -> b) -> f a -> f b
  map f x = ap (pure f) x
```

### 5.3 Rules of writing visible at once

- **Blocks are indentation only.** Curly braces are taken by other things:
  the effect row (`{IO}`), records (`{ x : Float }`), implicit parameters
  (`{Key : Ord}`).
- **The case of a name decides what it does.** Capitalized - it refers to
  something declared; lowercase - it binds. The rule is local: to read a
  clause one does not need to know what is declared above - and a typo in a
  constructor name is caught where it is written.
- **Multiplicities in signatures are written explicitly** (`(0 n : Nat)`,
  `(1 h : File)`). The contract about erasure and linearity is visible in the
  signature at the price of some noise.

---

## 6. The runtime

### 6.1 Perceus and FBIP

Memory management is reference counting in the style of Perceus:
deallocation is deterministic, there are no collector pauses, and the RC
operations are inserted and optimized by the compiler.

**FBIP** (Functional But In-Place) is a style of execution in which code that
syntactically builds a new structure runs, when its input is unique, as an
in-place mutation without allocation. This is not "the compiler guessed" but a
consequence of the properties of Perceus and of uniqueness analysis, and the
programmer can ask the compiler about it - by an attribute or an editor hint.

### 6.2 Concurrency

Lightweight threads and structured concurrency through a nursery. A nursery is
not an argument of a user function but an effect: the operations are
available inside the scope, and the Scope itself lives in the handler's
closure and is invisible on the surface. This solves the linearity problem of
Scope-as-an-argument, under which several `spawn` calls in a row would be
impossible.

### 6.3 FFI

The direct C ABI as the basis. Foreign calls are marked by the `Foreign`
effect, so the types show who in the program goes outside. Owned resources of
the foreign side are expressed by a resource type, which gives RAII
automatically.

Three levels of support: hand-written `extern` declarations, generation of
bindings, and high-level wrappers.

### 6.4 Data representation

`Flat` is a general class of representation, not a local restriction of a
region boundary. There is one array in the language, `Array n a`, and its
physical representation is determined by the presence of `Flat a`.
Structure-of-Arrays is not introduced as a separate mechanism: it is a record
of arrays, that is, the records already present without additions.

SIMD is a first-class part of the language, not FFI to intrinsics: someone
working with vector processing should not have to go to C.

---

## 7. What is promised on performance

| Scenario | Goal |
|---|---|
| Hot loops with linearity and unboxed numbers | parity with Rust |
| Zero-alloc loops with regions | parity with C |
| A frame function under `@noalloc` | zero heap allocations, checked by the compiler |
| SIMD-heavy code | parity with C + intrinsics |
| Flat containers and hash tables | parity with Rust |
| Typical business code with effects | 1.5-2x Rust |
| Symbol-heavy code | parity with Rust or better |
| Compiler start-up | < 100 ms cold |

The cost of a direct C call is not promised but **measured**: 0.28 ns with the
C lowering and 0.09 ns with LLVM, with zero allocations; on a body with a data
dependency the difference is indistinguishable from zero.

The promise of parity on symbolic code rests on FBIP: typical symbolic
workloads are chains of transformations over trees and lists, and without FBIP
every transformation costs O(n) allocations.

---

## 8. Tools

Building, type checking, the formatter, the documentation generator and the
LSP server are one driver. The server is built at the same time as the
compiler, not as an afterthought, and shows the reader what the compiler knows
but the text does not say: the full type with lifted row variables, the effect
row, the place of a heap allocation and the chain leading to it, the reuse of
a cell, the points where a resource is acquired and its destructor inserted,
the label a handler removes, and the handlers able to discharge an operation.

The hints have one rule: **a hint that lies is worse than a missing one**. So
what is shown is what was computed, not what was wished for, and where the
analysis has no corresponding category, no hint is introduced.

---

## 9. Where it is now

The implementation is in Rust: 10 crates, about 173 thousand lines.

**Done:** type checking and elaboration, the surface language, modules and
classes, effects with handlers, the interpreter, code generation through C and
through LLVM, the Perceus representation, regions, SIMD, FFI of all three
levels. The built-in standard library comes in by an import without a
manifest: the console and files (`Std.IO`) with the file closed on every path,
errors (`Std.Except`); the prelude gives text with `<>`, `show` and `==`. Work
on the tools is under way; the phase milestone - a language usable by an
outside reader - was checked by walking a newcomer's path through the
documentation alone.

A program travels the whole path - text, tree, core terms, type checking -
and then runs three ways: by the interpreter and by two backends. **All three
must answer the same thing**, and a divergence fails the build; the contract
is checked on 182 of the 183 corpus programs on every run.

The corpus: 41 programs, 161 recorded refusals, 183 evaluations with a
recorded answer, plus a separate project of ten files. A run is 142 targets,
about 1700 tests.

The realistic horizon is 3-5 years to the state "works and can be shown",
given that this is a side project with a learning component.

---

## 10. What is explicitly rejected

- **Laziness by default.** The opt-in remains.
- **Monad transformer stacks** - replaced by algebraic effects.
- **Global coherence of type classes as the default** - replaced by scoped
  implicits.
- **Partial functions in the prelude** (`head`, `fromJust` and the rest).
- **Many incompatible String types** - one UTF-8 representative plus views.
- **Records-as-functions** - records are first-class, with row polymorphism.
- **An impredicative `Type`** and Coq's two-sorted scheme.
- **Explicit layout through `{ ; }`** - one block, one way to write it.

---

## 11. Where it comes from

The key supports: Atkey (2018) on QTT; Leijen (2017) and Xie et al. (2020) on
the evidence translation of effects; Reinking, Xie, de Moura, Leijen (2021) on
Perceus and FBIP. The nearest neighbours learned from and checked against are
Idris 2, Koka, Lean 4, Rust, OCaml.

The full list of sources, all open questions with their candidate solutions
and the history of the decisions taken with their reasoning are in
`adamas-design.md`.

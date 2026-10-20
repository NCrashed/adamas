# Mini: a compiler written in Adamas

A compiler for a small ML, from source text to a stack machine that runs it.
It is a project rather than a single file: seven modules, a test module, and
about eleven hundred lines. Where the other examples each show one feature of
the language, this one shows the features working together on a program
written for its result.

```sh
adamas eval docs/examples/compiler          # run with the interpreter
adamas run docs/examples/compiler           # build through C and run
adamas test docs/examples/compiler          # src/Test.adamas
adamas doc docs/examples/compiler           # the documentation of every module
```

`main` compiles and runs eleven sample programs and prints what each one
computed, with its type, or why it was refused:

```text
7 : Int
3628800 : Int
7 : Int
Cons 1 (Cons 4 (Cons 9 Nil)) : List Int
5050 : Int
Some 14 : Option Int
<function> : (a -> a) -> a -> a
error: cannot unify Bool with Int
error: infinite type: a = b -> a
error: cannot unify Int with List a
error: unexpected character '#'
```

## The language it compiles

Mini has integers, booleans, `let` and `let rec`, lambdas, `if`, arithmetic,
and declared data types taken apart with `match`:

```text
data List a = Nil | Cons a (List a);
let rec map f xs = match xs with
  | Nil -> Nil
  | Cons y ys -> Cons (f y) (map f ys)
in map (\x -> x * 2) (Cons 1 (Cons 2 Nil))
```

Types are inferred, Hindley-Milner with let-polymorphism: `let id = \x -> x`
can be used at `Bool` and at `Int` in the same body, a lambda argument cannot.

## The stages

| Module | Stage |
|---|---|
| `Mini.Syntax` | tokens, the tree, types |
| `Mini.Lexer` | text to tokens |
| `Mini.Parser` | tokens to the tree, by recursive descent |
| `Mini.Infer` | type inference: unification and generalisation |
| `Mini.Compile` | the tree to instructions; variables become de Bruijn indices |
| `Mini.Machine` | the stack machine: closures, frames, constructors with tags |
| `Main` | the pipeline and the samples |

## What it shows about Adamas

- **Effects instead of plumbing.** Fresh type variables come from a `Fresh`
  effect whose handler keeps the counter in its state (§3.4): inference reads
  as if the counter were global, and the type of `infer` says that it is not.
  A refusal at any stage is `throw` from `Std.Except`, caught once, by
  `attempt`, in `Main`.
- **Data, matching and deriving.** The tree, the types and the instructions
  are ordinary `data`; `deriving (Eq, Show)` writes equality and printing for
  tokens, operators, patterns and types.
- **Mutual recursion** in `mutual` blocks: the parser's levels, `infer` with
  the arms of a `match`, the printer of types with its argument positions
  (§4.8).
- **Modules and ordered scoping.** Every file is a module, imports name what
  they take, and a definition is visible only below itself (§4.8).
- **One program, three evaluators.** The interpreter, the C backend and the
  LLVM backend print the same eleven lines; the gate checks it.

## They are checked by running

The project is part of the gate (`crates/adamas-cli/tests/examples.rs`): it
must check, its answer is recorded, its tests pass, it is documented, it is in
the formatter's canon, and the binaries built through C and through LLVM
print what the interpreter prints.

Section numbers (§) refer to the design document, `adamas-design.md`.

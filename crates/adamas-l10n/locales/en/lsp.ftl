# The LSP server: hints, hover, protocol (adamas-lsp).
#
# A literal brace is written in Fluent as {"{"} and {"}"}.

lsp-hints-1 = `@noalloc` would be accepted on this definition: among the sources listed in §5.1 the verdict found none. The verdict speaks about what is listed - installing a handler site is not in the list and costs three heap blocks (§10 question 190).
lsp-hints-2 = The construction takes a slot of the cell matched by the branch: the shape of the code does not prevent reuse, and on a unique input (RC = 1) it rewrites the slots instead of allocating (§5.1). Both lowerings insert it; whether it fires is decided by the reference count at runtime, and uniqueness is a property of the call site - so the hint speaks about the shape of the code, not about a particular run. The machine (`adamas eval`) has no reuse at all.
lsp-hints-3 = The binding is linear by construction (§3.3), but there is no destructor here: the value is spent further on, and whoever took it closes it. `unique data` has no destructor at all - memory is freed statically.
lsp-hints-4 = Here the compiler inserts the destructor call - on leaving the binding's scope, and on **all** exits: including the one where the computation is aborted by an effect (§3.3 × §3.4). Among several the order is LIFO: what is bound later is closed earlier.
lsp-hints-5 = `handle` takes the label from the first operation branch when it is not written after `@` (§4.1): it is not in the text here, and it is exactly what is removed. In the corpus 151 handlers of 175 are written this way.
lsp-hints-6 = Handlers **of this file** that discharge the operation's label. Which of them fires is decided by the call site, not by the operation's site: `handle` takes a named computation (§3.4), so the operation and its handler stand in different bodies. "in the row" - this file does not discharge the label, and it goes up the row.
lsp-hints-7 = There is no place: behind this name stands a record built by elaboration - a module value or an instance dictionary - and its author wrote no expression. There would be nowhere to point (82 such definitions in the corpus).
lsp-hints-8 = , reuse failed
lsp-hints-9 = heap
lsp-hints-10 = in the row
lsp-hints-11 = heap
lsp-hints-12 = no reuse
lsp-hints-13 = record
lsp-hints-14 = closure
lsp-hints-15 = boxing
lsp-reuse-count = Constructions taking a slot of the matched cell: { $count }. { $why }
lsp-released-here = The binding is linear by construction (§3.3). The compiler inserts `{ $drop } { $name }` on leaving the scope - on all exits, including an abort by an effect.
lsp-allocates-heap = Allocates on the Perceus heap: { $blame }.
lsp-reuse-blocked = Cell reuse: { $fault }.
lsp-spent = { $keyword }, spent
lsp-allocates = Allocates: { $blame }.
lsp-blame-partial = { $name } partially
lsp-blame-operation = operation { $name }
lsp-blame-handler = handler { $effect }
lsp-blame-opaque = { $name } without a body
lsp-bad-params = parameters not parsed: { $error }
lsp-unsupported = method `{ $method }` is not supported by the server
lsp-notification = notification `{ $method }` not handled: { $error }

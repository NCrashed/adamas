# The evaluation machine (adamas-interp).
#
# A literal brace is written in Fluent as {"{"} and {"}"}.

interp-unhandled = operation `{ $operation }` of label `{ $effect }` is left without a handler
interp-no-unit = unit is not declared with a single constructor: there is nothing to run a suspended computation with
interp-no-fiber = the task value names no live fiber: it was not built by a nursery
interp-foreign-task = the task belongs to another nursery: it can be awaited only there
interp-task-shape = the result of `{ $operation }` must be a type with one constructor and one field: it holds the fiber number
interp-deadlock = deadlock: all live tasks wait for each other
interp-no-library = library `{ $library }` did not load: { $why }
interp-no-symbol = library `{ $library }` has no symbol `{ $symbol }`: { $why }
interp-foreign-shape = signature `{ $symbol } : { $signature }` is outside the call table: there is no way to call it
interp-foreign-argument = argument { $at } of function `{ $symbol }` is declared `{ $want }`, but `{ $got }` came
interp-callback = callback `{ $symbol }`: { $why }
interp-machine-1 = the callback has an environment, and there is nowhere to put it: the position of `userdata` is written by the author - `callbackEnv` in an argument (FFI level 2)
interp-machine-2 = `callbackEnv` is written, and this call has no callback with an environment: level 1 carries no environment
interp-machine-3 = more than one callback with an environment in one call: `callbackEnv` names one, and which one is not written
interp-machine-4 = the name in the callback position is already applied: level 1 takes a pointer to a definition, not its application
interp-callback-1 = the shape is not among the machine's trampolines: supported are `(UInt64, UInt64) -> Int32` (the `qsort` comparator, and with an environment `qsort_r`) and `(UInt64, UInt64, UInt64, UInt64) -> UInt64` (the libcurl write callback)
interp-callback-2 = a machine invariant broke inside the callback: a panic cannot be unwound through a foreign frame, so it is turned into a refusal
interp-callback-3 = the foreign side called the trampoline outside its registration: the table slot is free, so the wrapper has already unregistered it (FFI level 3)
interp-callback-4 = the trampoline's `userdata` is not the registered one: the foreign side passed someone else's word, and there is nothing to compute with it (FFI level 2)
interp-callback-5 = closure
interp-callback-6 = the signature has no definition of that name
interp-foreign-4 = callback
interp-foreign-5 = no candidates were found
interp-foreign-6 = `dlsym` found it in none of them
interp-foreign-7 = none of the linked libraries opened
interp-foreign-buffer = `{ $symbol }` lends a buffer to the foreign side, and the array in this position is not a flat block: longer than { $limit } bytes or with a non-primitive cell
interp-callback-table-full = the machine's trampoline table is full: { $slots } slots, all taken (FFI level 3)
interp-callback-unhandled = operation `{ $operation }` of label `{ $effect }` is left without a handler inside the callback: the machine runs the callback separately, and the registration site is not visible to it. The lowerings compute this program - the evidence vector travels to them in `userdata` (FFI level 2)
interp-callback-answer = the callback's result is not a literal: { $term }

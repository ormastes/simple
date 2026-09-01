# Interpreter function calls ignored named argument order

**Status:** Source fixed; pure-Simple execution pending  
**Component:** compiler/core interpreter call evaluation  
**Found:** 2026-07-15

## Symptom

The parser retained call argument names, but ordinary, static, forced-deferred,
indirect, and instance-method call evaluation passed only argument expressions to the
callee. For example, `encode(b: 2, a: 1)` bound positionally and returned `21`
instead of `12`.

## Root cause and fix

Both function evaluator mirrors discarded `expr_get_arg_names(eid)` at the
function-call boundary. `eval_function_call` now receives the parallel name
list, evaluates every expression once in source order, maps named values to the
declared parameter slot, and lets positional values fill the next unoccupied
slot. Unknown, duplicate, and excess named-call arguments fail explicitly.
Reordering happens before generic inference, type checking, JIT conversion,
and environment binding. The active instance-method binder applies the same
mapping after its synthetic `self` slot and reorders expression IDs in parallel
so mutable argument write-back still targets the correct caller variable.

Internal lifecycle calls pass an empty name list. The existing direct
`core_interpret` regression now covers reordered ordinary, static, indirect,
and instance-method calls alongside constructor named arguments.

## Verification

Static source gates and independent high-level review are required before
landing. Runtime execution remains pending because this lane has no valid
pure-Simple executable; the Rust seed is bootstrap-only and is not an oracle.

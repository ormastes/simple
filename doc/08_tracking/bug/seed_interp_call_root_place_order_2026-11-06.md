# Seed interpreter: a call-result root keeps the old place order

- **Found:** 2026-11-06 in the W2a review (PR #7260).
- **Repro:** `get_arr()[i()] += rhs()` and `get_arr()[i()] = rhs()`, where `get_arr`, `i` and `rhs` each log a side effect.
- **Symptom:** the place root is not a variable, so `place::resolve_place` returns `None` and `node_exec.rs` falls back to the pre-W2a path. That path evaluates the index before the receiver call.
- **Expected:** per the owner contract of 2026-11-06, the RHS first, then the receiver, then the index, each exactly once.
- **Other engines:** the seed JIT moves a non-variable root under an index into a temporary (`$aug_root`) and conforms, and so does pure-Simple.
- **Fix direction:** make `resolve_place` accept a temporary root (evaluate it once, bind a hidden local), or reject call-result roots as non-places on every engine.

## Resolution (2026-11-06)

- **Root cause:** `place::resolve_place` returns `None` for a call-result root. `exec_assignment` and the indexed arm of `exec_augmented_assignment` (`interpreter/node_exec.rs`) then fell back to the identifier/field-only paths. Those evaluated the index before the root, and then rejected the target outright ("index assignment requires identifier or field access as container").
- **Fix:** `place::bind_call_root` evaluates a `Call`/`MethodCall` root once, after the RHS, and binds it to a hidden NUL-prefixed local. The place is rewritten onto that local, so `resolve_place` evaluates the indices after the root. Both index paths use it.
- **Evidence:** `test/01_unit/language/call_root_place_order_spec.spl` went from RED on the interpreter (the probe errored) to GREEN on both engines. The fresh base seed's JIT already conformed. An earlier run on the stale `simple-w2a` scratch seed showed `get,i,rhs,get,i`, so that seed should not be used as a reference.
- **Note:** the engines still diverge on where the write lands. The JIT writes through the returned array handle, while the interpreter writes into the bound copy. That is an array aliasing question, not an evaluation-order one, and this fix does not change it.

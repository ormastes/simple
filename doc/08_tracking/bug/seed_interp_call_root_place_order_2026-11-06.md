# Seed interpreter: a call-result root keeps the old place order

- **Found:** 2026-11-06 in the W2a review (PR #7260).
- **Repro:** `get_arr()[i()] += rhs()` and `get_arr()[i()] = rhs()`, where `get_arr`, `i` and `rhs` each log a side effect.
- **Symptom:** the place root is not a variable, so `place::resolve_place` returns `None` and `node_exec.rs` falls back to the pre-W2a path. That path evaluates the index before the receiver call.
- **Expected:** per the owner contract of 2026-11-06, the RHS first, then the receiver, then the index, each exactly once.
- **Other engines:** the seed JIT moves a non-variable root under an index into a temporary (`$aug_root`) and conforms, and so does pure-Simple.
- **Fix direction:** make `resolve_place` accept a temporary root (evaluate it once, bind a hidden local), or reject call-result roots as non-places on every engine.

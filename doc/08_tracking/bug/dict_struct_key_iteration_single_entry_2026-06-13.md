# Bug: Dict<SymbolId, MirFunction> struct-key iteration yields only one entry (interpreter)

- **Date:** 2026-06-13
- **Severity:** P2 (silent data loss in iteration — masks multi-entry processing)
- **Status:** Fix landed in worktree `wt_s22` for a reproduced type-corruption
  crash + a reproduced flaky duplicate-key non-collapse (interpreter/`val`
  path), PENDING-REDEPLOY (Rust seed change; not cargo-built/verified in this
  sandbox per lane hard rules). The exact "1 entry -> 4 iterations" / "3 -> 4"
  counts from the 2026-07-17 runtime-verification note below were NOT
  reproduced by this fix lane, on either the interpreter or the native/`var`
  path — see "Root cause and fix" and "Second, DISTINCT defect location"
  below before assuming this closes the reported symptom.
- **Area:** interpreter dict (`Value::Dict`) with struct/composite keys,
  `src/compiler_rust/compiler/src/value_impl.rs` +
  `interpreter/node_exec.rs` + `interpreter/expr/collections.rs` +
  `interpreter_helpers/collections.rs` + `interpreter_method/collections.rs`

## Symptom

Iterating a `Dict<SymbolId, MirFunction>` (struct-typed key) in interpreter
mode yields only ONE entry even when several were inserted. Hit while
implementing the W3.1 kernel→VHDL bridge: a multi-kernel MIR module's kernel
dict iterated as if it held a single kernel.

## Workaround

Use a single-entry dict per processing step, or call the per-item function
directly for each known key (used in
`test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl`, which
calls `emit_vhdl_kernel_entity` once per kernel instead of iterating the
module dict).

## Expected

Dict iteration visits every inserted entry regardless of key type.

## Notes

Found during `doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md`
W3.1. Likely related to struct-key hashing/equality in the interpreter dict
implementation. A minimal repro should insert 3 entries keyed by a 2-field
struct and count iteration visits.

## Runtime verification (2026-07-17)

Probed with 3 entries inserted into `Dict<Key,i64>` (2-field struct key). Symptom drifted from documented single-entry undercounting: `d.len()` now reports **4** (overcounting by 1), and iteration crashes with `error: semantic: undefined field: unknown property or method 'a' on String` — one of the iterated "keys" is a plain String, not a Key struct. This is not the exact documented symptom but clearly the same underlying struct-key Dict corruption class and is at least as broken (type confusion + silent over-counting).

## Root cause and fix (2026-07-17, worktree wt_s22)

The interpreter's `Value::Dict`/`FrozenDict` (`src/compiler_rust/compiler/src/value.rs`)
is `Arc<HashMap<String, Value>>` -- keys are ALWAYS converted to a `String` via
`Value::to_key_string()` before insertion, and only the associated *value* is
stored; the original key `Value` is discarded. Two independent defects follow
from this design, both confirmed empirically (5x re-run of a probe that
inserts the same-valued struct key twice into an empty dict; single-entry.spl
probes below):

1. **Over-count / drift (nondeterministic).** `to_key_string()`'s catch-all
   for composite types (`Value::Object`, `Value::Enum`, `Value::Tuple`, ...)
   fell through to `format!("{other:?}")` (derived `Debug`). `Value::Object`'s
   `fields` is `Arc<HashMap<String, Value>>`, and Rust's std `HashMap` seeds a
   fresh, randomized hasher per instance, so two structurally-EQUAL structs
   built as separate literals (e.g. `Key(a:7,b:8)` constructed twice) can
   iterate their fields in a different order and produce DIFFERENT debug
   strings. Re-run evidence (`s22p04_multi_entry.spl`, 5 runs): re-inserting
   `Key(a:7,b:8)` a second time with a different value produced `len()==2`
   (two runs) or the correct `len()==1` (three runs) -- a flaky 1-vs-2
   non-collapse. NOTE: this is NOT the literal "1 entry -> 4 iterations" /
   "3 entries -> len 4" from the runtime-verification note above -- that
   exact count was never reproduced here, on either the interpreter or the
   native path (see "Second, DISTINCT defect location" below), despite
   ~15 probe runs across single/multi/duplicate-key scenarios. This fix
   addresses the same defect CLASS (nondeterministic dict-key string for
   composite types) and the same directional symptom (over-count instead of
   under-count), but it is not confirmed to be the exact same bug instance
   the runtime-verification lane observed. Whoever confirms this fix at
   redeploy should re-check against the ORIGINAL 1-insert/4-iteration and
   3-insert/4-iteration repro, not just the flaky-duplicate-key repro used
   here.
2. **Type corruption on iteration (deterministic, 100% repro).** Iteration
   (`for k,v in dict`, `.keys()`, `.entries()`) only ever had the map's raw
   *string* key on hand, so it always bound `k = Value::text(string_key)`
   regardless of the ORIGINAL key's type. For struct keys this yields a
   String where a struct was expected, crashing on the very next field access
   (`error: semantic: undefined field: unknown property or method 'a' on
   String`). This is actually a pre-existing simplification for ALL non-text
   keys (confirmed: an i64-keyed dict's iterated `k` is also `Value::text`,
   e.g. `k + 1` on an int key silently does STRING CONCATENATION instead of
   integer addition -- masked because it still "looks like a number"). No
   existing test asserts key TYPE fidelity for scalar keys, so this bug's
   fix deliberately leaves scalar-key behavior byte-for-byte unchanged and
   only closes the gap for composite keys, per lane scope ("keep i64/text
   dict iteration untouched").

### Fix

- `value_impl.rs`: `to_key_string()` now canonicalizes `Value::Object`
  (fields sorted by name), `Value::Enum`, `Value::Tuple`, `Value::LabeledTuple`,
  `Value::Array`/`FrozenArray` instead of falling through to derived `Debug`
  -- deterministic regardless of internal `HashMap` iteration order. Fixes
  defect (1) directly.
- New helpers on `Value` (`value_impl.rs`): `dict_key_is_scalar`,
  `wrap_dict_entry`, `unwrap_dict_entry`, `dict_entry_key_for_iteration`,
  `dict_entry_value_for_iteration`. For composite (non-scalar) keys only, the
  dict's stored map value is now `Tuple([Symbol("__dict_entry__"), original_key,
  actual_value])` (a reserved marker, mirroring this codebase's existing
  `__setitem__`/`__getitem__` dunder convention) so the original key survives
  and can be recovered without a key argument on hand. Scalar keys
  (int/uint/float/bool/text/symbol/nil) are NEVER wrapped -- `wrap_dict_entry`
  returns `value` unchanged for them, so their stored representation and
  every observable behavior is bit-for-bit identical to before this patch.
- Wired at every dict SET site (`src/compiler_rust/compiler/src/interpreter/node_exec.rs`
  index-assignment x5, `interpreter/expr/collections.rs` dict literal + dict
  comprehension) and every dict GET/iterate site (`expr/collections.rs` index
  read, `interpreter_helpers/collections.rs::iter_to_vec` used by `for k,v in
  dict`, `interpreter_method/collections.rs::handle_dict_methods` --
  `get`/`get_or`/`fetch`/`keys`/`values`/`entries`/`items`/`set`/`insert`/`dig`).
  `handle_frozen_dict_methods` delegates to `handle_dict_methods` for reads,
  so it inherits the fix with no separate edit. `contains_key`/`remove`/
  `merge`/`clone`/`clear` needed no change (membership check doesn't need the
  value; remove/merge/clone/clear are transparent to the wrap convention).
  `map_values`/`filter`/`compact`/`group_by`/`dig`-via-lambda were left
  unmodified (out of this lane's verification scope; each would need the
  lambda-callback plumbing reworked too -- tracked as a known residual gap,
  not attempted here to avoid scope creep).

### Verification status

Probes reproduced BOTH defects pre-fix on the deployed seed binary (see
`s22_probes/` below). Per this lane's hard rules, `cargo` must not be run, so
the fix could not be rebuilt+re-run in this sandbox; validation here is
code-read only (every touched call site manually traced for type/ownership
correctness). Actual pass/fail on the fixed binary is PENDING-REDEPLOY.

### Second, DISTINCT defect location found (NOT fixed here -- follow-up)

`bin/simple run` on a `val`-bound dict that is still index-assigned fails HIR
capability checks ("mutation without mut capability") and falls back to the
buggy interpreter path above. A `var`-bound dict of the same shape instead
JIT/native-compiles successfully and, for a *single* entry, iterates
correctly (probe `s22p07_single_entry_var.spl`) -- because the native path
(`src/compiler_rust/runtime/src/value/dict.rs`, `RuntimeDict` /
`rt_dict_set`/`rt_dict_get`/etc.) stores the actual `RuntimeValue` key, not a
serialized string, so no TYPE corruption occurs there.

However, that native path has its OWN, deterministic (not flaky) over-count
defect: `keys_equal()` (dict.rs) only special-cases `String` for
content-equality; every other type -- including a struct/object heap pointer
-- falls back to `a == b` (raw pointer/tag identity). Two SEPARATELY
constructed struct instances with identical field values are therefore never
considered equal, so re-inserting a "duplicate" struct key creates a second,
distinct entry every time. Confirmed 3/3 runs via `var`-bound
`s22p08_var_duplicate_value_key.spl`: `d2[Key(a:7,b:8)] = 111` then
`d2[Key(a:7,b:8)] = 222` yields `len()==2` with BOTH `v2=111` and `v2=222`
present, deterministically (not the flaky 1-or-2 seen on the interpreter
path -- this one is a straight identity-vs-value-equality bug, always wrong).

This is real and confirmed, but is a SEPARATE code path from the interpreter
fix above, requires struct-layout-aware recursive field comparison inside a
low-level, ABI-adjacent runtime module with no compile-time type metadata
currently threaded into it, and was judged too large/risky to attempt
without compile verification in this lane (vs. the interpreter fix, which
was small, mechanical, and thoroughly code-read-verified). Left for a
follow-up lane; not touched by this patch. `src/compiler_rust/runtime/src/value/dict.rs`
is the file to fix (`hash_value`/`keys_equal`, both `pub(super)` near the top
of the file).

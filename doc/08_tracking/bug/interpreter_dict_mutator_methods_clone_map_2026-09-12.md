# Interpreter: dict mutator METHODS clone the whole map on every call

- Status: RESOLVED (2026-09-12) on `work/interp-dict-remove` for the
  BARE-IDENTIFIER receiver — ratios 14.69 / 19.37 / 15.49 / 11.78 -> 4.57 / 4.29 / 4.14 / 4.46
  at 4x n (linear is 4.00); pinned by `test/05_perf/interp/dict_mutator_scaling_spec.spl` and the
  DICTMUT rows in `scripts/check/check-perf-regression-tests.shs`. The FIELD
  receiver (`self.d.remove(k)`) is deliberately NOT fixed here — see
  "Not fixed in this lane".
- Found: 2026-09-12, interpreter component scaling probes
- Component: seed tree-walk interpreter —
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`
  (identifier-Dict branch of `handle_method_call_with_self_update_inner`),
  `src/compiler_rust/compiler/src/interpreter_method/collections.rs`
  (`handle_dict_methods` mutator arms)
- Lane: interpreter only; JIT/native lower dict writes to `rt_dict_*` and are flat.

## Summary

`d[k] = v` (indexed store) has always been linear: `interpreter/node_exec.rs`
mutates the binding's `Arc<HashMap>` through `Arc::make_mut`. The METHOD forms
did not. The identifier-Dict branch at `patterns.rs:1544` re-entered
`evaluate_expr` on the whole method call, which dispatched into the purely
functional `handle_dict_methods` — and every mutator arm there opens with
`let mut new_map = map.clone()`:

- `"set" | "insert"` — `collections.rs:1260`
- `"remove" | "delete"` — `collections.rs:1266`
- `"merge" | "extend"` — `collections.rs:1282`

`handle_dict_methods` takes `map: &HashMap<String, Value>` and never sees an
`Arc`, so it *cannot* mutate in place; the copy is structural to that entry
point. The defect is that the slot OWNER routed back into it instead of
mutating its own `Arc`.

Measured `Arc::strong_count == 1` at the branch on every call (`SIMPLE_DICT_TRACE`
instrumentation, removed after measurement): the binding is uniquely owned and
the whole-map copy is entirely gratuitous. One copy of the CURRENT length per
call gives `sum(len) = n(n-1)/2` = 12,497,500 entry copies at n = 5000, which is
exactly the measured progression (`call#2000 len=3000`, `call#4000 len=1000`).

## Evidence

Deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(50,093,192 bytes, built 2026-09-06 09:59:11), interpreter lane, standalone
probes at n=20000 vs 80000:

| loop body | n=20000 | n=80000 | verdict |
|---|---:|---:|---|
| `d.remove("k{i}")` (local) | 11.50 s | >90 s (timeout) | QUADRATIC |
| `self.d.remove(k)` (class method) | 14.16 s | >90 s (timeout) | QUADRATIC |
| `d["k{i}"] = i` (control, bracket store) | 0.03 s | 0.13 s | linear |

Through the spec runner at n=5000 vs 20000 (a 4x step; linear ~4, quadratic ~16),
one `test/05_perf/interp/dict_mutator_scaling_spec.spl` run per binary:

| loop body | RED n=5000 | RED n=20000 | RED ratio | GREEN n=5000 | GREEN n=20000 | GREEN ratio |
|---|---:|---:|---:|---:|---:|---:|
| `d.remove(k)` | 0.727 s | 10.678 s | **14.69** | 0.014 s | 0.065 s | **4.57** |
| `d.insert(k, v)` | 0.584 s | 11.312 s | **19.37** | 0.017 s | 0.073 s | **4.29** |
| `d.set(k, v)` | 0.527 s | 8.161 s | **15.49** | 0.018 s | 0.073 s | **4.14** |
| `d.merge(o)` | 0.554 s | 6.532 s | **11.78** | 0.019 s | 0.087 s | **4.46** |

RED binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50,093,192 bytes, 2026-09-06 09:59:11.
GREEN binary: `<worktree>/src/compiler_rust/target/release/simple`,
51,245,704 bytes, 2026-09-12 10:12:53. A second run on the final tree (same size,
2026-09-12 10:21:29 — the delta is comments and one assertion message) on a
less-loaded box gave 8.4/32.5, 8.8/36.1, 8.9/34.9 and 10.6/40.7 ms, i.e. ratios
3.88 / 4.11 / 3.93 / 3.86. Both runs are 8 of 8 examples passing.
At n=20000 the absolute cost falls 164x (`remove`), 154x (`insert`), 113x (`set`)
and 75x (`merge`); the RATIO is the load-independent statement.

## Fix (semantics unchanged)

One kernel, mirroring how arrays are handled:

- `apply_dict_mutation_in_place(method, &mut HashMap, key: Option<Value>, value: Option<Value>)`
  in `collections.rs`, immediately above `handle_dict_methods`. Returns `()`, not
  `Option<Value>` like the array kernel: every dict mutator's expression result is
  the DICT itself.
- `handle_dict_methods`' three cloning arms now `map.clone()` then call the kernel
  — the clone-then-mutate lane is unchanged in behaviour and still serves every
  caller that only has a `&HashMap`. `"clear"` keeps its O(1) fresh-empty-map
  short-circuit rather than being routed through a clone.
- The identifier-Dict branch in `patterns.rs` evaluates its argument(s) exactly
  once, parks module-global aliases via `release_global_aliases` (as the array
  path does), re-reads the binding with `env.get_mut`, and mutates through
  `Arc::make_mut` — uniquely owned mutates in place, a genuine alias
  (`val alias = d`) clones-then-mutates. `DICT_MUT_CALLS` /
  `DICT_MUT_COW_CLONES` / `DICT_MUT_COW_ENTRIES_CLONED` counters mirror `ARR_MUT_*`.

Preserved exactly: the return contract (the dict, not the removed value),
MODULE_GLOBALS write-through, the `CONST_NAMES` immutable-dict rejection, the
FrozenDict rejection (`env.get` matches `Value::Dict` only, so a frozen dict never
enters the fast path), the `merge` TYPE_MISMATCH text and its empty-dict default
for a missing argument, and value semantics on genuine aliasing.

### Accepted edge cases

`d.clear()` on a *genuinely aliased* dict now costs one extra whole-map copy:
`Arc::make_mut` clones the map and then clears the clone, where the functional arm
allocated a fresh empty map. The sole-owner case is unchanged in order — it was an
O(1) allocation plus the O(n) drop of the old map, and is now an O(n) in-place
clear — and the aliased case is a single call, never a loop. Noted rather than
special-cased.

The `merge`/`extend` slow path now clones the map BEFORE the argument type check,
so a non-dict argument pays one wasted copy before raising the same
`TYPE_MISMATCH`. Error path only, no semantic change; kept because routing all
three arms through one kernel is what makes the two lanes provably identical.

## Not fixed in this lane

`self.d.remove(k)` / `self.d.insert(k, v)` reach the SAME `collections.rs`
clone through the general PLACE branch (`patterns.rs:945` ->
`evaluate_method_call_with_self_update`, which evaluates the receiver to a value).
Fixing that requires the place kernel to walk `env.get_mut(root)` -> `project_mut`
-> `&mut HashMap` and mutate the leaf; the kernel added here is exactly what that
walk should call. Tracked in
`interpreter_nested_place_mutation_clones_container_2026-09-12.md`.
`test/05_perf/interp/dict_mutator_scaling_spec.spl` therefore carries the field
form as a CORRECTNESS pin only, with no ratio bound.

## Discrepancies found while writing the spec

- `remove` returns the **updated dict**, not the removed value — deliberately
  unlike `array.remove(i)`, which returns the removed element since the
  2026-07-20 contract fix. Pinned by the spec and by
  `dict_mutators_return_the_dict_not_the_element` in `patterns.rs`.
- `update` is **not** a plain-dict method: only `handle_frozen_dict_methods`'
  rejection list names it, and `d.update(o)` errors with
  ``method `update` not found on type `dict` ``. Out of scope here; recorded so
  the next reader does not assume the frozen list mirrors the real surface.

## Fix-test spec

`test/05_perf/interp/dict_mutator_scaling_spec.spl` — a ratio bound per mutator
(`remove`, `insert`, `set`, `merge`) plus semantic pins: drain-to-empty, alias
copy-on-write, the return contract, and the field form.

Rust mechanism tests in `interpreter_helpers/patterns.rs`
(`cow_alias_mechanism_tests`): `local_dict_insert_mutates_the_single_owner_in_place`,
`genuinely_aliased_dict_still_copies_on_write`,
`dict_mutators_return_the_dict_not_the_element`.

## Verification (rebuilt binary, 51,245,704 bytes @ 2026-09-12 10:21:29)

- `test/05_perf/interp/dict_mutator_scaling_spec.spl`: 8 of 8 examples pass
  (4 of 8 on the deployed seed — the four ratio bounds were the RED).
- `cargo test --release -p simple-compiler --lib cow_alias_mechanism_tests`:
  8 passed, 0 failed (3 new).
- `cargo test --release -p simple-compiler --lib -- dict collections patterns`:
  110 passed, 0 failed.
- 28 dict/map specs re-run on both binaries: 24 OK / 4 with pre-existing
  failures, and the per-file verdict lines are BYTE-IDENTICAL before and after.
  The four pre-existing reds are `compiler/dict_get_miss_returns_nil_spec.spl`
  (13/14), `compiler/interpreter/dict_class_value_identity_spec.spl` (3/4),
  `lib/nogc_async_mut/map_insert_if_absent_spec.spl` (0/1) and
  `lib/nogc_sync_mut/map_traversal_spec.spl` (parse-error) — all red on the
  deployed seed too.
- `scripts/check/check-perf-regression-tests.shs`: 191 -> 199 mechanisms checked
  (8 new DICTMUT rows, all ok), same 4 pre-existing regressions as `main`.
  `ROW_FLOOR` raised 147 -> 155 in the same change, per that file's own rule.
- Semantics probed on BOTH binaries with byte-identical output: a module-global
  dict mutated from a helper fn (`g.insert(k, v)` -> `g.len()` = 3, so the
  MODULE_GLOBALS write-through survives), and the immutable-binding rejection
  (`cannot call mutating method 'insert' on immutable dict 'd'`). A FrozenDict
  cannot be constructed from `.spl` source in the interpreter today (`freeze()`
  is not a dict method), so its rejection is argued structurally: `env.get`
  matches `Value::Dict(_)` only, so a frozen dict never enters the fast path.

## Related

- `doc/03_plan/agent_tasks/simple_infra_optimization_parallel_plan_2026-09-08.md` (L2/L3)
- `interpreter_string_char_index_rescans_per_call_2026-09-12.md` (same session,
  different mechanism)

# Seed interpreter: `g.push(x)` on a module-global array is O(len) per call

**Date:** 2026-08-22 · **Lane:** seed perf (sampling profiler) · **Status:** FIXED. `80c39729a40` (parallel lane) fixed the same-frame shape first; on top of it the helper-fn shape (expr_alloc) was STILL quadratic — measured 20k pushes 10.9 s / 80k 350 s on `c6f190752ff` — because the global is never in the helper's env and fell to the generic clone path. This lane's patterns.rs fix closes that shape

## Symptom

`bin/simple lint src/compiler/80.driver/driver_types.spl` under the seed
interpreter (`SIMPLE_EXECUTION_MODE=interpret`): 80.5 s wall / 44.4 s CPU.
The new level-gated sampler (`SIMPLE_INTERP_SAMPLE=1`, 10 ms SIGPROF) put
`expr_alloc` at **10.7 % self time** — the top frame — for a function that
does nothing but ~15 `push`es onto module-global side tables
(`src/compiler/10.frontend/core/_AstExpr/nodes.spl:506`). Not proportional
to the work.

## Reproduce (pre-fix, seed `c089809a253`+sampler)

| shape | 20k pushes | 80k pushes |
|---|---|---|
| local `var l: [i64]`, `l.push(i)` in a loop | 0.33 s | 0.65 s |
| module-global `g`, `g.push(i)` in `main`'s loop | 5.04 s | 143 s |
| module-global `g`, `alloc(i)` helper does `g.push(i)` (expr_alloc shape) | 23.8 s | 488 s |

`SIMPLE_PERF_COUNTERS=1`, N=3000, helper shape:
`ARR_MUT_CALLS 2999  ARR_MUT_COW_CLONES 2999  ARR_MUT_COW_ELEMS_CLONED 4498500`
— every single push deep-copied the backing Vec.

## Mechanism

`interpreter_helpers/patterns.rs` already had an ownership-gated in-place
path (`Arc::make_mut` on the frame's overlay Arc) for `name.push(..)`, but:

1. It was gated on `env.get(name)` being an Array. A module global mutated
   from a helper fn is NOT in the frame's env (identifier reads of non-local
   names go to `MODULE_GLOBALS`, `literals.rs`), so the helper shape fell
   through to the generic `evaluate_method_call_with_self_update`, which
   clones the receiver value and mutates the copy — O(len) always.
2. Even when the name was in the overlay (`main` shape), the Arc was aliased
   by `MODULE_GLOBALS` (re-published after every write by
   `sync_flat_global`), so `Arc::strong_count > 1` and `make_mut` cloned.

## Fix (`interpreter_helpers/patterns.rs`, `value.rs`) — helper-fn shape

* Promote a store-resident global array into the frame overlay (one Arc
  clone) so the in-place path applies to the helper-fn shape.
* `release_global_aliases`: before `make_mut`, park the stores' copies
  (`MODULE_GLOBALS`, owner live store -> `Nil`) and drop the frame's store
  snapshot (`release_scope`), so the overlay Arc is unique; the existing
  write-through (`sync_flat_global`) re-publishes the mutated Arc and the
  scope is re-pointed (`refresh_scope`). The error path restores the stores
  from the frame value. Semantics unchanged: a genuinely aliased array
  (another binding holds the Arc) still goes through the COW clone.

## After (same box, load ~26-30 vs ~47 before — compare CPU, not wall)

| shape | 20k pushes | 80k pushes |
|---|---|---|
| module-global `g`, `g.push(i)` in `main`'s loop | 5.04 s -> **0.16 s** | 143 s -> **0.47 s** |
| helper-fn `alloc(i)` (expr_alloc shape) | 23.8 s -> **0.47 s** | 488 s -> **2.19 s** |

Counters (helper shape, N=3000): `ARR_MUT_COW_CLONES 2999 -> 2`.

`lint src/compiler/80.driver/driver_types.spl` under `SIMPLE_EXECUTION_MODE=interpret`:
80.5 s wall / **44.4 s CPU** -> 35.8 s wall / **31.2 s CPU**; `expr_alloc` self
time 10.7 % -> 4.6 % of samples. (The default JIT-assisted lint of the same
file is 34.7 s wall and does not go through this path at all.)

Pin test pre-fix: `[global-push] 2k 202 ms, 8k 2.99 s, ratio 14.81` -> FAIL;
post-fix ratio well under 8.

## Third holder found by memory search

After parking both stores and the frame snapshot the Arc was STILL at
`strong_count == 2`. Searching the stopped process (`gdb` + `/proc/pid/mem`
scan for the `ArcInner` address) found exactly one heap holder (the overlay)
and the rest on the Rust STACK: `handle_method_call_with_self_update_inner`
did `MODULE_GLOBALS...get(obj_name).cloned()` into a `global_obj` local that
only ever matched `Value::Object`, but held the ARRAY clone for the rest of
the function. Now clones only an Object.

## Pins

* Rust: `src/compiler_rust/compiler/tests/interpreter_global_array_push_linear.rs` (helper-fn shape; same-frame shape is pinned upstream by `interpreter_global_array_push_in_place.rs`)
* Spec: `test/01_unit/compiler/interpreter/global_array_push_linear_spec.spl`
* Perf gate row: `scripts/check/check-perf-regression-tests.shs`

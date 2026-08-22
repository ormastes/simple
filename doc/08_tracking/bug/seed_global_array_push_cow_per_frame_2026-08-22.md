# Seed: every `global_array.push(x)` inside a function deep-copied the array once per frame (2026-08-22)

## Symptom

Parse time superlinear in module size under the Rust seed interpreter:
`src/compiler/hir/generated/hir_codec.spl` (6107 lines) took 19.8 min in the
stage1 driver; `SIMPLE_PERF_COUNTERS=1` over a synthetic module of N two-line
functions showed `ARR_MUT_COW_ELEMS_CLONED` 57 / 10,425 / 271,125 / 4,369,500
for N = 1 / 10 / 50 / 200 -- quadratic -- with ~108 COW clones per function.
The new attribution trace (`SIMPLE_PERF_COUNTERS_TRACE=<min_len>`) named
them: every flat-AST pool (`expr_tag`, `expr_span`, `span_pool_*`, ...) on
every `expr_alloc` call, i.e. ~70 pools deep-copied per AST node.

## Mechanism (three pins, all seed-side)

`Env::get_mut` promotes a module global into the frame overlay by cloning its
`Arc`. Because the store's owner map (shared with the frame's own scope
snapshot), the flat `MODULE_GLOBALS` mirror and caller frames' refreshed
overlay copies all kept their references, the array's strong count was >= 2 at
`Arc::make_mut`, which then copied the whole `Vec` -- O(len) per push, once per
frame per global. The parser pushes ~70 pools per node from a fresh frame each
time, so a parse is O(pools x nodes x pool_len).

One further pin was a plain temporary: `interpreter_helpers/patterns.rs`
cloned whatever the flat map held for the receiver name into `global_obj` (it
only ever used the `Object` case) and kept that clone alive across the
in-place mutation branch.

## Fix (`src/compiler_rust`, seed only; no Simple source semantics change)

1. `interpreter_state::steal_owned_global`: at promotion of a collection
   (Array/Dict/Object) the frame releases its scope snapshot so the store is
   uniquely owned, swaps a `Value::Nil` placeholder into the owner map and the
   flat mirror (pointer-checked), and re-pins a fresh snapshot. O(1), no map is
   cloned; it bails out (old behaviour) if anything still shares the store.
   Every call boundary and frame exit publishes before another frame can read,
   so the placeholder is never observable.
2. `Env::drop_published_globals`, called from `publish_and_repoint` after the
   overlay has been published and the scope refreshed: the frame drops its
   overlay copies of globals the scope resolves (reads continue through the
   refreshed snapshot with the identical value), so a caller no longer pins
   collections while its callee runs.
3. `patterns.rs`: clone the flat-map value only when it is an `Object`.

Counters pin it (`STEAL_OK`, `STEAL_*` bail-out reasons added to
`perf_counters.rs`).

## Measurement

Bare parse via `parse_and_build_module_scoped`, `SIMPLE_EXECUTION_MODE=interpret`,
shared host (load 28-55, so absolute times carry ~2x noise; the counters do
not). "old" = pinned seed `simple.1ffdfb58baf`; "new" = same tree built with
this fix. Both runs include the lexer fix from the sibling record.

| fixture | ARR_MUT_COW_ELEMS_CLONED old | new | parse ms old | new |
|---|---|---|---|---|
| 10 fns (362 B) | 10,425 | 45 | 378 | 262 |
| 50 fns (1.9 KB) | 271,125 | 1,225 | 2,180 | 1,356 |
| 200 fns (7.8 KB) | 4,369,500 | 19,900 | 7,537 | 6,263 |
| `src/compiler/10.frontend/core/parser.spl` (62 fns) | | | 23,496 | 16,332 |
| `src/compiler/hir/generated/hir_codec.spl` (6107 lines) | | | 631,368 | **186,827** |

The same file measured 1,186,509 ms in the stage1 driver (run10) before
either fix. Flat-pool dumps of every module above are byte-identical between
the two seeds. What remains on the 6107-line file is the linear interpreter
floor (~30 ms per declaration, dominated by per-call overhead), not a
quadratic term: 50 -> 200 functions now costs 4.6x for 4x.

Rust mechanism test: `src/compiler_rust/compiler/tests/interpreter_global_array_push_in_place.rs`
(pre-fix: 3,998,000 elements cloned for 2,000 allocs, x4 allocs cost x23.6;
post-fix: 0 per-frame copies, linear).

## Not changed

Value semantics, COW, the snapshot/publish protocol between frames, and the
flat `MODULE_GLOBALS` mirror are all kept; the fix only removes references
that were redundant with the store.

## Also found while here

- `origin/main` (`13d09a45d80`, "keep one dispatch profiler module owner")
  removed `pub(crate) mod dispatch_profile;` from `interpreter/mod.rs` while
  `interpreter/expr.rs:292` still calls it, so the seed did not compile
  (E0433). Restored in this change.
- Pre-existing on pristine `origin/main`, NOT caused by this change (verified
  by building the pristine tree in an isolated target dir):
  `interpreter_flattened_module_globals::flattened_same_named_global_arrays_remain_owner_isolated`
  (reads 2222, expects 1122 -- the bare-name flat `MODULE_GLOBALS` mirror wins
  over the owner scope on identifier reads, `interpreter/expr/literals.rs`)
  and `::unflattened_transitive_alias_sees_growing_global_array`. A third,
  `::inner_write_survives_two_enclosing_frame_returns`, fails pristine and
  passes with this change.
- The `X.new` special-casing at `interpreter/expr/calls.rs:413/:637` is not a
  per-call cost: `P.new(..)` measures 11.8 us vs 5.2 us for direct `Q(..)`,
  i.e. exactly one extra interpreted call, and the lexer/parser core has no
  `.new(` call sites. `:413` is only reached for a bare `X.new` used as a
  value. Lead closed.

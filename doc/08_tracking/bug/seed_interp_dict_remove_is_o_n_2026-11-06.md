# Seed interpreter `Dict.remove` is O(n) after the insertion-order switch (2026-11-06)

Status: open (perf regression, accepted for correctness; needs a follow-up).

## What

The insertion-order Dict contract (`doc/07_guide/language/dict_iteration_order.md`)
moved the seed interpreter's `Value::Dict` from `HashMap` to
`indexmap::IndexMap` (`DictMap`, `src/compiler_rust/compiler/src/value.rs`).
Keeping order on removal requires `IndexMap::shift_remove`, which shifts every
later entry: O(n) per remove instead of O(1). Call sites:
`apply_dict_mutation_in_place` in
`src/compiler_rust/compiler/src/interpreter_method/collections.rs` and
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`.

## Measurement

Fixture: insert keys 0..9999 into a `Dict<i64, i64>`, then `d.remove(j)` for
j in 0..9999 (removes from the front, the worst case for shifting).
`SIMPLE_EXECUTION_MODE=interpret`, 5 runs each, same host, load ~10:

| binary (sha256 prefix) | wall seconds |
|---|---|
| base `c512dc37c2300f20` (HashMap) | 0.06 0.06 0.07 0.07 0.06 |
| new `6aa1b055c747c97c` (IndexMap shift_remove) | 0.17 0.16 0.17 0.17 0.17 |

About 2.6x on this fixture, and the cost is quadratic in dict size for
front-heavy remove loops. The JIT / compiled runtime (`RuntimeDict`) is not
affected: its remove stays O(1) (insertion stamps), measured 0.07 vs 0.07.

## Fix direction

Tombstone the removed slot instead of shifting (e.g. store
`Option<Value>` entries in an append-only `IndexMap` and compact when
tombstones exceed live entries), or keep a stamp per entry like `RuntimeDict`.
Either keeps O(1) amortized remove with insertion-order iteration.

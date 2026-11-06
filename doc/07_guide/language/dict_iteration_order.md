# Dict Iteration Order

**Contract: builtin `Dict` iterates in INSERTION order, on every engine, on
every run.** (Owner decision 2026-11-06; supersedes the 2026-07 sorted-key
contract.)

| Form | Order |
|------|-------|
| `d.keys()` | insertion order |
| `d.values()` | insertion order (so `keys()[i]` pairs with `values()[i]`) |
| `d.entries()` / `d.items()` | insertion order |
| `for (k, v) in d` / `for k in d.keys()` | insertion order |
| `print(d)` / `"{d}"` | insertion order |

Rules:

- A new key is appended at the end.
- Setting an existing key replaces its value **in place** (position kept).
- Removing a key drops it from the order; re-adding it appends at the end.
- Order survives table growth / rehash.

`{"b": 1, "a": 2}.keys()` is `["b", "a"]`.

Code that needs a canonical order (deterministic output, byte-identical
artifacts) must sort explicitly, e.g. `for name in d.keys().sort():` — see
`src/compiler/80.driver/driver_build/smf_staged_parts_v1.spl`.

## Implementations

| Engine | Storage | How order is kept |
|--------|---------|-------------------|
| Seed interpreter (`Value::Dict`, `Value::FrozenDict`) | `Arc<DictMap>`, `DictMap = indexmap::IndexMap<String, Value>` (`src/compiler_rust/compiler/src/value.rs`) | IndexMap order; removal uses `shift_remove` (never `swap_remove` / deprecated `remove`). All order-visible boundaries go through `dict_entries_ordered` (`value_impl.rs`). |
| Rust runtime (JIT / seed native) `RuntimeDict` | open addressing (`src/compiler_rust/runtime/src/value/dict.rs`) | per-slot u64 insertion stamp stored after the (key, value) pairs in the same allocation, `next_seq` counter; `dict_collect` sorts live slots by stamp. Grow and remove-backshift carry stamps. |
| C runtime `RtCoreDict` (`src/runtime/runtime_native.c`) | open addressing + tombstones | `RtCoreDictEntry.seq` + `RtCoreDict.next_seq`; resize carries stamps (`rt_core_dict_put_seq`); `rt_core_dict_ordered_slots` feeds keys/values/entries/format. |
| Pure-Simple core runtime (`src/runtime/simple_core/core_array.spl`) | dense array | appends in order; `rt_dict_remove` shifts later entries down (no swap-remove). |
| Pure-Simple frontend interpreter (`src/compiler/10.frontend/core/interpreter`) | `__dict` struct field list | upsert appends / replaces in place. |

Lookup and insert stay O(1) on the hash-table engines; producing an ordered
view (`keys()`, `values()`, `entries()`, a `for` loop, display) costs
O(n log n) for the stamp sort.

The scope-read views (`rt_dict_scope_read_slot_v1`) still expose HASH SLOTS,
not iteration order; they are a lookup surface, not an iteration surface.

## Specs

- `test/01_unit/lib/collections/dict_insertion_order_spec.spl` — the contract.
- `test/02_integration/app/run/dict_insertion_order_parity_spec.spl` — the same
  fixture under `SIMPLE_EXECUTION_MODE=interpret` and `=jit` must print the
  same insertion-ordered output.
- Rust: `runtime/src/value/dict.rs` tests (`keys_values_iterate_in_insertion_order`,
  `replace_keeps_position_and_readd_after_remove_appends`,
  `insertion_order_survives_growth_and_remove_backshift`).
- C: `src/runtime/test/rt_dict_scope_read_selfcheck.c` (`check_insertion_order`).

## History

From 2026-07 to 2026-11 the contract was SORTED key order, chosen because the
interpreter's `HashMap` iterated in a per-process random order (15 distinct
orderings in 20 runs of a 4-key literal) and the runtime tables iterated in
slot order. The interpreter sorted at every boundary; the JIT and C runtime
never did, so engines disagreed. Insertion order is now kept by every engine
directly.

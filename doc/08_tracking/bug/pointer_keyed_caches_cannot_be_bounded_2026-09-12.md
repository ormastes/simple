# Pointer-keyed seed caches cannot be retention-bounded without re-keying

- Status: OPEN (2026-09-12)
- Area: `src/compiler_rust/compiler/src/module_cache.rs`,
  `src/compiler_rust/compiler/src/interpreter_state.rs`
- Found by: lane L4 (memory lifecycle: bounded Rust-seed interpreter caches)

## Summary

Three process-global seed caches are keyed by a **raw address**
(`Arc::as_ptr as usize` / `&FunctionDef as usize`):

| cache | file:line | key |
|---|---|---|
| `FILTERED_DICT_CACHE` | `module_cache.rs:227` | address of the source dict `HashMap` |
| `MODULE_EXPORT_OWNERS` | `module_cache.rs:239` | address of the exports dict |
| `FUNCTION_MODULE_OWNER` | `interpreter_state.rs:472` | address of a `FunctionDef` |

Those keys are unique only because the cache **retains** something that keeps
the allocation alive (`FILTERED_DICT_CACHE` stores the source `Arc<HashMap>`
alongside the filtered one, precisely for this). Retention is therefore
load-bearing for correctness, not just for speed.

The consequence is that the obvious memory fix — cap the entry count and evict
the least-recently-used entry — **introduces a silent wrong-answer bug**: the
evicted entry's allocation is freed, a later allocation can land at the same
address, and the next lookup is a false hit that returns another module's
filtered dict / another module's owner id. No error, no panic, wrong value.

This is why lane L4 bounded `PARSED_SOURCE_CACHE`, `PROBE_SOURCE_CACHE` and
`PATH_KEY_CACHE` and deliberately left these three unbounded. They remain
unbounded-growth caches in a long-lived process.

## Repro (reasoning, not yet a failing test)

No failing test is attached, because writing one requires the bound that must
not be added. The hazard is structural and can be read directly:

1. `module_cache.rs:759 filter_functions_from_value` keys the memo on
   `Arc::as_ptr(&map) as usize`.
2. The memo's value tuple's first element is the source `Arc<HashMap<...>>` —
   the only thing keeping that address reserved.
3. Drop that tuple and the address is returnable by the allocator.
4. `HashMap` allocations of the same layout are extremely common on this path,
   so reuse is likely, not theoretical.

## Fix direction

Re-key off a stable identity before bounding:

- `FILTERED_DICT_CACHE`: key on the owning module's canonical path (the same
  `normalize_path_key` the sibling caches use) rather than the dict address.
- `MODULE_EXPORT_OWNERS` / `FUNCTION_MODULE_OWNER`: carry the owner id inside
  the value/def rather than in a side table keyed by address.

Both are behaviour-visible refactors of the interpreter's ownership plumbing and
were out of scope for the memory-lifecycle lane.

## Related

- Design: `doc/05_design/compiler/interpreter/bounded_seed_interpreter_caches_2026-09-12.md` §3

# Address-keyed owner side tables re-check nothing and cannot be retention-bounded

- Status: OPEN (2026-09-12)
- Area: `src/compiler_rust/compiler/src/module_cache.rs`,
  `src/compiler_rust/compiler/src/interpreter_state.rs`
- Found by: lane L4 (memory lifecycle: bounded Rust-seed interpreter caches)

## Summary

Two process-global seed side tables are keyed by a **raw address** and neither
retains the allocation that address names, nor re-validates it on a hit:

| table | file:line | key | written by |
|---|---|---|---|
| `MODULE_EXPORT_OWNERS` | `module_cache.rs:239` | `Arc::as_ptr(dict) as usize` | `cache_module_exports` (`:525`) |
| `FUNCTION_MODULE_OWNER` | `interpreter_state.rs:472` | address of a `FunctionDef` | `tag_function_module_owner` |

`module_exports_owner` (`module_cache.rs:539`) is the whole read path:

```rust
MODULE_EXPORT_OWNERS.with(|cache| cache.borrow().get(&(Arc::as_ptr(dict) as usize)).cloned())
```

There is no `ptr_eq` re-check and no retained `Arc`. These keys are unique only
because a **different** cache — `MODULE_EXPORTS_CACHE` / `MODULE_FUNCTIONS_CACHE`
— holds the object for the life of the process.

The consequence is a coupling that is invisible at both call sites: giving
`MODULE_EXPORTS_CACHE` or `MODULE_FUNCTIONS_CACHE` any release path (a retention
bound, an unload, an LRU) frees the address, a later allocation can land on it,
and the next `module_exports_owner` call returns **another module's owner id**.
No error, no panic, wrong value.

Contrast `FILTERED_DICT_CACHE` (`module_cache.rs:227`), which is keyed the same
way but *does* re-check — its hit path is
`get(&key).and_then(|(src, out)| Arc::ptr_eq(src, dict).then(...))` — so a
recycled address is a miss and a rebuild. That is why lane L4 was able to bound
`FILTERED_DICT_CACHE` and could not extend a bound to these two or to the
definition caches they depend on.

## Repro (reasoning, not a failing test)

No failing test is attached, because reproducing it requires adding the release
path that must not be added until this is fixed. The hazard is structural and
reads directly off the source:

1. `cache_module_exports` stores `Arc::as_ptr(dict) as usize -> owner`, keeping
   no reference of its own.
2. The dict stays alive only via `MODULE_EXPORTS_CACHE`, which today is never
   released except by a whole-cache `clear_module_cache*`.
3. `module_exports_owner` looks the address up and returns whatever it finds.
4. Any future partial release of `MODULE_EXPORTS_CACHE` makes step 3 a lookup on
   a possibly-recycled address.

## Fix direction

Either re-validate like `FILTERED_DICT_CACHE` does (store the `Arc` alongside
the owner and `ptr_eq` on the hit path), or — better — carry the owner id inside
the value/def instead of in an address-keyed side table. The second removes the
coupling rather than documenting it.

## Related

- Design: `doc/05_design/compiler/interpreter/bounded_seed_interpreter_caches_2026-09-12.md` §3

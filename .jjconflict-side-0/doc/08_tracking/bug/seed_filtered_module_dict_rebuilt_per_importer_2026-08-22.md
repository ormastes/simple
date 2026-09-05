# Seed interpreter rebuilt every imported module's export dict once per importing module

**Status:** FIXED 2026-08-22 (seed, `src/compiler_rust/compiler/src/module_cache.rs`).
**Class:** memory retention — O(importers x exports) materialisation; second slice of the
"per-module env/export materialisation" item in
`memory_retention_compiler_and_interpreter_2026-08-21.md` (first slice:
`seed_empty_captured_env_allocated_per_import_binding_2026-08-22.md`).

## Mechanism

`use pkg.x` binds module `x`'s export dict (one shared `Arc<HashMap>`) into the importer's
env. When the importer's env is frozen, `create_filtered_env` walks every value through
`filter_functions_from_value`, and for a `Value::Dict` that REBUILT the whole map — new
`String` keys, new `Value::Function`s — and retained the copy in the importer's frozen env
(`MODULE_ENV_BY_OWNER`, plus every exported function's shared-base env). The result is a pure
function of the source dict's contents, so the N copies held by N importers were byte-identical.
This is the "a 3.4 KB source file can own a 5000-entry environment" effect.

## Fix

Thread-local memo `FILTERED_DICT_CACHE`: source `Arc` pointer -> (clone of the source `Arc`,
filtered `Arc`). Holding the source Arc means its address cannot be recycled while the entry
is live, so a pointer hit is always the same dict; `Arc::ptr_eq` is re-checked on read.
Cleared in `clear_module_cache`; `clear_module_cache_selective` drops entries whose source
is no longer held by anyone else. Value semantics unchanged: `Value::Dict` is COW
(`Arc::make_mut` clones on write), so importers sharing one filtered Arc can never observe
each other.

Counters: `FILTERED_DICT_BUILDS` / `FILTERED_DICT_HITS` (`SIMPLE_PERF_COUNTERS=1`).

## Measured

See the table appended below (seed `simple.fix2` vs `simple.fix3`, interpret-mode lint of
`driver_types.spl`, 163 module loads).

## Pin

`src/compiler_rust/compiler/tests/interpreter_filtered_module_dict_memo.rs`: 6 modules importing
the same base module -> >= 5 memo hits, builds do not scale with importers (pre-fix: 0 hits,
6 builds). Gate row in `scripts/check/check-perf-regression-tests.shs`.

| (interpret lint `driver_types.spl`, 163 modules, 2 runs each, identical) | fix-2 (`7fe00b1c4d5`) | fix-3 |
|---|---|---|
| `eval_retained` | 105.7 MB | **92.3 MB** (-13%) |
| live at exit | 185.8 MB | 172.3 MB |
| peak live | 316.5 MB | 303.1 MB |
| max RSS | 386 / 386 MB | 370 / 372 MB |
| `FILTERED_DICT_BUILDS` / `HITS` | 629 / 0 (by construction) | 165 / 464 |

Cumulative from the fix-1 seed: eval_retained 157.2 -> 92.3 MB (-41%), live 237 -> 172 MB.

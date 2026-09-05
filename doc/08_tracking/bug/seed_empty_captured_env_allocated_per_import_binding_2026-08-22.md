# Seed interpreter allocated a fresh empty `captured_env` for every imported-function binding

**Status:** FIXED 2026-08-22 (seed, `src/compiler_rust/compiler`).
**Class:** memory retention — O(modules x visible names) materialisation
(`memory_retention_compiler_and_interpreter_2026-08-21.md`, "Open: per-module env/export
materialisation"). This is the first concrete slice of that open item.

## Mechanism

A module's frozen env is built by `create_filtered_env` → `filter_functions_from_value`
(`module_cache.rs`), which rebinds every imported `Value::Function` with an EMPTY
`captured_env` (deliberately, to stop nested-env growth). It did so with `Arc::new(Env::new())`
per entry. `CowEnv` is ~9 maps/sets plus an `Arc<HashMap>` (`global_bindings`) — two heap
allocations, ~600 B, per binding, per importing module, retained for the life of the process
by `MODULE_ENV_BY_OWNER` and every exported function's shared-base env. Same pattern at the
method-export sites in `evaluation_helpers.rs` (4) and `module_merger.rs` (1). A native-build
shard carries ~950k env entries (`[mem] env_entries`), so the empties alone were ~0.5 GB that
encoded nothing.

## Fix

`CowEnv::shared_empty()` (`value.rs`): one thread-local `Arc<CowEnv>`; the seven retention
sites use it. Semantics unchanged: nothing mutates an empty captured env in place —
`Arc::make_mut` on a shared Arc clones first, and the sites were already constructing a value
no one could distinguish from any other empty env.

## Measured (`SIMPLE_EXECUTION_MODE=interpret SIMPLE_MEM_TRACE=1 simple lint driver_types.spl`, 163 module loads, two runs each, identical across runs)

| | fix-1 seed (`a3a8d05e822`) | fix-2 |
|---|---|---|
| `eval_retained` | 157.2 MB | **105.7 MB** (-33%) |
| live at exit | 237.3 MB | 185.8 MB |
| peak live | 368.0 MB | 316.5 MB |
| max RSS | 437 / 449 MB | 402 / 391 MB |
| wall | 62 / 43 s | 45 / 40 s (shared box; not a claim) |

## Pin

`src/compiler_rust/compiler/tests/interpreter_shared_empty_captured_env.rs`: a module importing
400 functions must add >= 400 holders to `Env::shared_empty()` (pre-fix: 0 new holders, FAIL).
Gate row in `scripts/check/check-perf-regression-tests.shs`.

## Still open in the same item

The filtered env itself is still one `(String, Value)` entry per visible name per importing
module (48,879 import bindings here); `filter_functions_from_value` also rebuilds imported
module DICTS per importer. Those are the remaining O(modules x names) terms.

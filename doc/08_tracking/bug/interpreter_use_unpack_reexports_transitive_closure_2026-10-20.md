# Seed interpreter: every `use` re-exports the imported module's whole surface (O(closure) tables per module)

Status: FIXED (work/interp-reexport-sharing) — tables are shared by reference; name resolution unchanged (see "Fix").
Found by: 2026-10-19 full sweep memory cluster (212 specs `memory allocation failed`).
Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (seed `b5482745b46`), worktree `release_phase3` @ `10ecc006b67`.

## Symptom

Specs that import compiler or app modules need 3.6-6.2 GB RSS before their first
example runs. Measured with `/usr/bin/time` + `/proc/<pid>/status` sampling, no
runner limit, `systemd-run --user --scope -p MemoryMax=8G`:

| spec | VmPeak | VmHWM (peak RSS) | wall |
|---|---|---|---|
| app/bootstrap_builder/grouped_native_worker_spec | 6.66 GB | 5.42 GB | 83 s |
| app/test_daemon/test_daemon_gui_routing_spec | 7.71 GB | 6.04 GB | 89 s |
| compiler/assurance/policy_five_site_convergence_spec | 7.71 GB | 6.19 GB | 95 s |
| compiler/driver/admitted_epoch_spec | 6.66 GB | 5.10 GB | 74 s |
| compiler/loader/aspect_catalog_invalidation_spec | 6.66 GB | 5.40 GB | 75 s |
| compiler/cache/driver_hir_shard_transaction_spec | 4.57 GB | 3.60 GB | 48 s |
| compiler/linker/extern_unimplemented_weak_stub_fabrication_spec | 4.57 GB | 3.66 GB | 45 s |
| 02_integration/t32_hw/backends/config_file_spec | 7.71 GB | 6.01 GB | 73 s |

`SIMPLE_EXECUTION_MODE=interpreter` gives the same peak (5.29 GB for
grouped_native_worker), so the JIT attempt is not the cost.

## Where the memory goes

RSS time series for admitted_epoch: 1.0 GB at 5 s (parse + flatten), then a
linear ramp to 5.2 GB over the next 46 s with no output, then all 13 examples
finish in 0.3 s. The ramp is interpreter module evaluation.

`SIMPLE_MEM_TRACE=1` at 1000 of 1161 loaded modules (no repeat loads):

```
phases: module_loads=1000 source=16.7MB parse_retained=31.3MB eval_retained=1958.9MB
        env_entries=2435815 export_entries=2418224
globals census: import_bindings=2425606
22.56MB self  src= 14754B items= 31 env=16322 exp=16305  80.driver/cache/driver_hir_post_validation_policy_v1.spl
13.84MB self  src=  4227B items= 15 env=16518 exp=16496  80.driver/driver_compiler_type.spl
```

A 4 KB, 15-item file retains 13.8 MB because its env, its exports and its
import-binding table each hold ~16,500 names. Parse is 31 MB; evaluation
retains 2 GB, all of it in these per-module name tables.

## Root cause

`process_use_stmt` in
`src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
(the `for (name, export_value) in module_exports.iter()` loop, ~line 608)
inserts EVERY export of the imported module into the importer's `env`, its
`exports`, and `record_import_binding`, whatever the `ImportTarget` is. A
`use X.{a}` therefore re-exports all of X's surface, and X's surface already
contains everything X imported. Exports grow with the transitive import
closure, so total retained entries are roughly modules x closure width:
quadratic in the import graph.

## Decision needed

Restricting `exports` to locally defined items plus explicit `export` /
`export use` would make the tables linear. It also changes which names are
visible through `use Y.{z}` when `z` reached `Y` only through a plain `use`.
The sweep already has 87 specs failing "module does not export symbol" in the
strict lanes, so code does lean on this permissiveness. Two separable behaviours:

1. env visibility inside the importing module (needed for the module's own code);
2. re-propagation into the importer's `exports` (only needed for transitive
   leakage).

Dropping (2) alone is the memory fix. It needs a whole-suite run before and
after on the same binary, with the newly failing set reviewed name by name.

## What landed instead (work/sweep-alloc-abort)

The runner fix: dir-mode spec children no longer get a 3 GiB RLIMIT_AS (which
counts reserved but untouched VA). Memory is capped through a per-child
`systemd-run --user --scope` MemoryMax at `--max-mem`, and an overrun is
reported as `TERMINATED: Memory limit exceeded` instead of a SIGABRT crash. The
specs above now run to their real verdict under the default 16 GiB cap. Their
RSS is unchanged until this bug is fixed.

## Fix (2026-10-20, work/interp-reexport-sharing)

Option A, no semantics change: the importer records the imported module's
table and resolves through it lazily instead of copying it. The permissive
rules stay exactly as they were (`use m.{x}` still binds m's whole surface,
including what m only imported); the "Decision needed" above is not taken.

- `ModuleTable` (value.rs): a module's export `Value::Dict` holds only its own
  entries; whole imports are `layers` (`Arc<ModuleTable>`), looked up own
  first, then latest layer first. Pushing a layer evicts the own entries it
  rebinds, which reproduces last-insert-wins. Lookups use a process-wide
  name -> defining-tables index plus a per-table reachability set, so no
  per-(table, name) state is kept.
- `LayeredEnv` replaces the frozen module env (`MODULE_ENV_BY_OWNER`, every
  exported function's `captured_env` base); filtered layers read
  `ModuleTable::filtered_own`.
- `ModuleBindings` gains binding layers (snapshot of the source module's
  table at import time), so `import_bindings` no longer copies.
- `ProvidedSet` reads the shared export table.
- Every place that reads a module value by name goes through
  `module_dict_get` / `module_dict_for_each_visible` / `module_dict_len`
  (module_cache.rs registry keyed by dict address); dict collection methods
  on a module value see the flat surface via `module_dict_flat`.
- Lookup memos are owner-thread only (no lock on the hit path).

Not routed through the registry: `==` between module values and printing a
module value see the module's own entries only. Writes into a module value
(`m.x = v`, `m[k] = v`) first materialize the flat surface, so the written
copy keeps every name.

Measured, same worktree, `run` in an 8 GiB scope (peak RSS, user CPU):

| spec | before RSS | after RSS | before user | after user |
|---|---|---|---|---|
| compiler/driver/admitted_epoch | 5.48 GB | 1.72 GB | 32.2 s | 12.2 s |
| compiler/loader/aspect_catalog_invalidation | 5.81 GB | 1.83 GB | 35.9 s | 12.3 s |
| compiler/cache/driver_hir_shard_transaction | 5.09 GB | 2.10 GB | 25.4 s | 10.7 s |
| app/bootstrap_builder/grouped_native_worker | 5.75 GB | 1.77 GB | 31.9 s | 10.6 s |

Spec output is byte-identical before/after (modulo temp-dir names). A 40-module
`use prev.*` chain: export entries 4100 -> 239, env entries 4379 -> 518,
import bindings 3940 -> 79. Lookup-heavy loop (300k iterations of
cross-module unqualified + qualified calls, min of 7, host load ~28):
2.59-3.02 s before, 2.68 s after. Plain-dict loop (1.5M iterations of
`d[k] = v`, `d.len()`, `d.get(k)`, `k in d`): min 3.09 s -> 3.16 s, median
3.45 s -> 3.24 s (within noise). Plain dicts reach the module-dict registry
only through a lock-free address filter.

126 interpreter / module-import specs: identical verdicts before and after
(`me_call_dict_field_write_cost_spec` is timing-flaky under load on both
binaries). Rust `simple-compiler --lib`: 4468 pass; the same 11
native_project/vulkan failures exist on the base commit.

Tests: `test/01_unit/compiler/interpreter/use_reexport_sharing_equivalence_spec.spl`
(fixture graph `test/fixtures/interp_reexport_sharing/`, expected values
recorded from the copying seed) and the Rust unit test
`chained_glob_imports_retain_tables_linear_in_own_exports`.

The pure-Simple interpreter (`src/compiler/10.frontend/core/interpreter/`)
does not have this pattern: `extract_module_exports` reads only a module's own
declarations and imports bind per caller.

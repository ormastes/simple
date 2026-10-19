# Seed interpreter: every `use` re-exports the imported module's whole surface (O(closure) tables per module)

Status: OPEN — root cause located, fix needs a semantics decision (see "Decision needed").
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

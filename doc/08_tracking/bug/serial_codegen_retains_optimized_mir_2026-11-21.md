# Serial LLVM codegen keeps every module's optimized MIR live for the whole build

- **Date:** 2026-11-21
- **Area:** `src/compiler/70.backend/backend/backend_helpers.spl` (`compile_llvm_module_to_object_path`)
- **Status:** fix landed in source, **unmeasured** (see "Verification")
- **Related:** `codegen_module_memory_not_freed_per_module_2026_11_02`,
  `stage3_c_runtime_worker_memory_2x_2026-11-20` (the pool-lane sibling of this bug)

## Symptom

A 1601-module pure-Simple compiler build (`--backend llvm`, serial codegen lane)
was killed by its cgroup memory cap during native codegen.

Log `~/.simple/prov/p3/build.attempt3-cgroup-oom-after-codegen.log`:

```
[mir] 1601/1601 rss_mib=21222 elapsed_s=9951 module=lib.common.build_progress.__init__
[build] phase=native_compile state=running unit_kind=modules done=63 total=1601 remaining=1538 ...
[NATIVE] codegen: 1538 uncached module(s), concurrency=1 (serial lane in this process: one worker admitted (cpus=64 budget_kib=44000000 headroom_kib=25079324))
exit=143
```

The log carries no line between the `[NATIVE] codegen` banner and the kill: the
serial lane printed nothing per module. Observed outside the log by the
operator of that run: the process passed 44 GB (the cap) and was killed after
all 1538 objects had been written. From 21.2 GB to >44 GB over 1538 modules is
roughly 15 MiB of growth per module.

## Cause

`compile_llvm_module_to_object_path` ran each module in two transient scopes:

1. scope A: storage lowering + `optimize_module_for_backend`, then
   `transient_promote<MirModule>(backend_module)` and scope end;
2. scope B (inside `llvm_compile_module_direct_to_path`): translation + object
   emission, nothing promoted.

Promotion makes the optimized MIR copy persistent. The runtime has no
collector, so each module's optimized MIR stayed live until process exit.
Scope B frees the IR text, but the MIR it was translated from had already
escaped scope A.

The promoted module has exactly one consumer: the
`llvm_compile_module_direct_to_path(options, backend_module, ...)` call that
immediately follows, which returns an `i64` status. Nothing reads the MIR
after the object file is written, so the promotion bought nothing but the
ability to end scope A before scope B began.

The pool-lane sibling `llvm_module_ir_to_path_v1` (same file) already holds
one scope across lowering, optimization, translation and the IR write, and
promotes only a failure-reason text.

## Fix

`compile_llvm_module_to_object_path` now holds ONE transient scope across
storage lowering, MIR optimization, IR translation and object emission, and
promotes nothing (the result is a scalar status). The warm-ups that
`llvm_compile_module_direct_to_path` performs before its own scope
(`llvm_object_tool_v1()`, `bootstrap_llvm_name_index_ensure()`) and the target
config resolution now run before the single scope; the bootstrap string
globals are retained before scope end, as before.

The previous two-scope lane (with the MIR promotion) is kept only for the two
cases in which `llvm_compile_module_direct_to_path` itself declines to scope:
`SIMPLE_CODEGEN_MODULE_SCOPE=0` and `SIMPLE_LLVM_BITCODE_DEBUG=1`.

One ordering difference, shared with the pool sibling: `reset_provider_report()`
now runs after translation rather than between optimization and translation.
The provider report is written only by `60.mir_opt` and reset by drivers;
nothing under `70.backend` reads it.

## Attribution for the next failure

The serial lane now prints, every 50 completed modules and at the end, a line
shaped like the MIR one:

```
[codegen] 1500/1538 rss_mib=<n> elapsed_s=<n> module=<name>
```

(`log_codegen_progress_module_done`, `src/compiler/80.driver/driver_log_helpers.spl`;
counted in `_compile_frozen_module_capsule_prefetched_v1`.)

## Verification

**Unmeasured.** Rebuilding the compiler to observe the effect costs hours and
more than 40 GB and was not done. What was checked:

- by reading: the single consumer of the promoted MIR, and that nothing in
  `70.backend` reads the provider report;
- syntax only: isolated copies of the new helper code and of the new control
  flow shape were compiled with the bootstrap compiler on a small fixture.

Not checked: that the edited compiler sources build, that objects are
byte-identical to the two-scope lane, and the actual RSS slope. The first
build that includes this change should read the `[codegen]` lines: a flat
`rss_mib` confirms the fix; a slope that persists means another per-module
retainer exists and this record should be reopened.

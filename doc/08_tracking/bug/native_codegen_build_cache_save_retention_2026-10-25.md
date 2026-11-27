# Native codegen keeps every build-cache save (2026-10-25)

**Status:** fixed (`build_cache_persist` runs in a transient scope),
`src/compiler/80.driver/driver_build/incremental.spl`.
**Lane:** Phase 3 native-build, codegen in MIR fork workers
(`SIMPLE_CODEGEN_MODULE_SCOPE=1`).

## Symptom

A codegen worker's Private_Dirty grew by several MB for every module it
compiled, even with the per-module codegen scope on.

## Root cause

After each module, `driver_native_collect_capsule_result_v1`
(`driver_aot_native_output.spl`) calls `build_cache.save()` →
`build_cache_persist`. That function rebuilds the whole cache file on every
call: one row per entry, the joined text, the reverse-reference generation,
and its encoded receipt. The runtime has no collector, and this ran outside
any transient scope, so every save's scratch stayed allocated for the life of
the process. Each save costs O(entries) and the cache grows by one entry per
module, so the total retained memory grows quadratically.

Measured with temporary heap probes around the per-module steps (142-module
closure, 2 fork workers, 373 module completions):

| step | objects / module | header bytes / module |
|---|---|---|
| codegen itself (inside the module scope) | ~260 | ~19 KB |
| collect, before save | ~0 | 55-740 KB |
| `build_cache.save()` | ~58,000 | 4.2 MB at the first save, rising to 10.5 MB |

## Fix

`build_cache_persist` wraps its body in `transient_scope_begin` /
`transient_scope_end`. Only the bool result leaves the scope. Nothing on that
path writes a persistent object or a module-level `var`. Inside a caller's
scope (scopes do not nest), the save runs unscoped exactly as before.

Residual, not fixed here: the collect step re-reads each module's source to
re-check its identity, which costs about 0.1 MB per module.

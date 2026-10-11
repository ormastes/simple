# Opt-in Windows HIR worker diagnostic workaround

Use only when an admitted compiler's optional HIR warmup fails before publishing a child diagnostic. Track [BUG-WIN-HIR-WORKER-DIAGNOSTICS-20261010](../../08_tracking/bug/windows_hir_worker_diagnostics_2026-10-10.md); it remains open. This option is not a compiler fix or a default build setting.

In a POSIX-compatible shell, source the helper and enable it in a subshell around the same already-admitted command:

```sh
(
    . scripts/bootstrap/workarounds/hir-worker-diagnostics.shs
    simple_enable_hir_worker_diagnostics_workaround
    "$SIMPLE_BINARY" native-build "$@"
)
```

`SIMPLE_BINARY` and all arguments must come from the caller's verified compiler/request. This example supplies no invented target, runtime, source root or output. Sourcing the file alone does nothing. Calling the function sets only `SIMPLE_HIR_SHARDING=0`; the subshell prevents leakage to subsequent builds. Preserve canonical source/cache authority, no-stub setting, memory/time admission and complete receipts. Do not set marked-worker variables, bypass validation, convert an error into success or restart a capped attempt.

The inspected source skips optional asynchronous HIR warmup and retains ordinary compilation. Confirm actual path behavior for the selected producer;80030 embedded source binding for the seven motivating failures is unproven. Tests, warnings and compiler errors remain real. Reuse valid caches through normal keys; do not relabel cache identities.

Recovery: apply and qualify the underlying process/diagnostic repair, then narrowly remove the explicit opt-in and helper in a linked recovery commit. Fetching a fix alone is insufficient. The bug record preserves original sources, private experiment/recovery identities and the public workaround link.

Configuration regression: `sh test/00_unit/scripts/hir_worker_diagnostics_workaround_test.shs`. This checks the helper's actual shell behavior only; it does not rerun the seven original native attempts or establish any of the six full subsystem binaries.

Portable workaround commit: [99c65b91e269e3c4c489a859d94a0e2c741bb645](https://github.com/ormastes/simple/commit/99c65b91e269e3c4c489a859d94a0e2c741bb645). Recovery baseline remains `d6abe34243c4ea9365454eca4c7e8586b8d216bf`.

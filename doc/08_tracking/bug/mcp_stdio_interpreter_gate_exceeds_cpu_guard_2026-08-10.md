# MCP stdio interpreter gate exceeds the CPU guard

Status: claimed by Codex `/root` (2026-08-10)

## Exact failure

The required user-facing gate

```text
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
```

is killed before any scenario executes. The bounded baseline on 2026-08-10 was
68.18 seconds wall time, 1,337,660 KiB max RSS, and 96.6% CPU. The terminating
diagnostic is `killed by kill_simple_monitor (cpu=96.6% age=67s>=60s)`.

Immediately before termination the driver reports that `SIMPLE_LIB=src`
contains 600+ `.spl` files and emits warnings from the full test-runner import
closure. This record owns diagnosis and a pure-Simple/tool-driver fix for the
unbounded one-file test startup work. The next diagnostic run raises only the
existing CPU watchdog so the underlying MCP scenario failures can be observed;
that run is diagnostic evidence, not a passing gate.

## Owner-boundary decision

- `runtime_need`: none established.
- `facade_checked`: test-runner single-file discovery/import loading and the
  MCP spec's existing `std.*` facades.
- `chosen_path`: fix the pure-Simple/compiler/test-runner owner after profiling.
- `rejected_shortcuts`: permanently raising/disabling the watchdog, switching
  to the Rust seed, weakening scenarios, or removing `SIMPLE_LIB=src` from the
canonical contract.

A watchdog-raised diagnostic was stopped after 111.33 seconds and 2,503,188
KiB max RSS because it still had not entered a scenario. Source inspection
locates the scaling trigger at
`src/compiler/80.driver/driver_source_pipeline_loading.spl:268`: every
non-check project input bulk-loads all of `src/app`, `src/lib`, `src/compiler`,
and `src/runtime` unless native entry-closure mode is active.

The adjacent `scripts/check/check-mcp-native-smoke.shs` gate fails too. Its
wrapper contracts pass, but admitted `simple_mcp_server` and
`simple_lsp_mcp_server` artifacts are absent. Setup also reports JIT fallback
for unresolved `rt_file_is_char_device`. The pure-Simple declaration is at
`src/lib/nogc_sync_mut/io_runtime.spl:52`; interpreter and C implementations
exist, while the JIT runtime symbol list currently includes neighboring
`rt_file_is_regular_no_follow` but not `rt_file_is_char_device`
(`src/compiler_rust/common/src/runtime_symbols.rs:966`). That is sufficient
evidence that this adjacent defect is below the pure-Simple facade boundary.

The canonical MCP native-build attempt reproduces the startup defect in its
worker path: `src/app/cli/native_build_main.spl:246` dispatches through
`bin/simple run src/app/cli/native_build_worker.spl`. The worker stayed at
~100% CPU and ~2.73 GiB RSS for 4 minutes 35 seconds without emitting a build
phase or artifact, so the attempt was stopped rather than masking the issue
with a longer timeout.

## Current coordination blocker

The owner files needed for the two fixes overlap active external work:
compiler/test-runner files are dirty while a Stage-3 bootstrap is running, and
`src/compiler_rust/common/src/runtime_symbols.rs` has unrelated uncommitted
edits. Preserve those edits. Resume after their owning sessions settle by
implementing a general import-closure load for interpreted single-entry
`run`/`test` (without reusing the native-only environment contract), then add
`rt_file_is_char_device` to the registered JIT runtime provider and rebuild the
fresh MCP/LSP artifacts.

## Pure-Simple source fix

Implemented in the clean owner on 2026-08-10:
`driver_source_pipeline_loading.spl` now excludes explicit
`CompileMode.Interpret` from `needs_bulk_project_sources`. Check and native
entry-closure behavior are preserved, and other compilation modes retain their
existing bulk-source model. The adjacent source contract is
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.

This is not yet runtime PASS evidence. Both a focused spec invocation and a
`bin/simple check` invocation dispatch through interpreted app entries in the
stale deployed binary and hit its pre-fix bulk loader before reaching their
targets. A concurrent Stage-3 bootstrap owns deployment and was still active
when this record was updated. Do not rerun the same stale-binary commands;
resume with the freshly admitted binary and record one result per gate.

Rust/runtime work is not authorized by current evidence. It would require a
profile proving correct pure-Simple delegation and a bottleneck below that
boundary.

## Unblock condition

The exact command completes under the normal resource guard with real MCP
assertions, and an adjacent MCP regression covering the same owner path passes.

# MCP stdio interpreter gate exceeds the CPU guard

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## Superseding implementation evidence (2026-08-10)

The earlier native-artifact and Rust-authorization statements describe the
initial reproduction, not current state. Pure-Simple delegation was confirmed:
the declaration, interpreter implementation, and C runtime implementation of
`rt_file_is_char_device` were already correct. The defect was below that
boundary, so the common JIT symbol list and Rust runtime metadata/export chain
were repaired with unrelated shared-file hunks preserved.

Host MCP and LSP MCP binaries now exist with matching SHA-256 admission
sidecars. Direct production-wrapper probes return real initialize responses
with exit 0 for both servers. The first-run LSP functional probe also retained
its initialize/list/`lsp_symbols` checks, but its allowance increased from 10
to 30 seconds because the real probe completed in about 9 seconds under load
and raced the former threshold. These results close the original
missing-artifact handshake failure; they do not close the interpreter gate.

The remaining bootstrap loop is now bounded with stronger evidence:

- the deployed `bin/simple` is still the 2026-08-09 Rust seed, SHA-256
  `166c622b30c2257c9b0fbb0a5f08078f27f51d2c491305533ecf6a21ba5a35fb`;
- the old admitted Stage-2 compiler completes a synthetic 40-module dense-glob
  closure in 26.13 seconds and 80 modules in 122.17 seconds, but the 160-module
  row times out after 600.01 seconds with no artifact (159,488 KiB max RSS),
  proving superlinear time rather than memory exhaustion for that reproducer;
- canonical isolated Stage-2 seed builds with LLVM fail because both available
  Rust seeds lack LLVM support;
- the available Cranelift launcher returned before its native-build child. The
  child reached about 184% lifetime CPU and 327 MiB RSS, then its only child
  (`simple-main`, PID 876298) became a zombie while the parent (PID 876269)
  slept on a futex. No output artifact or cache file existed. This is the exact
  failure family tracked by
  `native_build_worker_zombie_parent_hang_2026-07-03.md`; both owned PIDs were
  terminated after confirmation.

Three distinct bootstrap probes are exhausted for this session. Unblock now
requires a fresh session to use the tracked direct-run bootstrap workaround
(bypassing the broken native-build worker wrapper), sanity-pass its pure-Simple
compiler, and then prove Stage-3 self-host equivalence. Only that compiler may
run the exact MCP interpreter gate for the after-fix wall/RSS comparison and
final scenario verdict.

## Verification 2026-08-17 (w02/s4 lane) — `rt_file_is_char_device` half is FIXED

Classified by CONTENT of current source (session brief CORRECTION 1).

This doc bundles two claims. The **unresolved `rt_file_is_char_device`** half
(named at line 44) is fixed; the symbol is now complete across all three layers
it needs to exist in:

- **Declared** (Simple extern): `src/lib/nogc_sync_mut/io_runtime.spl:52`
  `extern fn rt_file_is_char_device(path: text) -> bool`, with a caller at `:250`
  and a rationale comment at `:245`.
- **Defined** (C runtime): `src/runtime/runtime.c:1172`
  `int rt_file_is_char_device(const uint8_t* path_ptr, uint64_t path_len)`,
  documented at `:1164` as a "no-shell stat(2) probe".
- **Registered in the MIR extern ABI allowlist** — the actual resolution
  mechanism, and the one whose absence produces an "unresolved" symbol:
  `src/compiler/50.mir/text_extern_abi.spl:74` lists `"rt_file_is_char_device"`
  in the text-ABI extern match arm alongside `rt_file_exists`,
  `rt_file_canonicalize`, etc.

`src/runtime/runtime_native.c:8258` additionally refers to this in the past
tense as "the rt_file_is_char_device defect (fixed ...)". (That comment cites a
SHA; per CORRECTION 1 the SHA proves nothing — the three content facts above
are what settle it.)

**Verdict on the `rt_file_is_char_device` half: ALREADY FIXED. No patch applied.**

**Explicitly NOT proven, and the row should stay open for it:** the *other* half
of this doc — that the **MCP stdio interpreter gate exceeds the CPU guard** — was
not measured by this lane. That is a performance/timeout claim requiring a real
run of `test/02_integration/app/mcp_stdio_integration_spec.spl`, which this lane
could not schedule: the host is under a live stage-3 bootstrap with 164
concurrent `simple` processes, and the one spec this lane did queue
(`iso_use_after_move_e2e_spec.spl`) was still waiting on `test-slot.shs` after
25+ minutes. Do not read this note as closing the CPU-guard claim.

Note also `src/compiler/50.mir/**` is claimed by another lane this session; the
`text_extern_abi.spl` reference above is a READ for evidence only — nothing under
`50.mir` was edited here.

# Bug: `browser_session_fetch_wasm_chain_spec.spl` file-level FAIL despite 250/250 passing

- **Date:** 2026-06-30
- **Status:** Open
- **Component:** test runner (`src/app/test_runner_new/`) — NOT the js/web library under test
- **Severity:** Medium (false-negative test result; the code under test is correct)
- **Spec:** `test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl` (250 it-blocks, ~6370 lines)

## Symptom

`bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl`
reports `Files: 1, Passed: 0, Failed: 1` (file-level FAIL). The captured child
output contains only a partial prefix of `✓` lines (observed **111, 122, and 123**
across separate runs — non-deterministic) with **no `✗` failures** and **no
`N examples, M failures` BDD summary line**. The child exits non-zero with no
panic/abort text. Duration ~64s.

## Evidence the spec and library are CORRECT

Run directly in the interpreter, the spec passes in full, deterministically:

```
bin/release/x86_64-unknown-linux-gnu/simple run <spec>
  -> 250 examples, 0 failures   (exit 0, ~104s, peak RSS 315 MB)
```

Replicating the runner's exact child command (the runner uses
`build_child_args` => `["run", <spec>]` wrapped by `process_run_timeout_unix`
=> `timeout 120 simple run <spec>`) with output captured through a pipe also
passes in full:

```
( timeout 120 simple run <spec> 2>&1 | cat )
  -> 250 examples, 0 failures   (exit 0)
```

The 124th it-block (the first one missing its `✓`, `compares compileStreaming
and instantiateStreaming memory maximum failures in browser scripts`, spec line
4271) **passes in isolation** when extracted into a standalone spec.

## Ruled out

- **Not a per-block defect:** block 124 passes alone; the spec passes 250/250 via `simple run`.
- **Not host OOM:** host had **119 GB free** during the failing run; no `dmesg` oom-killer event. (Child peak RSS is only ~315 MB.)
- **Not the 120s timeout:** child stops at ~64s, well under the 120s `process_run_timeout` budget; exit code is not the timeout marker (124/-1).
- **Not a pipe-buffer deadlock:** total child output is only ~21 KB (≈10.9 KB at block 122), far below the 64 KB pipe buffer.
- **Not infix-matcher preprocessing:** the spec uses method-form `expect(x).to_equal(y)`, so `preprocess_infix_matchers_only` is a no-op (temp == original).
- **Not the SMF/compile path:** default mode is `TestExecutionMode.Interpreter` (`run_test_file_interpreter`). (Separately, `simple compile <spec>` fails with `semantic: undefined identifier: NATIVE_PROMISE_THEN` — a distinct compile-mode resolution gap, see below.)

## Root cause (narrowed)

The failure is reproducible **only** when launched through `bin/simple test`
(the test-runner parent), never when the identical child command is run in
isolation. The long-running (~64-104s), memory-growing child (no GC =>
allocate-and-leak, climbing to ~315 MB RSS / higher VSZ) is being terminated
prematurely and non-deterministically by the test-runner harness. The most
likely mechanism is a resource monitor / watchdog in the runner
(`src/app/test_runner_new/test_runner_resources.spl` `default_resource_limits`
= `memory_mb_limit: 512`, `cpu_percent_limit: 200%`; `system_monitor.spl` /
`process_monitor` `exceeds_limits`) sampling the child and killing it when a
sampled metric (VSZ, accumulated CPU, or wall time) crosses a threshold — the
non-deterministic stop point (111/122/123) matches sampling-race behaviour.

This is a test-runner / no-GC-memory-growth interaction, not a defect in the
`std.gc_async_mut.web.browser_session*` or `std.nogc_sync_mut.js.engine` code
exercised by the spec.

## Reproduction

```
# FAILS (file-level), non-deterministic ✓ count:
bin/simple test test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl

# PASSES 250/250 (identical child command, isolated):
bin/release/x86_64-unknown-linux-gnu/simple run \
  test/01_unit/lib/common/web/browser_session_fetch_wasm_chain_spec.spl
```

## Suggested remedies (test-runner scope — not attempted here)

1. Verify/raise the per-child resource-monitor ceiling for the default
   interpreter path (the child legitimately needs ~315 MB; a 512 MB sampled
   ceiling on VSZ would explain the kill), or exempt single-file runs from the
   watchdog.
2. When the child is killed by the harness watchdog, record an explicit
   `error` (signal/limit reason) in `make_result_from_output`
   (`test_executor_parsing.spl`) instead of a bare non-zero exit, so this class
   of false-negative is diagnosable.
3. Optionally split this 250-block / 6370-line spec into smaller files so each
   child stays well under any sampled ceiling (mechanical; preserves all
   assertions).

## Related compile-mode gap (separate, lower priority)

`simple compile <spec>` => `semantic: undefined identifier: NATIVE_PROMISE_THEN`.
The identifier is defined and exported from
`src/lib/nogc_sync_mut/js/engine/runtime.spl`; it resolves in interpreter mode
but not in compile mode. This does not affect the default interpreter test path
but blocks `--mode=native/smf` for this spec. Tracks with the known
"compile-mode false-greens / SSpec compile pipeline" fragility.

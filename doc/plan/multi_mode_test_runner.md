# Multi-Mode Test Runner — Plan

**Status:** Draft
**Date:** 2026-03-14
**Cross-References:**
- Requirement: [`doc/requirement/multi_mode_test_runner.md`](../requirement/multi_mode_test_runner.md)
- Research: [`doc/research/multi_mode_test_runner.md`](../research/multi_mode_test_runner.md)
- Design: [`doc/design/multi_mode_test_runner.md`](../design/multi_mode_test_runner.md)
- System Tests: [`test/system/multi_mode_test_runner_spec.spl`](../../test/system/multi_mode_test_runner_spec.spl)

## Objective

Enable tests to run across all three execution backends (interpreter, loader/SMF, native AOT) through a unified `test_main()` entry point, with CLI flags for mode selection, per-mode result aggregation, and future remote/baremetal execution support. This ensures correctness across all compilation targets and catches backend-specific regressions.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| `TestExecutionMode` enum | Real (4 modes: Interpreter, Smf, Native, Composite) | `src/app/test_runner_new/test_runner_types.spl` |
| `execution_mode_from_string()` | Real (parses "interpreter", "smf", "native", composite specs) | `src/app/test_runner_new/test_runner_types.spl` |
| `run_test_file_interpreter()` | Real (full: binary discovery, coverage, limits, timeout, parsing) | `src/app/test_runner_new/test_runner_execute.spl` |
| `run_test_file_smf()` | Framework exists, falls back to native when coverage enabled | `src/app/test_runner_new/test_runner_execute.spl` |
| `run_test_file_native()` | Framework exists, calls `preprocess_sspec_file()` + AOT compile + run binary | `src/app/test_runner_new/test_runner_execute.spl` |
| `run_test_file_composite()` | Real (dispatches to baremetal/remote by platform layer) | `src/app/test_runner_new/test_executor_composite.spl` |
| `parse_test_output()` | Real (extracts passed/failed/skipped/pending from stdout) | `src/app/test_runner_new/test_executor_parsing.spl` |
| `preprocess_sspec_file()` | Real (wraps SSpec `_spec.spl` in `fn main()` for native compile) | `src/app/test_runner_new/test_runner_execute.spl` |
| `TestOptions.execution_mode` | Real (field exists, parsed from CLI) | `src/app/test_runner_new/test_runner_types.spl` |
| Baremetal `test_harness` | Real (init/start/pass/fail/end via serial, QEMU exit) | `src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl` |
| Semihost (ARM, RISC-V) | Real | `src/lib/nogc_async_mut_noalloc/baremetal/*/semihost.spl` |
| QEMU launch + ELF dispatch | Real | `src/app/test_runner_new/test_executor_composite.spl` |
| SSpec framework | Real (describe/it/expect, skip/ignore decorators) | `src/lib/nogc_sync_mut/spec/mod.spl` |
| `aot_c_file()` | Real | `src/compiler/80.driver/mod.spl` |
| `interpret_file()` | Real | `src/compiler/80.driver/mod.spl` |
| JIT instantiator | Real (load-time generic instantiation) | `src/compiler/99.loader/loader/jit_instantiator.spl` |
| `test_main()` universal entry point | Does NOT exist | -- |
| `--mode` CLI flag | Does NOT exist (execution_mode field exists but no `--mode` flag) | -- |
| `--all-modes` CLI flag | Does NOT exist | -- |
| `init_fn` callback support | Does NOT exist | -- |
| Called-function mode (user main imports test_main) | Does NOT exist | -- |
| Remote test execution | Does NOT exist (TODO stubs in composite executor) | -- |

## What To Do

### Task Group A: Core Infrastructure

#### A1. Create `test_main()` universal entry point (difficulty: 3)

Create `src/app/test_runner_new/test_main.spl` with:

```simple
fn test_main(args: List<text>, init_fn: Option<Fn()>) -> TestRunResult
```

- Discovers test files from `args` (paths, globs, or default `test/`)
- Calls `init_fn` if `Some` -- if it throws/fails, skip all tests with error
- Runs SSpec describe/it blocks via the existing spec framework
- Collects `TestRunResult` with per-file `TestFileResult` entries
- Returns structured result (no `sys_exit()` -- caller decides exit behavior)
- Re-uses existing `parse_test_output()` for stdout-based result extraction

**Files to modify/create:**
- Create: `src/app/test_runner_new/test_main.spl`
- Modify: `src/app/test_runner_new/test_runner_types.spl` (add `TestRunResult` if missing)

**Cross-refs:** Used by B4, B5, C7, C8, C9.

---

#### A2. Update `TestExecutionMode` for multi-mode support (difficulty: 1)

Add helper functions to `test_runner_types.spl`:

- `all_host_modes() -> List<TestExecutionMode>` -- returns `[Interpreter, Smf, Native]`
- `execution_mode_label(mode) -> text` -- human-readable label for reports

**Files to modify:**
- `src/app/test_runner_new/test_runner_types.spl`

**Cross-refs:** Used by A3, D10.

---

#### A3. Add `--mode` and `--all-modes` CLI flags (difficulty: 2)

Extend argument parsing in `test_runner_args.spl`:

- `--mode=interpreter|loader|native` -- select single execution mode (default: interpreter)
- `--all-modes` -- run all three host modes sequentially
- Map `loader` to `TestExecutionMode.Smf` (user-facing name vs internal name)
- Validate: `--all-modes` and `--mode` are mutually exclusive

**Files to modify:**
- `src/app/test_runner_new/test_runner_args.spl`
- `src/app/test_runner_new/test_runner_types.spl` (add `all_modes: bool` field to `TestOptions`)

**Depends on:** A2.

---

### Task Group B: Mode Implementations

#### B4. Implement native mode end-to-end (difficulty: 3)

Complete `run_test_file_native()` in `test_runner_execute.spl`:

1. Call `preprocess_sspec_file()` to wrap SSpec files in `fn main()` (already exists)
2. AOT compile via `aot_c_file()` -- generate C, compile to binary with clang
3. Link with runtime (`src/runtime/runtime.c`) and spec library
4. Execute compiled binary with timeout
5. Parse stdout via `parse_test_output()`
6. Clean up generated artifacts (`.c`, binary) unless `--keep-artifacts`

**Key concern:** The `preprocess_sspec_file()` already handles SSpec wrapping. Verify it correctly includes all imports and top-level definitions outside `fn main()`.

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl` (complete `run_test_file_native`)

**Depends on:** A1. **Cross-refs:** Used by B6.

---

#### B5. Implement loader (SMF) mode end-to-end (difficulty: 3)

Complete `run_test_file_smf()` in `test_runner_execute.spl`:

1. Compile test file to SMF format
2. Load SMF via JIT instantiator (`src/compiler/99.loader/loader/jit_instantiator.spl`)
3. Resolve `test_main` export symbol from loaded SMF
4. Call `test_main()` with args and collect results
5. Fall back to interpreter mode on load failure with diagnostic message

**Key concern:** JIT instantiator currently handles generic template instantiation at load-time. Need to verify it can load and call arbitrary exported functions from SMF modules.

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl` (complete `run_test_file_smf`)

**Depends on:** A1. **Cross-refs:** Used by B6.

---

#### B6. Wire mode dispatch in test execution (difficulty: 2)

Update the main test execution path to dispatch based on `TestOptions.execution_mode`:

```simple
match options.execution_mode:
    Interpreter: run_test_file_interpreter(file, options)
    Smf: run_test_file_smf(file, options)
    Native: run_test_file_native(file, options)
    Composite(spec): run_test_file_composite(file, options, spec)
```

Verify the existing dispatch logic in `test_runner_execute.spl` already does this or wire it up.

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl`

**Depends on:** B4, B5.

---

### Task Group C: Startup Modes

#### C7. Standalone mode -- generated `main()` calls `test_main()` (difficulty: 2)

For native and loader modes, generate a `main()` wrapper that:

1. Calls `test_main(sys_args(), None)` -- no custom init
2. Prints results to stdout in parseable format
3. Exits with code 0 (all pass) or 1 (any fail)

This is partially done by `preprocess_sspec_file()` which wraps SSpec content in `fn main()`. Extend it to call `test_main()` instead of directly running SSpec blocks.

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl` (update `preprocess_sspec_file`)

**Depends on:** A1.

---

#### C8. Called-function mode -- user imports `test_main()` (difficulty: 2)

Support the pattern where a user's own `main()` imports and calls `test_main()`:

```simple
use std.spec.test_main

fn main():
    val init = Some(\: setup_database())
    val result = test_main(sys_args(), init)
    if result.failed > 0:
        sys_exit(1)
```

This requires `test_main()` to be exported from the spec library namespace. No special implementation needed beyond A1 -- just ensure the module is importable via `use std.spec.test_main`.

**Files to modify:**
- `src/lib/nogc_sync_mut/spec/mod.spl` (re-export `test_main`)
- `src/app/test_runner_new/test_main.spl` (ensure public export)

**Depends on:** A1.

---

#### C9. Pre-loaded init support via `init_fn` (difficulty: 2)

Implement the `init_fn: Option<Fn()>` parameter in `test_main()`:

- If `Some(fn)`: call the function before any test execution
- If the init function fails (returns error or throws): skip all tests, report init failure
- Useful for database setup, service startup, fixture loading
- Init timing reported separately in `TestRunResult.setup_ms`

**Files to modify:**
- `src/app/test_runner_new/test_main.spl`

**Depends on:** A1.

---

### Task Group D: All-Modes Runner

#### D10. Implement `--all-modes` sequential execution (difficulty: 2)

When `--all-modes` is specified:

1. Run tests in interpreter mode, collect `TestRunResult`
2. Run tests in loader/SMF mode, collect `TestRunResult`
3. Run tests in native mode, collect `TestRunResult`
4. Aggregate into `MultiModeResult` with per-mode breakdown
5. Report overall pass/fail (all modes must pass)
6. If `--fail-fast`, stop at first mode that has failures

**Files to modify/create:**
- `src/app/test_runner_new/test_runner_execute.spl` (add `run_all_modes()`)
- `src/app/test_runner_new/test_runner_types.spl` (add `MultiModeResult` type)

**Depends on:** A2, A3.

---

#### D11. Per-mode result reporting with labels and timing (difficulty: 1)

Enhance test output to show mode-labeled results:

```
=== Interpreter Mode ===
42 passed, 0 failed (1.2s)

=== Loader Mode ===
42 passed, 0 failed (0.8s)

=== Native Mode ===
42 passed, 0 failed (0.3s)

=== Summary (all modes) ===
126 passed, 0 failed across 3 modes (2.3s total)
```

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl` (formatting in `run_all_modes`)

**Depends on:** D10.

---

### Task Group E: Baremetal Remote (TODO stubs only)

These tasks create design documentation and TODO stubs for future remote execution. No implementation -- design only.

#### E12. Design remote test protocol (difficulty: 2, design only)

Document the protocol for remote test execution:

- **Upload:** How test binary/SMF reaches the target (semihosting file I/O, TFTP, debug probe)
- **Execute:** How tests are triggered (semihosting SYS_OPEN, GDB `run`, JTAG halt+go)
- **Results:** How results return to host (serial port parsing, semihosting stdout, shared memory)
- **Timeout:** How host detects hung target (watchdog timer, serial silence timeout)

**Files to create:**
- `doc/design/remote_test_protocol.md`

---

#### E13. Add TODO stubs for remote interpreter execution (difficulty: 1)

Add TODO markers in composite executor for remote interpreter:

- Remote interpreter requires: target has Simple interpreter binary
- Upload test `.spl` file via semihosting or network
- Execute interpreter on target, capture serial output
- Parse results from serial stream

**Files to modify:**
- `src/app/test_runner_new/test_executor_composite.spl`

**Depends on:** E12.

---

#### E14. Add TODO stubs for remote native execution (difficulty: 1)

Add TODO markers for remote native test execution:

- Cross-compile test to target arch (riscv32, arm32, aarch64)
- Upload ELF via debug probe or semihosting
- Execute on target, parse serial output via `parse_test_output()`
- Existing `run_test_file_baremetal_qemu()` is the local emulation equivalent

**Files to modify:**
- `src/app/test_runner_new/test_executor_composite.spl`

**Depends on:** E12.

---

#### E15. Add TODO stubs for minimal loader on baremetal (difficulty: 1)

Add TODO markers for SMF loading on baremetal targets:

- Minimal loader: semihosting file read + interrupt vector setup only
- No OS, no malloc -- static memory allocation for loaded SMF
- Subset of JIT instantiator for embedded targets
- Requires: linker script, startup assembly, semihosting I/O

**Files to modify:**
- `src/app/test_runner_new/test_executor_composite.spl`

**Depends on:** E12.

---

## Dependencies (DAG)

```
A1 (test_main entry point)
 +---> B4 (native mode)
 +---> B5 (loader/SMF mode)
 |       |
 |       +---> B6 (wire dispatch) <--- B4
 +---> C7 (standalone mode)
 +---> C8 (called-function mode)
 +---> C9 (init_fn support)

A2 (mode helpers) ---> A3 (CLI flags) ---> D10 (all-modes runner) ---> D11 (reporting)

E12 (protocol design)
 +---> E13 (remote interpreter stubs)
 +---> E14 (remote native stubs)
 +---> E15 (baremetal loader stubs)
```

Groups A-C can proceed in parallel once A1 is complete. Group D requires A2+A3. Group E is independent (design/TODO only).

## Suggested Implementation Order

| Phase | Tasks | Effort |
|-------|-------|--------|
| Phase 1 | A1, A2 | Core entry point + mode helpers |
| Phase 2 | A3, C7, C8, C9 | CLI flags + startup modes (parallel) |
| Phase 3 | B4, B5 | Complete native + loader backends (parallel) |
| Phase 4 | B6 | Wire dispatch |
| Phase 5 | D10, D11 | All-modes runner + reporting |
| Phase 6 | E12-E15 | Design doc + TODO stubs |

## Key Files

| File | Role |
|------|------|
| `src/app/test_runner_new/test_runner_types.spl` | Type definitions, `TestExecutionMode` enum |
| `src/app/test_runner_new/test_runner_execute.spl` | Core execution modes (interpreter, SMF, native) |
| `src/app/test_runner_new/test_runner_args.spl` | CLI argument parsing |
| `src/app/test_runner_new/test_executor_composite.spl` | Composite/baremetal/remote execution |
| `src/app/test_runner_new/test_executor_parsing.spl` | Output parsing, binary discovery |
| `src/app/test_runner_new/test_main.spl` | NEW: universal test entry point |
| `src/lib/nogc_sync_mut/spec/mod.spl` | SSpec framework |
| `src/compiler/80.driver/mod.spl` | `aot_c_file()`, `interpret_file()` |
| `src/compiler/99.loader/loader/jit_instantiator.spl` | JIT/SMF loading |
| `src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl` | Baremetal test harness |

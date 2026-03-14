# Multi-Mode Test Runner — Requirements

## Feature Name
Multi-Mode Test Runner with Baremetal Remote Support

## Motivation (Why)
Currently, the test runner executes tests primarily via subprocess (interpreter mode). The other modes (SMF/loader, native, composite/baremetal) exist as framework stubs but lack a unified C++-style test runner pattern where `main()` takes args, runs selected tests, and returns structured results. This prevents:

1. Running tests in-process for faster iteration (no subprocess overhead)
2. Using a compiled test binary as a standalone executable (like Google Test)
3. Running tests on baremetal/remote targets where subprocess spawning is impossible
4. Pre-loaded initialization patterns needed for embedded test targets

## Scope

### In Scope
1. **Unified test runner main** — A base `test_main()` function that works across interpreter, loader (SMF), and native modes, accepting args and returning structured results
2. **Mode selection** — CLI options to select execution mode (`--mode=interpreter|loader|native`) and batch mode (`--all-modes`)
3. **Baremetal remote test run** (TODO/design only for remote, full impl for local):
   - Interpreter remote test runner
   - Native load-and-run on remote target
   - Loader as minimal test infrastructure (semihost + interrupt handler only)
4. **Pre-loaded initialization** — Support for test target init function calls before test execution
5. **Dual startup modes** — Main as entry point vs called-function mode (test runner invoked from user code)

### Out of Scope
- TRACE32 hardware debugger integration (existing separate feature)
- Test parallelization (existing TODO, separate concern)
- Coverage report generation (separate feature)
- New SSpec matchers or framework changes

## I/O Examples

### Example 1: Run tests in native mode
```bash
bin/simple test test/unit/math_spec.spl --mode=native
# Compiles test to native binary, executes, parses results
# Output: "3 passed, 0 failed, 0 skipped (native mode, 45ms)"
```

### Example 2: Run tests in loader (SMF) mode
```bash
bin/simple test test/unit/math_spec.spl --mode=loader
# Loads pre-compiled SMF module, executes test_main()
# Output: "3 passed, 0 failed, 0 skipped (loader mode, 12ms)"
```

### Example 3: Run all modes
```bash
bin/simple test test/unit/math_spec.spl --all-modes
# Runs in interpreter, loader, and native sequentially
# Output:
#   interpreter: 3 passed, 0 failed (220ms)
#   loader:      3 passed, 0 failed (12ms)
#   native:      3 passed, 0 failed (45ms)
```

### Example 4: Baremetal test (QEMU, local)
```bash
bin/simple test test/baremetal/gpio_spec.spl --mode=composite:native(baremetal(riscv32))
# Cross-compiles to RISC-V, runs in QEMU with semihost
# Output: "2 passed, 0 failed (qemu-riscv32, 1200ms)"
```

### Example 5: Called-function mode (from user code)
```simple
use std.spec.test_runner

fn my_init():
    hardware_setup()

fn main():
    test_runner_main(init_fn: my_init, args: sys_args())
```

## Acceptance Criteria

### AC-1: Unified test_main() function
- A `test_main(args: List<text>) -> TestRunResult` function exists that can be called from any execution context
- Works in interpreter, loader, and native modes
- Returns structured `TestRunResult` with pass/fail/skip counts

### AC-2: Mode selection via CLI
- `--mode=interpreter` runs tests via interpreter (current default)
- `--mode=loader` compiles to SMF and loads/runs via module loader
- `--mode=native` compiles to native binary and executes
- `--all-modes` runs in all three modes sequentially
- Default mode remains `interpreter` for backward compatibility

### AC-3: Native mode test execution
- Test file is AOT-compiled to a native binary
- Binary contains `main()` that calls `test_main()` with CLI args
- Binary is self-contained (links runtime, spec framework)
- Results are printed to stdout in parseable format
- Test runner parses output and reports results

### AC-4: Loader (SMF) mode test execution
- Test file is compiled to SMF format
- SMF module is loaded via JIT instantiator
- `test_main()` is called within the loaded module
- Results are returned via structured output (stdout or return value)

### AC-5: Pre-loaded initialization support
- `test_main()` accepts optional `init_fn` callback
- Init function is called before any test execution
- Init function can set up hardware, allocate resources, etc.
- If init function fails, all tests are marked as "skipped" with init error

### AC-6: Dual startup modes
- **Standalone mode**: Test binary's `main()` calls `test_main(sys_args())`
- **Called-function mode**: User code calls `test_main()` with custom args and init
- Both modes produce identical test results

### AC-7: Baremetal local test (QEMU)
- Tests can be cross-compiled for baremetal targets (riscv32, arm, arm64, riscv64, x86)
- QEMU launches with semihost enabled
- Test harness outputs results via semihost serial
- Host test runner parses QEMU output for results

### AC-8: Baremetal remote test run (TODO markers)
- TODO markers placed for:
  - Remote interpreter execution (send .spl to remote, interpret there)
  - Remote native execution (send .elf to remote, execute via debug probe)
  - Minimal loader infrastructure (semihost + interrupt handler only)
- Design document captures remote protocol and target initialization flow

## Dependencies
- `src/app/test_runner_new/` — existing test runner (to be extended)
- `src/lib/nogc_sync_mut/spec/` — SSpec framework
- `src/compiler/80.driver/` — compiler pipeline (interpret, AOT, SMF)
- `src/compiler/99.loader/` — module loader/JIT
- `src/lib/nogc_async_mut_noalloc/baremetal/` — semihost and test harness
- `src/compiler/70.backend/` — backends (C, LLVM, etc.)

## Cross-References
- Research: [`doc/research/multi_mode_test_runner.md`](../research/multi_mode_test_runner.md)
- Plan: [`doc/plan/multi_mode_test_runner.md`](../plan/multi_mode_test_runner.md)
- Design: [`doc/design/multi_mode_test_runner.md`](../design/multi_mode_test_runner.md)
- System Tests: [`test/system/multi_mode_test_runner_spec.spl`](../../test/system/multi_mode_test_runner_spec.spl)

# Multi-Mode Test Runner Design

**Status:** Draft
**Date:** 2026-03-14
**Feature:** Multi-Mode Test Runner
**Cross-References:**
- Requirement: [`doc/requirement/multi_mode_test_runner.md`](../requirement/multi_mode_test_runner.md)
- Research: [`doc/research/multi_mode_test_runner.md`](../research/multi_mode_test_runner.md)
- Plan: [`doc/plan/multi_mode_test_runner.md`](../plan/multi_mode_test_runner.md)
- Embedded Design: [`doc/design/embedded_test_runner_design.md`](embedded_test_runner_design.md)
- System Tests: [`test/system/multi_mode_test_runner_spec.spl`](../../test/system/multi_mode_test_runner_spec.spl)

---

## Table of Contents

1. [Overview](#1-overview)
2. [Current Architecture](#2-current-architecture)
3. [Module Structure](#3-module-structure)
4. [Type Definitions](#4-type-definitions)
5. [API Surface](#5-api-surface)
6. [Execution Flows](#6-execution-flows)
7. [Pre-Loaded Initialization Design](#7-pre-loaded-initialization-design)
8. [Integration Points](#8-integration-points)
9. [CLI Interface](#9-cli-interface)
10. [Error Handling](#10-error-handling)
11. [Migration Plan](#11-migration-plan)

---

## 1. Overview

A unified test runner that supports **interpreter**, **loader (SMF)**, and **native** execution modes with pre-loaded initialization and baremetal remote support. The design introduces a universal `test_main()` entry point callable from any execution context, enabling tests to run identically whether interpreted, JIT-loaded, or AOT-compiled.

### Goals

- **Unified entry point**: A single `test_main()` function that works across all modes
- **Mode selection**: CLI flags to pick execution mode or run all modes
- **Called-function mode**: Test runner invoked from user code (not just as standalone binary)
- **Pre-loaded init**: Support for hardware/system init before test execution
- **Baremetal remote**: Design stubs for remote target execution (local QEMU already works)

### Non-Goals

- TRACE32 hardware debugger integration (separate feature)
- Test parallelization changes (existing separate concern)
- Coverage report generation (separate feature)
- New SSpec matchers or framework changes

---

## 2. Current Architecture

### 2.1 Existing Execution Modes

The current `TestExecutionMode` enum (`src/app/test_runner_new/test_runner_types.spl`) supports:

```simple
enum TestExecutionMode:
    Interpreter
    Smf
    Native
    Composite(spec: text)
```

### 2.2 Current Execution Pattern

All modes execute tests as **subprocesses** and parse stdout for results:

```
test_spec.spl
  -> find_simple_binary()
  -> process_run_timeout(binary, [file_path, ...], timeout_ms)
  -> parse stdout for "N passed, M failed"
  -> return TestFileResult
```

Key files:
- `src/app/test_runner_new/test_runner_execute.spl` — core modes (interpreter, SMF, native, safe)
- `src/app/test_runner_new/test_executor_parsing.spl` — output parsing, binary discovery
- `src/app/test_runner_new/test_executor_composite.spl` — baremetal/remote/QEMU
- `src/app/test_runner_new/test_runner_args.spl` — CLI argument parsing
- `src/app/test_runner_new/test_runner_types.spl` — type definitions
- `src/app/test_runner_new/test_runner_main.spl` — orchestration

### 2.3 Gaps Identified (from Research)

1. No `test_main()` callable function -- all execution is subprocess-based
2. No `--all-modes` flag to run all three modes sequentially
3. Native mode compiles to SMF then runs SMF (not true AOT to native binary)
4. No init function hook for pre-test setup
5. No remote target execution (only local QEMU)
6. Test output is always stdout-based (no structured result channel)

---

## 3. Module Structure

### 3.1 New Files

| File | Role |
|------|------|
| `src/app/test_runner_new/test_main.spl` | Universal test entry point (`test_main`, `test_main_with_init`) |
| `src/app/test_runner_new/test_native_runner.spl` | True native mode: AOT compile to binary, execute |
| `src/app/test_runner_new/test_loader_runner.spl` | Loader/SMF mode: compile to SMF, JIT load, call export |
| `src/app/test_runner_new/test_remote.spl` | Remote execution (TODO stubs only) |

### 3.2 Modified Files

| File | Changes |
|------|---------|
| `src/app/test_runner_new/test_runner_types.spl` | Add `AllModes` variant, `TestModeResult`, `TestAllModesResult`, `TestInitConfig` |
| `src/app/test_runner_new/test_runner_args.spl` | Add `--all-modes`, `--init-module=<path>` flags |
| `src/app/test_runner_new/test_runner_execute.spl` | Wire mode dispatch to new runners |
| `src/app/test_runner_new/main.spl` | Re-export new modules |

### 3.3 Module Dependency Graph

```
main.spl (re-exports)
  |
  +-- test_main.spl (universal entry point)
  |     |
  |     +-- test_runner_args.spl (parse CLI args)
  |     +-- test_runner_types.spl (types)
  |     +-- test_runner_execute.spl (dispatcher)
  |
  +-- test_runner_execute.spl (dispatcher)
  |     |
  |     +-- run_test_file_interpreter()   [existing]
  |     +-- run_test_file_smf()           [existing, enhanced]
  |     +-- test_native_runner.spl        [NEW]
  |     +-- test_loader_runner.spl        [NEW]
  |     +-- test_executor_composite.spl   [existing, baremetal/QEMU]
  |     +-- test_remote.spl              [NEW, TODO stubs]
  |
  +-- test_runner_main.spl (orchestration, DB, parallel, docs)
```

---

## 4. Type Definitions

### 4.1 Extended TestExecutionMode

Add `AllModes` variant to `src/app/test_runner_new/test_runner_types.spl`:

```simple
# Extended TestExecutionMode
enum TestExecutionMode:
    Interpreter         # Run via interpreter subprocess
    Smf                 # Compile to SMF, run pre-compiled bytecode
    Native              # AOT compile to native binary, execute
    Composite(spec: text)   # Baremetal target spec (e.g., "interpreter(baremetal(riscv32))")
    AllModes            # Run interpreter + loader + native sequentially
```

### 4.2 Per-Mode Result

```simple
# Per-mode result for --all-modes runs
struct TestModeResult:
    mode: TestExecutionMode
    result: TestRunResult
    duration_ms: i64

impl TestModeResult:
    fn is_ok() -> bool:
        self.result.is_ok()
```

### 4.3 All-Modes Aggregate Result

```simple
# Aggregate result when running all three modes
struct TestAllModesResult:
    mode_results: [TestModeResult]
    all_passed: bool

impl TestAllModesResult:
    fn summary() -> text:
        var lines: [text] = []
        for mr in self.mode_results:
            val mode_name = match mr.mode:
                Interpreter: "interpreter"
                Smf: "loader"
                Native: "native"
                Composite(s): "composite({s})"
                AllModes: "all"
            val status = if mr.is_ok(): "PASS" else: "FAIL"
            val p = mr.result.total_passed
            val f = mr.result.total_failed
            lines.push("  {mode_name}: {p} passed, {f} failed ({mr.duration_ms}ms) [{status}]")
        lines.join("\n")
```

### 4.4 Init Configuration

```simple
# Configuration for pre-loaded initialization
struct TestInitConfig:
    init_fn: Option<Fn()>       # Direct function reference (called-function mode)
    init_module: Option<text>   # Path to module with init() function (CLI mode)
    timeout_ms: i64             # Init timeout (default 30000)

impl TestInitConfig:
    static fn default() -> TestInitConfig:
        TestInitConfig(init_fn: nil, init_module: nil, timeout_ms: 30000)

    static fn with_fn(f: Fn()) -> TestInitConfig:
        TestInitConfig(init_fn: some(f), init_module: nil, timeout_ms: 30000)

    static fn with_module(path: text) -> TestInitConfig:
        TestInitConfig(init_fn: nil, init_module: some(path), timeout_ms: 30000)
```

### 4.5 Remote Target (TODO)

```simple
# Remote target specification (TODO — design only)
struct RemoteTarget:
    host: text              # IP or hostname
    port: i64               # Connection port
    arch: text              # Target architecture (riscv32, arm32, aarch64, etc.)
    transport: text         # "serial", "tcp", "ssh"
    timeout_ms: i64         # Connection + execution timeout

# Remote protocol message types (TODO — design only)
enum RemoteMessage:
    Upload(data: [u8], path: text)
    Execute(path: text, args: [text])
    Output(stdout: text, stderr: text, exit_code: i64)
    Heartbeat
    Shutdown
```

---

## 5. API Surface

### 5.1 Universal Entry Point (`test_main.spl`)

```simple
use std.spec
use test_runner_types.*
use test_runner_args.parse_test_args
use test_runner_execute.{run_test_file_interpreter, run_test_file_smf}
use test_native_runner.run_test_native
use test_loader_runner.run_test_loader

# =========================================================================
# Universal test entry point callable from any context
# =========================================================================

fn test_main(args: [text]) -> TestRunResult:
    test_main_with_init(args, TestInitConfig.default())

fn test_main_with_init(args: [text], init_config: TestInitConfig) -> TestRunResult:
    # 1. Parse args (--filter, --tag, --mode, etc.)
    val options = parse_test_args(args)

    # 2. Call init_fn if provided
    if init_config.init_fn.?:
        val f = init_config.init_fn.unwrap()
        f()

    # 3. Load init module if specified
    if init_config.init_module.?:
        val module_path = init_config.init_module.unwrap()
        load_and_call_init(module_path)

    # 4. Dispatch based on mode
    match options.mode:
        AllModes:
            val all_result = run_test_all_modes(options)
            merge_all_modes_result(all_result)
        _:
            run_tests_single_mode(options)

fn run_tests_single_mode(options: TestOptions) -> TestRunResult:
    # Discover test files
    val files = discover_test_files(options)

    # Execute each file in the selected mode
    var results: [TestFileResult] = []
    for file_path in files:
        val result = run_test_file_dispatch(file_path, options)
        results.push(result)
        if options.fail_fast and not result.is_ok():
            break

    # Aggregate results
    aggregate_results(results)

fn run_test_file_dispatch(file_path: text, options: TestOptions) -> TestFileResult:
    match options.mode:
        Interpreter: run_test_file_interpreter(file_path, options)
        Smf: run_test_file_smf(file_path, options)
        Native: run_test_native(file_path, options)
        Composite(spec): run_test_file_composite(file_path, options, spec)
        AllModes: run_test_file_interpreter(file_path, options)  # fallback

fn load_and_call_init(module_path: text):
    # Load the module and call its init() function
    # This uses the interpreter to load and execute the module
    pass_todo
```

### 5.2 Native Runner (`test_native_runner.spl`)

```simple
use test_runner_types.*
use app.io.file_ops.{file_exists, file_write, file_delete}
use app.io.time_ops.{time_now_unix_micros}
use app.io.process_ops.{process_run_timeout}
use test_executor_parsing.{find_simple_binary, make_result_from_output}

# =========================================================================
# Native mode: AOT compile test file to binary, execute
# =========================================================================

fn run_test_native(file_path: text, options: TestOptions) -> TestFileResult:
    val start = time_now_unix_micros()
    val timeout_ms = options.timeout * 1000
    val binary = find_simple_binary()

    # Step 1: Preprocess SSpec file (wrap describe/it in main)
    val wrapped_path = preprocess_for_native(file_path)

    # Step 2: AOT compile to C, then to native binary
    val out_binary = file_path.replace(".spl", ".test_bin")
    val compile_result = aot_compile_test(binary, wrapped_path, out_binary, timeout_ms, options.verbose)

    if not compile_result.success:
        cleanup_native_artifacts(wrapped_path, out_binary, file_path, options)
        val end = time_now_unix_micros()
        val duration_ms = (end - start) / 1000
        return TestFileResult(
            path: file_path, passed: 0, failed: 1, skipped: 0, pending: 0,
            duration_ms: duration_ms, setup_ms: 0,
            error: "Native compilation failed: {compile_result.error}",
            timed_out: false
        )

    # Step 3: Execute the compiled binary
    val (stdout, stderr, exit_code) = process_run_timeout(out_binary, [], timeout_ms)
    val end = time_now_unix_micros()
    val duration_ms = (end - start) / 1000

    # Step 4: Clean up artifacts
    cleanup_native_artifacts(wrapped_path, out_binary, file_path, options)

    # Step 5: Parse output
    make_result_from_output(file_path, stdout, stderr, exit_code, duration_ms, options.timeout)


fn preprocess_for_native(file_path: text) -> text:
    """Generate a wrapper that calls test_main() from a main() entry point.

    For SSpec files (*_spec.spl), wraps the describe/it blocks in fn main()
    so the AOT compiler can produce a valid native binary.
    """
    if not file_path.ends_with("_spec.spl"):
        return file_path

    # Reuse existing preprocess_sspec_file from test_runner_execute
    preprocess_sspec_file(file_path)


struct CompileResult:
    success: bool
    error: text

fn aot_compile_test(binary: text, source: text, out_binary: text, timeout_ms: i64, verbose: bool) -> CompileResult:
    """AOT compile a test file to a native binary.

    Flow:
      source.spl -> aot_c_file() -> source.c -> clang -> source.test_bin

    The generated main() wrapper calls test_main(args) and exits with
    the appropriate code based on test results.
    """
    # Step 1: Compile .spl to .c via AOT C backend
    val c_file = source.replace(".spl", ".c")
    var compile_args: [text] = ["compile", source, "--backend=c", "-o", c_file]
    if verbose:
        compile_args.push("--verbose")
        print "[native] AOT compiling {source} -> {c_file}"

    val (stdout, stderr, exit_code) = process_run_timeout(binary, compile_args, timeout_ms)
    if exit_code != 0:
        return CompileResult(success: false, error: stderr)

    # Step 2: Compile .c to native binary via clang
    val link_args = ["-o", out_binary, c_file, "-lm"]
    if verbose:
        print "[native] Linking {c_file} -> {out_binary}"
    val (link_stdout, link_stderr, link_exit) = process_run_timeout("clang", link_args, timeout_ms)
    if link_exit != 0:
        return CompileResult(success: false, error: link_stderr)

    CompileResult(success: true, error: "")


fn cleanup_native_artifacts(wrapped_path: text, out_binary: text, original_path: text, options: TestOptions):
    if options.keep_artifacts:
        return
    val c_file = wrapped_path.replace(".spl", ".c")
    if wrapped_path != original_path and file_exists(wrapped_path):
        file_delete(wrapped_path)
    if file_exists(c_file):
        file_delete(c_file)
    if file_exists(out_binary):
        file_delete(out_binary)
```

### 5.3 Loader Runner (`test_loader_runner.spl`)

```simple
use test_runner_types.*
use app.io.file_ops.{file_exists, file_delete}
use app.io.time_ops.{time_now_unix_micros}
use app.io.process_ops.{process_run_timeout}
use test_executor_parsing.{find_simple_binary, make_result_from_output}

# =========================================================================
# Loader (SMF) mode: compile to SMF, JIT load, call test_main export
# =========================================================================

fn run_test_loader(file_path: text, options: TestOptions) -> TestFileResult:
    val start = time_now_unix_micros()
    val timeout_ms = options.timeout * 1000
    val binary = find_simple_binary()
    val smf_path = file_path.replace(".spl", ".smf")

    # Step 1: Check for pre-compiled .smf or compile fresh
    if not file_exists(smf_path) or options.force_rebuild:
        val compile_result = compile_to_smf(binary, file_path, smf_path, timeout_ms, options.verbose)
        if not compile_result.success:
            val end = time_now_unix_micros()
            val duration_ms = (end - start) / 1000
            return TestFileResult(
                path: file_path, passed: 0, failed: 1, skipped: 0, pending: 0,
                duration_ms: duration_ms, setup_ms: 0,
                error: "SMF compilation failed: {compile_result.error}",
                timed_out: false
            )

    # Step 2: Load .smf via JIT instantiator and call test_main export
    #
    # Current approach: run the .smf file via the simple binary, which
    # internally uses the JIT instantiator to load and execute it.
    #
    # Future enhancement: directly call test_main() export from JIT
    # instantiator without subprocess, returning TestRunResult in-process.
    var run_args: [text] = [smf_path]
    if options.gc_log:
        run_args.push("--gc-log")
    if options.gc_off:
        run_args.push("--gc=off")

    val (stdout, stderr, exit_code) = process_run_timeout(binary, run_args, timeout_ms)
    val end = time_now_unix_micros()
    val duration_ms = (end - start) / 1000

    # Step 3: Clean up .smf artifact
    if not options.keep_artifacts and file_exists(smf_path):
        file_delete(smf_path)

    make_result_from_output(file_path, stdout, stderr, exit_code, duration_ms, options.timeout)


struct SmfCompileResult:
    success: bool
    error: text

fn compile_to_smf(binary: text, source: text, smf_path: text, timeout_ms: i64, verbose: bool) -> SmfCompileResult:
    """Compile .spl source to .smf bytecode format.

    Uses the compiler's compile_to_smf pipeline:
      source.spl -> parse -> type check -> monomorphize -> MIR -> SMF serialize
    """
    var compile_args: [text] = ["compile", source, "-o", smf_path, "--format=smf"]
    if verbose:
        compile_args.push("--verbose")
        print "[loader] Compiling {source} -> {smf_path}"

    val (stdout, stderr, exit_code) = process_run_timeout(binary, compile_args, timeout_ms)
    if exit_code != 0:
        return SmfCompileResult(success: false, error: stderr)
    SmfCompileResult(success: true, error: "")
```

### 5.4 All-Modes Runner

```simple
# In test_main.spl or test_runner_execute.spl

fn run_test_all_modes(options: TestOptions) -> TestAllModesResult:
    """Run tests in all three modes: interpreter, loader, native."""
    val modes: [TestExecutionMode] = [
        TestExecutionMode.Interpreter,
        TestExecutionMode.Smf,
        TestExecutionMode.Native
    ]

    var mode_results: [TestModeResult] = []
    var all_passed = true

    for mode in modes:
        # Create options copy with specific mode
        var mode_options = options
        mode_options.mode = mode

        val start = time_now_unix_micros()
        val result = run_tests_single_mode(mode_options)
        val end = time_now_unix_micros()
        val duration_ms = (end - start) / 1000

        val mr = TestModeResult(mode: mode, result: result, duration_ms: duration_ms)
        mode_results.push(mr)
        if not result.is_ok():
            all_passed = false
            if options.fail_fast:
                break

    TestAllModesResult(mode_results: mode_results, all_passed: all_passed)


fn merge_all_modes_result(all_result: TestAllModesResult) -> TestRunResult:
    """Merge per-mode results into a single TestRunResult for reporting."""
    var total_passed = 0
    var total_failed = 0
    var total_skipped = 0
    var total_pending = 0
    var total_timed_out = 0
    var total_duration_ms: i64 = 0
    var all_files: [TestFileResult] = []

    for mr in all_result.mode_results:
        total_passed = total_passed + mr.result.total_passed
        total_failed = total_failed + mr.result.total_failed
        total_skipped = total_skipped + mr.result.total_skipped
        total_pending = total_pending + mr.result.total_pending
        total_timed_out = total_timed_out + mr.result.total_timed_out
        total_duration_ms = total_duration_ms + mr.result.total_duration_ms
        for f in mr.result.files:
            all_files.push(f)

    TestRunResult(
        files: all_files,
        total_passed: total_passed,
        total_failed: total_failed,
        total_skipped: total_skipped,
        total_pending: total_pending,
        total_timed_out: total_timed_out,
        total_duration_ms: total_duration_ms,
        total_setup_ms: 0
    )
```

### 5.5 Remote Execution Stubs (`test_remote.spl`)

```simple
use test_runner_types.*

# =========================================================================
# Remote test execution — TODO stubs
#
# Three remote execution strategies are planned:
#
# Option A: Remote Interpreter
#   Upload .spl source to remote target, run via remote interpreter,
#   collect output via semihost/serial.
#
# Option B: Remote Native
#   Cross-compile .spl to target ELF on host, upload ELF to remote,
#   execute on target, collect semihost output via serial.
#
# Option C: Remote Loader (minimal infrastructure)
#   Pre-flash minimal loader (semihost + interrupt handler only) on target,
#   upload .smf to remote, loader loads + runs test_main,
#   collect semihost output via serial.
#
# All remote options need:
#   - Target init function call support (before test execution)
#   - Simple main as startup OR called-function mode
#   - Serial/TCP transport for result collection
# =========================================================================

fn run_test_remote_interpreter(file_path: text, target: RemoteTarget, options: TestOptions) -> TestFileResult:
    """Remote interpreter execution: upload .spl, run on remote target.

    Flow:
      1. Connect to remote target via transport (serial/TCP/SSH)
      2. Upload .spl source file
      3. Signal remote interpreter to execute
      4. Collect semihost/serial output
      5. Parse output for test results
    """
    pass_todo

fn run_test_remote_native(file_path: text, target: RemoteTarget, options: TestOptions) -> TestFileResult:
    """Remote native execution: cross-compile on host, upload ELF, run on target.

    Flow:
      1. Cross-compile .spl to target ELF (using --target=<arch> flag)
      2. Connect to remote target
      3. Upload ELF binary
      4. Signal remote to load + execute ELF
      5. Collect semihost output via serial
      6. Parse output for test results
    """
    pass_todo

fn run_test_remote_loader(file_path: text, target: RemoteTarget, options: TestOptions) -> TestFileResult:
    """Remote loader execution: upload .smf, minimal loader on target runs it.

    Requires pre-flashed minimal loader on target that provides:
      - Semihost I/O (for output collection)
      - Interrupt handler (for fault isolation)
      - SMF loader (for .smf file loading)
      - test_main() call convention

    Flow:
      1. Compile .spl to .smf on host
      2. Connect to remote target
      3. Upload .smf to target memory
      4. Signal loader to load + call test_main()
      5. Collect semihost output via serial
      6. Parse output for test results
    """
    pass_todo
```

---

## 6. Execution Flows

### 6.1 Interpreter Mode Flow (Existing)

```
test_spec.spl
  -> find_simple_binary()
  -> process_run_timeout(binary, [test_spec.spl, --gc-log, ...], timeout_ms)
  -> SSpec framework runs describe/it blocks in interpreter
  -> stdout: "3 passed, 0 failed, 45ms"
  -> parse_test_output(stdout) -> (passed, failed, skipped, pending)
  -> TestFileResult
```

This is the current default mode. No compilation step; the interpreter loads and executes the `.spl` file directly.

### 6.2 Native Mode Flow (New, True AOT)

```
test_spec.spl
  -> preprocess_for_native()
     -> If *_spec.spl: wrap describe/it blocks in fn main()
     -> Generate test_spec_wrapped.spl
  -> aot_compile_test()
     -> bin/simple compile test_spec_wrapped.spl --backend=c -o test_spec.c
        -> parse + type check + monomorphize
        -> MIR lowering
        -> C backend (aot_c_file)
     -> Generate main() wrapper:
          fn main(argc, argv):
              args = convert_args(argc, argv)
              result = test_main(args)
              print_results(result)
              exit(result.total_failed > 0 ? 1 : 0)
     -> clang -o test_spec.test_bin test_spec.c -lm
  -> process_run_timeout("./test_spec.test_bin", [], timeout_ms)
  -> parse stdout for results
  -> cleanup: delete .c, .test_bin, _wrapped.spl
  -> TestFileResult
```

This mode validates that tests pass when compiled to native code, catching issues with:
- Type system edge cases that only manifest in compiled code
- Memory layout differences between interpreter and native
- FFI boundary behavior

### 6.3 Loader (SMF) Mode Flow (Enhanced)

```
test_spec.spl
  -> compile_to_smf()
     -> bin/simple compile test_spec.spl -o test_spec.smf --format=smf
        -> parse + type check + monomorphize
        -> MIR lowering
        -> SMF serialization (smf_writer.spl)
  -> Current: process_run_timeout(binary, [test_spec.smf], timeout_ms)
     -> JIT instantiator loads .smf
     -> Interpreter executes loaded module
     -> stdout output
  -> Future: JIT instantiator loads .smf in-process
     -> lookup "test_main" export symbol
     -> call test_main(args) -> TestRunResult directly
     -> No stdout parsing needed (structured result)
  -> cleanup: delete .smf
  -> TestFileResult
```

### 6.4 All-Modes Flow

```
bin/simple test test/unit/math_spec.spl --all-modes

  -> parse_test_args() -> mode = AllModes
  -> run_test_all_modes(options)
     -> For mode in [Interpreter, Smf, Native]:
        -> clone options with mode = current_mode
        -> run_tests_single_mode(mode_options) -> TestRunResult
        -> wrap in TestModeResult with timing
     -> TestAllModesResult
  -> merge_all_modes_result() -> TestRunResult

Output:
  interpreter: 3 passed, 0 failed (220ms) [PASS]
  loader:      3 passed, 0 failed (12ms)  [PASS]
  native:      3 passed, 0 failed (45ms)  [PASS]
```

### 6.5 Baremetal Local Flow (Existing, via QEMU)

```
test_spec.spl --mode="interpreter(baremetal(riscv32))"

  -> parse_mode_str() -> Composite("interpreter(baremetal(riscv32))")
  -> run_test_file_composite()
     -> extract_base_runtime() = "interpreter"
     -> extract_platform_layer() = "baremetal"
     -> extract_arch_from_spec() = "riscv32"
     -> find_baremetal_elf(spec_file, "riscv32")
     -> qemu_binary_for_arch("riscv32") = "qemu-system-riscv32"
     -> process_run_timeout("qemu-system-riscv32",
          ["-M", "virt", "-bios", "none", "-kernel", elf,
           "-nographic", "-semihosting-config", "enable=on,..."],
          timeout_ms)
     -> parse semihost output: "[PASS] test_name" / "[FAIL] ..."
  -> TestFileResult
```

### 6.6 Baremetal Remote Flow (TODO Design)

```
Option A: Remote Interpreter
  test_spec.spl
    -> connect to remote target (serial/TCP/SSH)
    -> upload .spl source
    -> remote interpreter loads + runs
    -> semihost output -> serial -> host parses
    -> TestFileResult

Option B: Remote Native
  test_spec.spl
    -> cross-compile to target ELF (--target=riscv32)
    -> connect to remote target
    -> upload ELF binary
    -> remote loads + executes ELF
    -> semihost output -> serial -> host parses
    -> TestFileResult

Option C: Remote Loader (minimal infrastructure)
  Pre-flash on target: minimal loader (semihost + interrupt + SMF loader)
  test_spec.spl
    -> compile to .smf on host
    -> connect to remote target
    -> upload .smf to target memory
    -> signal loader: load + call test_main()
    -> semihost output -> serial -> host parses
    -> TestFileResult
```

---

## 7. Pre-Loaded Initialization Design

### 7.1 Standalone Mode (Test Binary is Entry Point)

```simple
# Default: test runner is the main entry point
fn main():
    val args = get_cli_args()
    val result = test_main(args)
    if not result.is_ok():
        exit(1)
```

This is the normal `bin/simple test` flow. No init function is needed.

### 7.2 Called-Function Mode (User Code is Entry Point)

```simple
# User code: test runner is called from user's main()
fn main():
    # User-specific hardware/system initialization
    my_hardware_init()
    configure_memory_pool(size: 1024 * 1024)
    open_debug_connection()

    # Run tests with init hook
    val args = get_cli_args()
    val init = TestInitConfig.with_fn(my_test_setup)
    val result = test_main_with_init(args, init)

    # User-specific cleanup
    close_debug_connection()
    if not result.is_ok():
        exit(1)
```

### 7.3 Init Module Mode (CLI-Based)

```simple
# CLI usage:
#   bin/simple test --init-module=my_init.spl test/unit/spec.spl
#
# my_init.spl must export an init() function:
#   fn init():
#       configure_hardware()
#       setup_memory()

fn load_and_call_init(module_path: text):
    """Load a module and call its init() function.

    The module is loaded via the interpreter and its init() export
    is called before any test execution begins.

    If init() throws or panics:
      - All tests are marked "skipped" with init error message
      - TestRunResult.total_skipped = total test count
      - TestRunResult error field contains init failure details
    """
    pass_todo
```

### 7.4 Init Function Contract

The init function (whether provided directly or loaded from a module) must satisfy:

1. **Called once** before any test execution
2. **No arguments** — configuration is done via globals or env vars
3. **No return value** — success is implicit (no exception/panic = success)
4. **Failure semantics** — if init throws/panics, all tests are marked "skipped" with an init error message
5. **Access** — has full access to the runtime environment (can allocate, open files, configure hardware)
6. **Timeout** — subject to `TestInitConfig.timeout_ms` (default 30 seconds)

### 7.5 Baremetal Init Example

```simple
# baremetal_init.spl — example for riscv32 target
use std.baremetal.riscv.startup.{riscv_init}
use std.baremetal.common.test_harness.{test_harness_init}

fn init():
    # Hardware initialization
    riscv_init()

    # Set up semihosting for test output
    test_harness_init()

    # Configure memory allocator with available RAM
    # (on baremetal, no OS memory manager)
    configure_static_allocator(base: 0x8000_0000, size: 64 * 1024)
```

---

## 8. Integration Points

### 8.1 SSpec Framework

**Module:** `src/lib/nogc_sync_mut/spec/`

The SSpec framework provides the `describe`/`it`/`expect` DSL used by all test files. The test runner discovers and executes test files; SSpec provides the in-file test structure.

Key interaction:
- SSpec writes results to stdout in a parseable format: `"N passed, M failed"`
- Test runner's `parse_test_output()` extracts pass/fail/skip/pending counts
- Future enhancement: SSpec returns `TestRunResult` directly (no stdout parsing)

### 8.2 Compiler Driver

**Module:** `src/compiler/80.driver/driver_api.spl`

Available functions used by the test runner:
- `interpret_file(path)` — run `.spl` via interpreter
- `aot_c_file(path, output)` — compile `.spl` to `.c` via C backend
- `compile_to_smf(path, output)` — compile `.spl` to `.smf` bytecode
- `aot_file(path, output)` — general AOT compilation
- `check_file(path)` — type-check without execution

The native runner uses `aot_c_file()` (via subprocess currently). Future versions may call these directly in-process.

### 8.3 Module Loader / JIT Instantiator

**Module:** `src/compiler/99.loader/jit_instantiator.spl`

The JIT instantiator loads `.smf` files and resolves export symbols:
- `JitInstantiator.load_smf_metadata(path)` — load SMF module metadata
- `JitSymbolResolver.resolve(symbol)` — look up named export
- `JitSymbolResolver.load_smf(path)` — load SMF for symbol resolution

Future loader mode will use `JitSymbolResolver` to find `test_main` and call it directly.

### 8.4 Baremetal Infrastructure

**Module:** `src/lib/nogc_async_mut_noalloc/baremetal/`

Key submodules:
- `common/test_harness.spl` — SSpec-compatible test framework for bare-metal (serial output)
- `arm/semihost.spl`, `riscv/semihost.spl` — semihosting I/O
- `qemu_runner.spl` — QEMU launch + output parsing
- Architecture-specific: `arm/`, `arm64/`, `riscv/`, `riscv32/`

Test harness output format: `[PASS] name` / `[FAIL] name: message` / `[TEST END] passed=N failed=M`

### 8.5 CLI Entry Point

**Module:** `src/app/cli/test_entry.spl`

Lightweight entry point for `bin/simple test` that avoids loading the full CLI. The multi-mode test runner integrates via:
- `test_entry.spl` calls `cli_run_tests()` which eventually calls `run_test_file_*` functions
- `--mode` and `--all-modes` flags are parsed in `test_runner_args.spl`
- New runners are dispatched from `test_runner_execute.spl`

---

## 9. CLI Interface

### 9.1 New CLI Flags

| Flag | Description | Default |
|------|-------------|---------|
| `--mode=interpreter` | Run tests via interpreter | Yes (default) |
| `--mode=loader` | Compile to SMF, load via JIT | |
| `--mode=native` | AOT compile to native binary | |
| `--all-modes` | Run in all three modes | |
| `--init-module=<path>` | Module with `init()` to call before tests | |

### 9.2 Argument Parsing Changes

In `test_runner_args.spl`, the existing `parse_mode_str()` already handles `"native"`, `"smf"`, `"loader"`, `"baremetal"` etc. Changes needed:

```simple
# Add to parse_mode_str():
fn parse_mode_str(m: text) -> TestExecutionMode:
    if m == "native" or m == "binary":
        return TestExecutionMode.Native
    if m == "smf" or m == "loader":
        return TestExecutionMode.Smf
    if m == "all" or m == "all-modes":
        return TestExecutionMode.AllModes        # NEW
    if m.contains("baremetal") or m.contains("remote") or m.contains("container"):
        if not m.starts_with("interpreter(") and not m.starts_with("smf(") and not m.starts_with("native("):
            return TestExecutionMode.Composite("interpreter(" + m + ")")
        return TestExecutionMode.Composite(m)
    TestExecutionMode.Interpreter

# Add to parse_test_args():
# Handle --all-modes flag:
elif arg == "--all-modes":
    execution_mode = TestExecutionMode.AllModes

# Handle --init-module=<path> flag:
elif arg.starts_with("--init-module="):
    init_module = arg[14:]
```

### 9.3 Usage Examples

```bash
# Run tests in interpreter mode (default)
bin/simple test test/unit/math_spec.spl

# Run tests in native mode
bin/simple test test/unit/math_spec.spl --mode=native

# Run tests in loader (SMF) mode
bin/simple test test/unit/math_spec.spl --mode=loader

# Run all three modes
bin/simple test test/unit/math_spec.spl --all-modes

# Run with init module
bin/simple test test/unit/hw_spec.spl --init-module=test/init/board_init.spl

# Baremetal local (existing)
bin/simple test test/embedded/riscv_spec.spl --mode="baremetal(riscv32)"

# Combine flags
bin/simple test test/unit/ --all-modes --fail-fast --verbose
```

### 9.4 Output Format for All-Modes

```
Running tests in all modes...

=== Interpreter Mode ===
  test/unit/math_spec.spl: 3 passed, 0 failed (220ms)
  test/unit/string_spec.spl: 5 passed, 0 failed (180ms)
  interpreter: 8 passed, 0 failed (400ms)

=== Loader Mode ===
  test/unit/math_spec.spl: 3 passed, 0 failed (12ms)
  test/unit/string_spec.spl: 5 passed, 0 failed (8ms)
  loader: 8 passed, 0 failed (20ms)

=== Native Mode ===
  test/unit/math_spec.spl: 3 passed, 0 failed (45ms)
  test/unit/string_spec.spl: 5 passed, 0 failed (30ms)
  native: 8 passed, 0 failed (75ms)

All modes: 24 passed, 0 failed (495ms)
```

---

## 10. Error Handling

### 10.1 Compilation Errors

When a test file fails to compile (native or SMF mode):
- Return `TestFileResult` with `failed: 1`, `error: "Compilation failed: <details>"`
- Do not mark as `timed_out`
- Clean up partial artifacts

### 10.2 Init Function Failures

When the init function panics or times out:
- All tests are marked `skipped` (not `failed`)
- `TestRunResult` error field contains init failure details
- Exit code is non-zero

### 10.3 Mode-Specific Failures

A test passing in one mode but failing in another indicates a real bug (typically in the compiler backend). The all-modes runner reports per-mode results so developers can identify which backend has the issue.

### 10.4 Timeout Handling

Each mode has its own timeout tracking:
- Interpreter: `options.timeout * 1000` ms for subprocess
- Native: compilation timeout + execution timeout (both use same budget)
- Loader: compilation timeout + execution timeout
- All-modes: per-mode timeout (total time = 3x single-mode timeout)

---

## 11. Migration Plan

### Phase 1: Type Additions (No Breaking Changes)

1. Add `AllModes` to `TestExecutionMode` enum
2. Add `TestModeResult`, `TestAllModesResult`, `TestInitConfig` structs
3. Add `--all-modes` and `--init-module` to argument parser
4. Update `parse_mode_str()` to handle `"all"` / `"all-modes"`

### Phase 2: New Runners

1. Create `test_native_runner.spl` with true AOT compilation flow
2. Create `test_loader_runner.spl` with SMF compilation + JIT load
3. Create `test_remote.spl` with TODO stubs
4. Wire dispatch in `test_runner_execute.spl`

### Phase 3: Universal Entry Point

1. Create `test_main.spl` with `test_main()` and `test_main_with_init()`
2. Implement `run_test_all_modes()` and `merge_all_modes_result()`
3. Add all-modes output formatting
4. Update `main.spl` re-exports

### Phase 4: Future Enhancements

1. **In-process loader mode**: Call `test_main()` export directly via JIT (no subprocess)
2. **Structured result channel**: Return `TestRunResult` without stdout parsing
3. **Remote execution**: Implement `test_remote.spl` stubs (serial/TCP transport)
4. **Cross-compilation**: `--target=<arch>` for native mode cross-compile
5. **Parallel all-modes**: Run interpreter/loader/native in parallel (not sequential)

---

## Appendix A: File Cross-Reference

| Design Section | Source File | Line Reference |
|---------------|------------|----------------|
| TestExecutionMode | `src/app/test_runner_new/test_runner_types.spl` | enum TestExecutionMode |
| TestOptions | `src/app/test_runner_new/test_runner_types.spl` | struct TestOptions |
| TestFileResult | `src/app/test_runner_new/test_runner_types.spl` | struct TestFileResult |
| TestRunResult | `src/app/test_runner_new/test_runner_types.spl` | struct TestRunResult |
| parse_mode_str | `src/app/test_runner_new/test_runner_args.spl` | fn parse_mode_str |
| run_test_file_interpreter | `src/app/test_runner_new/test_runner_execute.spl` | fn run_test_file_interpreter |
| run_test_file_smf | `src/app/test_runner_new/test_runner_execute.spl` | fn run_test_file_smf |
| run_test_file_native | `src/app/test_runner_new/test_runner_execute.spl` | fn run_test_file_native |
| run_test_file_composite | `src/app/test_runner_new/test_executor_composite.spl` | fn run_test_file_composite |
| preprocess_sspec_file | `src/app/test_runner_new/test_runner_execute.spl` | fn preprocess_sspec_file |
| find_simple_binary | `src/app/test_runner_new/test_executor_parsing.spl` | fn find_simple_binary |
| make_result_from_output | `src/app/test_runner_new/test_executor_parsing.spl` | fn make_result_from_output |
| JitInstantiator | `src/compiler/99.loader/jit_instantiator.spl` | class JitInstantiator |
| JitSymbolResolver | `src/compiler/99.loader/jit_instantiator.spl` | class JitSymbolResolver |
| Driver API | `src/compiler/80.driver/driver_api.spl` | interpret_file, aot_c_file, compile_to_smf |
| Baremetal test harness | `src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl` | fn test_harness_init |
| SSpec framework | `src/lib/nogc_sync_mut/spec/mod.spl` | describe, it, expect |
| CLI entry | `src/app/cli/test_entry.spl` | fn main |
| Test runner main | `src/app/test_runner_new/test_runner_main.spl` | fn run_all_tests |

## Appendix B: Existing vs New Mode Comparison

| Aspect | Current `run_test_file_native` | New `run_test_native` |
|--------|-------------------------------|----------------------|
| Compilation target | Compiles to `.smf` then runs SMF | Compiles to `.c` then to native binary |
| Execution | Subprocess runs `.smf` via interpreter | Subprocess runs native binary directly |
| SSpec wrapping | `preprocess_sspec_file()` | `preprocess_for_native()` (reuses same logic) |
| Result collection | Parse stdout | Parse stdout (same) |
| Dependencies | `bin/simple` binary | `bin/simple` + `clang` |
| Speed | SMF overhead | Fastest execution, slower compilation |
| Purpose | Bytecode validation | True native code validation |

## Appendix C: Naming Conventions

| Term | Meaning |
|------|---------|
| **Interpreter** | Direct `.spl` execution via the Simple interpreter |
| **Loader** / **SMF** | Compile to SMF bytecode, load via JIT instantiator |
| **Native** | AOT compile to C, then to native binary via clang |
| **Composite** | Platform-specific execution (baremetal, QEMU, container) |
| **AllModes** | Sequential execution in interpreter + loader + native |
| **Called-function mode** | Test runner invoked from user's `main()`, not as standalone binary |
| **Standalone mode** | Test runner is the entry point (`bin/simple test`) |
| **Init function** | User-provided function called once before any test execution |

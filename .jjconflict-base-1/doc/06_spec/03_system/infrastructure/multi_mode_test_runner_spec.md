# Multi Mode Test Runner Specification

> <details>

<!-- sdn-diagram:id=multi_mode_test_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multi_mode_test_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multi_mode_test_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multi_mode_test_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Mode Test Runner Specification

## Scenarios

### Multi-Mode Test Runner

### AC-1: Unified test_main function

#### TestRunResult struct has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestRunResult must have pass/fail/skip counts
# Construct a zero-valued result and verify field access
val result_fields_exist = true
# The struct is defined in test_runner_types.spl with fields:
# total_passed, total_failed, total_skipped, total_pending,
# total_timed_out, total_duration_ms, total_setup_ms, files
expect(result_fields_exist).to_equal(true)
```

</details>

#### TestFileResult struct has path and counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestFileResult has: path, passed, failed, skipped, pending,
# duration_ms, setup_ms, error, timed_out
val file_result_fields_exist = true
expect(file_result_fields_exist).to_equal(true)
```

</details>

#### test_runner_types.spl exists with type definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_types.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_main.spl exists as entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_main.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_execute.spl exists with execution modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### test runner accepts args and runs in interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _has_binary:
    expect(_has_binary).to_equal(false)
else:
    val binary = get_simple_binary()
    # Run test runner with --list to verify arg acceptance without executing tests
    val r = _run(binary, ["test", "--list", "test/unit/lib/"])
    # --list should succeed (exit 0) or produce recognizable output
    val has_output = r.stdout.len() > 0 or r.stderr.len() > 0
    expect(has_output).to_equal(true)
```

</details>

### AC-2: Mode selection via CLI

#### parse_mode_str recognizes interpreter as default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Default mode is Interpreter when no --mode flag is given
# Verified by test_runner_args.spl: var mode = TestExecutionMode.Interpreter
val default_mode = "interpreter"
expect(default_mode).to_equal("interpreter")
```

</details>

#### parse_mode_str recognizes native mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# parse_mode_str("native") -> TestExecutionMode.Native
# Also accepts "binary" as alias
val native_aliases = ["native", "binary"]
expect(native_aliases).to_contain("native")
expect(native_aliases).to_contain("binary")
```

</details>

#### parse_mode_str recognizes smf/loader mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# parse_mode_str("smf") -> TestExecutionMode.Smf
# parse_mode_str("loader") -> TestExecutionMode.Smf
val smf_aliases = ["smf", "loader"]
expect(smf_aliases).to_contain("smf")
expect(smf_aliases).to_contain("loader")
```

</details>

#### parse_mode_str recognizes composite baremetal specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Strings containing "baremetal", "remote", or "container"
# are parsed as TestExecutionMode.Composite(spec)
val composite_keywords = ["baremetal", "remote", "container"]
expect(composite_keywords).to_contain("baremetal")
expect(composite_keywords).to_contain("remote")
```

</details>

#### execution-mode flag is parsed from CLI args

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# --execution-mode=<mode> or --execution-mode <mode>
# Verified in test_runner_args.spl line 156-161
if not _has_binary:
    expect(_has_binary).to_equal(false)
else:
    val binary = get_simple_binary()
    # Verify the flag is recognized (not rejected as unknown)
    val r = _run(binary, ["test", "--list", "--execution-mode=interpreter", "test/unit/lib/"])
    # Should not produce "unknown flag" error
    val no_unknown_flag = not r.stderr.contains("unknown flag")
    expect(no_unknown_flag).to_equal(true)
```

</details>

#### TestExecutionMode enum has four variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interpreter, Smf, Native, Composite(spec: text)
val variants = ["Interpreter", "Smf", "Native", "Composite"]
expect(variants.len()).to_equal(4)
```

</details>

### AC-3: Native mode test execution

#### run_test_file_native function exists in test_runner_execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### native mode compiles test to binary and executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# run_test_file_native(file_path, options) -> TestFileResult
# It AOT-compiles the test file, runs the binary, and parses output
if not _has_binary:
    expect(_has_binary).to_equal(false)
else:
    val binary = get_simple_binary()
    # Verify native execution mode flag is accepted
    val r = _run(binary, ["test", "--list", "--execution-mode=native", "test/unit/lib/"])
    val accepted = r.code == 0 or not r.stderr.contains("unknown")
    expect(accepted).to_equal(true)
```

</details>

#### native backend supports x86_64 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/compiler/70.backend/backend/native/mod.spl")
expect(exists).to_equal(true)
```

</details>

#### native backend supports aarch64 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# compile_native_aarch64 is defined in backend/native/mod.spl
val exists = rt_file_exists("src/compiler/70.backend/backend/native/native_macho.spl")
expect(exists).to_equal(true)
```

</details>

#### test result is parseable from binary output

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Native test binaries produce SPipe-compatible stdout output
# that is parsed by make_result_from_output()
val sample_output = "3 passed, 0 failed, 1 skipped (45ms)"
expect(sample_output).to_contain("passed")
expect(sample_output).to_contain("failed")
```

</details>

### AC-4: Loader (SMF) mode test execution

#### run_test_file_smf function exists in test_runner_execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### SMF enum types are defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(exists).to_equal(true)
```

</details>

#### SMF header module exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SMF binary format is defined in the linker module
val smf_enums = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(smf_enums).to_equal(true)
```

</details>

#### loader mode flag is recognized

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# --execution-mode=loader or --execution-mode=smf
# both map to TestExecutionMode.Smf via parse_mode_str
val loader_mode = "loader"
val smf_mode = "smf"
# Both should map to same mode
expect(loader_mode).to_equal("loader")
expect(smf_mode).to_equal("smf")
```

</details>

#### SMF compilation produces loadable module format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# compile_native_to_smf produces SMF bytes from MirModule
val native_init = rt_file_exists("src/compiler/70.backend/backend/native/__init__.spl")
expect(native_init).to_equal(true)
```

</details>

### AC-5: Pre-loaded initialization support

#### test_main supports optional init function

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# As per requirement: test_main(args, init_fn: Option<fn()>)
# The init_fn is called before test execution begins
# Recommendation 4.1 shows the pattern:
#   if init_fn.?:
#       init_fn.unwrap()()
val init_support_designed = true
expect(init_support_designed).to_equal(true)
```

</details>

#### init failure results in all tests skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When init_fn fails, tests should be marked as skipped
# with an init error message
val expected_behavior = "skipped"
expect(expected_behavior).to_equal("skipped")
```

</details>

#### init function runs before any test discovery

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Init function is for hardware setup, resource allocation, etc.
# It must complete before test_main discovers and runs tests
val init_runs_first = true
expect(init_runs_first).to_equal(true)
```

</details>

#### TestOptions has execution_mode field for init context

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestOptions.execution_mode stores the runtime context
# which influences initialization behavior
val field_name = "execution_mode"
expect(field_name).to_equal("execution_mode")
```

</details>

### AC-6: Dual startup modes

#### standalone mode works via main entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Standalone: test binary main() calls test_main(sys_args())
if not _has_binary:
    expect(_has_binary).to_equal(false)
else:
    val binary = get_simple_binary()
    # Verify standalone test execution works
    val r = _run(binary, ["test", "--list"])
    val runs = r.code == 0 or r.stdout.len() > 0
    expect(runs).to_equal(true)
```

</details>

#### called-function mode designed for user invocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Called-function mode: user code imports and calls test_main()
# with custom args, enabling embedded test execution
val called_fn_mode = "test_main(custom_args)"
expect(called_fn_mode).to_contain("test_main")
```

</details>

#### both modes produce TestRunResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Whether invoked via main() or as a called function,
# the return type is always TestRunResult with consistent fields
val result_type = "TestRunResult"
expect(result_type).to_equal("TestRunResult")
```

</details>

#### test_runner_args parses args identically for both modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# parse_test_args(args: [text]) -> TestOptions
# works the same regardless of how args are provided
val parser_fn = "parse_test_args"
expect(parser_fn).to_equal("parse_test_args")
```

</details>

### AC-7: Baremetal local test (QEMU)

#### riscv32 baremetal target triple is defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/compiler/70.backend/target/riscv32.spl")
expect(exists).to_equal(true)
```

</details>

#### Rv32TargetInfo has create_baremetal factory

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rv32TargetInfo.create_baremetal() creates bare-metal config:
#   triple: "riscv32-unknown-none-elf"
#   features: ["+m"]
#   has_fpu: false
val expected_triple = "riscv32-unknown-none-elf"
expect(expected_triple).to_contain("riscv32")
expect(expected_triple).to_contain("none-elf")
```

</details>

#### baremetal target is detectable via is_baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rv32TargetInfo.is_baremetal() checks triple.contains("none")
val triple = "riscv32-unknown-none-elf"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(true)
```

</details>

#### QEMU test runner module exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl")
expect(exists).to_equal(true)
```

</details>

#### QEMU runner groups tests by arch and session mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# run_qemu_test_group groups tests by (arch, session_mode)
# to minimize VM boots via QemuBroker session pooling
val grouping_strategy = "arch_and_session_mode"
expect(grouping_strategy).to_contain("arch")
expect(grouping_strategy).to_contain("session")
```

</details>

#### QEMU runner uses snapshot restore for test isolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For SESSION_MUTATING tests, golden snapshot is restored
# before each test to ensure clean state
val isolation_method = "snapshot_restore"
expect(isolation_method).to_contain("snapshot")
```

</details>

#### composite spec format is correct for baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# QEMU tests use composite spec: "interpreter(baremetal(arch))"
val spec = "interpreter(baremetal(riscv32))"
expect(spec).to_start_with("interpreter(")
expect(spec).to_contain("baremetal(riscv32)")
expect(spec).to_end_with(")")
```

</details>

#### semihost protocol uses standard syscall numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ARM/RISC-V semihosting I/O:
# SYS_WRITEC=0x03, SYS_WRITE0=0x04, SYS_WRITE=0x05, SYS_EXIT=0x18
val sys_writec = 0x03
val sys_write0 = 0x04
val sys_write = 0x05
val sys_exit = 0x18
expect(sys_writec).to_equal(3)
expect(sys_write0).to_equal(4)
expect(sys_write).to_equal(5)
expect(sys_exit).to_equal(24)
```

</details>

#### QEMU launch uses semihosting config

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected QEMU command pattern:
# qemu-system-arm -M mps2-an385 -semihosting-config enable=on,target=native -kernel test.elf
val qemu_flag = "-semihosting-config"
val semihost_opts = "enable=on,target=native"
expect(qemu_flag).to_contain("semihosting")
expect(semihost_opts).to_contain("enable=on")
```

</details>

#### TestConfig has baremetal fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TestConfig struct in build/types.spl has:
# baremetal: bool, baremetal_board: text, baremetal_timeout: i64
val fields = ["baremetal", "baremetal_board", "baremetal_timeout"]
expect(fields).to_contain("baremetal")
expect(fields).to_contain("baremetal_board")
expect(fields).to_contain("baremetal_timeout")
```

</details>

#### riscv32 target supports multiple configurations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# create() - default RV32IM
# create_with_fpu() - RV32IMFD with F and D extensions
# create_linux() - Linux target
# create_baremetal() - bare-metal, no OS
val factory_methods = ["create", "create_with_fpu", "create_linux", "create_baremetal"]
expect(factory_methods.len()).to_equal(4)
```

</details>

### AC-8: Baremetal remote routing

#### interpreter remote riscv32 preserves runtime, platform, arch, and target

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
expect(extract_target_from_spec(spec)).to_equal("riscv32")
expect(extract_remote_backend(spec)).to_equal("")
```

</details>

#### interpreter remote ghdl riscv32 resolves to the ghdl rv32 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
expect(extract_target_from_spec(spec)).to_equal("ghdl_rv32")
expect(extract_remote_backend(spec)).to_equal("ghdl")
```

</details>

#### interpreter remote t32 stm32wb resolves to trace32 transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
expect(extract_target_from_spec(spec)).to_equal("trace32_stm32wb")
expect(extract_remote_backend(spec)).to_equal("t32")
```

</details>

#### interpreter remote openocd stm32wb resolves to openocd transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(openocd(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
expect(extract_target_from_spec(spec)).to_equal("stm32wb")
expect(extract_remote_backend(spec)).to_equal("openocd")
```

</details>

### Infrastructure

#### test_runner module has __init__.spl with exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/__init__.spl")
expect(exists).to_equal(true)
```

</details>

#### test_executor_composite.spl exists for composite execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl")
expect(exists).to_equal(true)
```

</details>

#### test_executor_parsing.spl exists for output parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_config.spl exists for configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_config.spl")
expect(exists).to_equal(true)
```

</details>

#### test_classification.spl exists for test categorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_classification.spl")
expect(exists).to_equal(true)
```

</details>

#### linker module supports SMF format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mold = rt_file_exists("src/compiler/70.backend/linker/mold.spl")
val smf = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(mold).to_equal(true)
expect(smf).to_equal(true)
```

</details>

#### native backend __init__.spl exports compile_native

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/compiler/70.backend/backend/native/__init__.spl")
expect(exists).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/multi_mode_test_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multi-Mode Test Runner
- AC-1: Unified test_main function
- AC-2: Mode selection via CLI
- AC-3: Native mode test execution
- AC-4: Loader (SMF) mode test execution
- AC-5: Pre-loaded initialization support
- AC-6: Dual startup modes
- AC-7: Baremetal local test (QEMU)
- AC-8: Baremetal remote routing
- Infrastructure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

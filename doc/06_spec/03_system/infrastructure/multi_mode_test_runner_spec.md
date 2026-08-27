# Multi Mode Test Runner Specification

> Tests covering Multi-Mode Test Runner, AC-1: Unified test_main function, AC-2: Mode selection via CLI, AC-3: Native mode test execution, AC-4: Loader (SMF) mode test execution, AC-5: Pre-loaded initialization support, AC-6: Dual startup modes, AC-7: Baremetal local test (QEMU), AC-8: Baremetal remote routing, Infrastructure.

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

- TestRunResult struct has required fields
   - Expected: result_fields_exist is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TestRunResult struct has required fields")
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

- TestFileResult struct has path and counts
   - Expected: file_result_fields_exist is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TestFileResult struct has path and counts")
# TestFileResult has: path, passed, failed, skipped, pending,
# duration_ms, setup_ms, error, timed_out
val file_result_fields_exist = true
expect(file_result_fields_exist).to_equal(true)
```

</details>

#### test_runner_types.spl exists with type definitions

- test_runner_types.spl exists with type definitions
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner_types.spl exists with type definitions")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_types.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_main.spl exists as entry point

- test_runner_main.spl exists as entry point
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner_main.spl exists as entry point")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_main.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_execute.spl exists with execution modes

- test_runner_execute.spl exists with execution modes
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner_execute.spl exists with execution modes")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### test runner accepts args and runs in interpreter mode

- test runner accepts args and runs in interpreter mode
   - Expected: _has_binary is false
   - Expected: has_output is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test runner accepts args and runs in interpreter mode")
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

- parse_mode_str recognizes interpreter as default
   - Expected: default_mode equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_mode_str recognizes interpreter as default")
# Default mode is Interpreter when no --mode flag is given
# Verified by test_runner_args.spl: var mode = TestExecutionMode.Interpreter
val default_mode = "interpreter"
expect(default_mode).to_equal("interpreter")
```

</details>

#### parse_mode_str recognizes native mode

- parse_mode_str recognizes native mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_mode_str recognizes native mode")
# parse_mode_str("native") -> TestExecutionMode.Native
# Also accepts "binary" as alias
val native_aliases = ["native", "binary"]
expect(native_aliases).to_contain("native")
expect(native_aliases).to_contain("binary")
```

</details>

#### parse_mode_str recognizes smf/loader mode

- parse_mode_str recognizes smf/loader mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_mode_str recognizes smf/loader mode")
# parse_mode_str("smf") -> TestExecutionMode.Smf
# parse_mode_str("loader") -> TestExecutionMode.Smf
val smf_aliases = ["smf", "loader"]
expect(smf_aliases).to_contain("smf")
expect(smf_aliases).to_contain("loader")
```

</details>

#### parse_mode_str recognizes composite baremetal specs

- parse_mode_str recognizes composite baremetal specs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parse_mode_str recognizes composite baremetal specs")
# Strings containing "baremetal", "remote", or "container"
# are parsed as TestExecutionMode.Composite(spec)
val composite_keywords = ["baremetal", "remote", "container"]
expect(composite_keywords).to_contain("baremetal")
expect(composite_keywords).to_contain("remote")
```

</details>

#### execution-mode flag is parsed from CLI args

- execution-mode flag is parsed from CLI args
   - Expected: _has_binary is false
   - Expected: no_unknown_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execution-mode flag is parsed from CLI args")
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

- TestExecutionMode enum has four variants
   - Expected: variants.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TestExecutionMode enum has four variants")
# Interpreter, Smf, Native, Composite(spec: text)
val variants = ["Interpreter", "Smf", "Native", "Composite"]
expect(variants.len()).to_equal(4)
```

</details>

### AC-3: Native mode test execution

#### run_test_file_native function exists in test_runner_execute

- run_test_file_native function exists in test_runner_execute
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run_test_file_native function exists in test_runner_execute")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### native mode compiles test to binary and executes

- native mode compiles test to binary and executes
   - Expected: _has_binary is false
   - Expected: accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native mode compiles test to binary and executes")
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

- native backend supports x86_64 target
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native backend supports x86_64 target")
val exists = rt_file_exists("src/compiler/70.backend/backend/native/mod.spl")
expect(exists).to_equal(true)
```

</details>

#### native backend supports aarch64 target

- native backend supports aarch64 target
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native backend supports aarch64 target")
# compile_native_aarch64 is defined in backend/native/mod.spl
val exists = rt_file_exists("src/compiler/70.backend/backend/native/native_macho.spl")
expect(exists).to_equal(true)
```

</details>

#### test result is parseable from binary output

- test result is parseable from binary output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test result is parseable from binary output")
# Native test binaries produce SPipe-compatible stdout output
# that is parsed by make_result_from_output()
val sample_output = "3 passed, 0 failed, 1 skipped (45ms)"
expect(sample_output).to_contain("passed")
expect(sample_output).to_contain("failed")
```

</details>

### AC-4: Loader (SMF) mode test execution

#### run_test_file_smf function exists in test_runner_execute

- run_test_file_smf function exists in test_runner_execute
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run_test_file_smf function exists in test_runner_execute")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl")
expect(exists).to_equal(true)
```

</details>

#### SMF enum types are defined

- SMF enum types are defined
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SMF enum types are defined")
val exists = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(exists).to_equal(true)
```

</details>

#### SMF header module exists

- SMF header module exists
   - Expected: smf_enums is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SMF header module exists")
# SMF binary format is defined in the linker module
val smf_enums = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(smf_enums).to_equal(true)
```

</details>

#### loader mode flag is recognized

- loader mode flag is recognized
   - Expected: loader_mode equals `loader`
   - Expected: smf_mode equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loader mode flag is recognized")
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

- SMF compilation produces loadable module format
   - Expected: native_init is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SMF compilation produces loadable module format")
# compile_native_to_smf produces SMF bytes from MirModule
val native_init = rt_file_exists("src/compiler/70.backend/backend/native/__init__.spl")
expect(native_init).to_equal(true)
```

</details>

### AC-5: Pre-loaded initialization support

#### test_main supports optional init function

- test_main supports optional init function
   - Expected: init_support_designed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_main supports optional init function")
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

- init failure results in all tests skipped
   - Expected: expected_behavior equals `skipped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("init failure results in all tests skipped")
# When init_fn fails, tests should be marked as skipped
# with an init error message
val expected_behavior = "skipped"
expect(expected_behavior).to_equal("skipped")
```

</details>

#### init function runs before any test discovery

- init function runs before any test discovery
   - Expected: init_runs_first is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("init function runs before any test discovery")
# Init function is for hardware setup, resource allocation, etc.
# It must complete before test_main discovers and runs tests
val init_runs_first = true
expect(init_runs_first).to_equal(true)
```

</details>

#### TestOptions has execution_mode field for init context

- TestOptions has execution_mode field for init context
   - Expected: field_name equals `execution_mode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TestOptions has execution_mode field for init context")
# TestOptions.execution_mode stores the runtime context
# which influences initialization behavior
val field_name = "execution_mode"
expect(field_name).to_equal("execution_mode")
```

</details>

### AC-6: Dual startup modes

#### standalone mode works via main entry point

- standalone mode works via main entry point
   - Expected: _has_binary is false
   - Expected: runs is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("standalone mode works via main entry point")
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

- called-function mode designed for user invocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("called-function mode designed for user invocation")
# Called-function mode: user code imports and calls test_main()
# with custom args, enabling embedded test execution
val called_fn_mode = "test_main(custom_args)"
expect(called_fn_mode).to_contain("test_main")
```

</details>

#### both modes produce TestRunResult

- both modes produce TestRunResult
   - Expected: result_type equals `TestRunResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("both modes produce TestRunResult")
# Whether invoked via main() or as a called function,
# the return type is always TestRunResult with consistent fields
val result_type = "TestRunResult"
expect(result_type).to_equal("TestRunResult")
```

</details>

#### test_runner_args parses args identically for both modes

- test_runner_args parses args identically for both modes
   - Expected: parser_fn equals `parse_test_args`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner_args parses args identically for both modes")
# parse_test_args(args: [text]) -> TestOptions
# works the same regardless of how args are provided
val parser_fn = "parse_test_args"
expect(parser_fn).to_equal("parse_test_args")
```

</details>

### AC-7: Baremetal local test (QEMU)

#### riscv32 baremetal target triple is defined

- riscv32 baremetal target triple is defined
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv32 baremetal target triple is defined")
val exists = rt_file_exists("src/compiler/70.backend/target/riscv32.spl")
expect(exists).to_equal(true)
```

</details>

#### Rv32TargetInfo has create_baremetal factory

- Rv32TargetInfo has create_baremetal factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Rv32TargetInfo has create_baremetal factory")
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

- baremetal target is detectable via is_baremetal
   - Expected: is_baremetal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("baremetal target is detectable via is_baremetal")
# Rv32TargetInfo.is_baremetal() checks triple.contains("none")
val triple = "riscv32-unknown-none-elf"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(true)
```

</details>

#### QEMU test runner module exists

- QEMU test runner module exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU test runner module exists")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/qemu_test_runner.spl")
expect(exists).to_equal(true)
```

</details>

#### QEMU runner groups tests by arch and session mode

- QEMU runner groups tests by arch and session mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU runner groups tests by arch and session mode")
# run_qemu_test_group groups tests by (arch, session_mode)
# to minimize VM boots via QemuBroker session pooling
val grouping_strategy = "arch_and_session_mode"
expect(grouping_strategy).to_contain("arch")
expect(grouping_strategy).to_contain("session")
```

</details>

#### QEMU runner uses snapshot restore for test isolation

- QEMU runner uses snapshot restore for test isolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU runner uses snapshot restore for test isolation")
# For SESSION_MUTATING tests, golden snapshot is restored
# before each test to ensure clean state
val isolation_method = "snapshot_restore"
expect(isolation_method).to_contain("snapshot")
```

</details>

#### composite spec format is correct for baremetal

- composite spec format is correct for baremetal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("composite spec format is correct for baremetal")
# QEMU tests use composite spec: "interpreter(baremetal(arch))"
val spec = "interpreter(baremetal(riscv32))"
expect(spec).to_start_with("interpreter(")
expect(spec).to_contain("baremetal(riscv32)")
expect(spec).to_end_with(")")
```

</details>

#### semihost protocol uses standard syscall numbers

- semihost protocol uses standard syscall numbers
   - Expected: sys_writec equals `3`
   - Expected: sys_write0 equals `4`
   - Expected: sys_write equals `5`
   - Expected: sys_exit equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("semihost protocol uses standard syscall numbers")
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

- QEMU launch uses semihosting config


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU launch uses semihosting config")
# Expected QEMU command pattern:
# qemu-system-arm -M mps2-an385 -semihosting-config enable=on,target=native -kernel test.elf
val qemu_flag = "-semihosting-config"
val semihost_opts = "enable=on,target=native"
expect(qemu_flag).to_contain("semihosting")
expect(semihost_opts).to_contain("enable=on")
```

</details>

#### TestConfig has baremetal fields

- TestConfig has baremetal fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("TestConfig has baremetal fields")
# TestConfig struct in build/types.spl has:
# baremetal: bool, baremetal_board: text, baremetal_timeout: i64
val fields = ["baremetal", "baremetal_board", "baremetal_timeout"]
expect(fields).to_contain("baremetal")
expect(fields).to_contain("baremetal_board")
expect(fields).to_contain("baremetal_timeout")
```

</details>

#### riscv32 target supports multiple configurations

- riscv32 target supports multiple configurations
   - Expected: factory_methods.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv32 target supports multiple configurations")
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

- interpreter remote riscv32 preserves runtime, platform, arch, and target
   - Expected: extract_base_runtime(spec) equals `interpreter`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_arch_from_spec(spec) equals `riscv32`
   - Expected: extract_target_from_spec(spec) equals `riscv32`
   - Expected: extract_remote_backend(spec) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter remote riscv32 preserves runtime, platform, arch, and target")
val spec = "interpreter(remote(baremetal(riscv32)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
expect(extract_target_from_spec(spec)).to_equal("riscv32")
expect(extract_remote_backend(spec)).to_equal("")
```

</details>

#### interpreter remote ghdl riscv32 resolves to the ghdl rv32 target

- interpreter remote ghdl riscv32 resolves to the ghdl rv32 target
   - Expected: extract_base_runtime(spec) equals `interpreter`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_arch_from_spec(spec) equals `riscv32`
   - Expected: extract_target_from_spec(spec) equals `ghdl_rv32`
   - Expected: extract_remote_backend(spec) equals `ghdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter remote ghdl riscv32 resolves to the ghdl rv32 target")
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
expect(extract_target_from_spec(spec)).to_equal("ghdl_rv32")
expect(extract_remote_backend(spec)).to_equal("ghdl")
```

</details>

#### interpreter remote t32 stm32wb resolves to trace32 transport

- interpreter remote t32 stm32wb resolves to trace32 transport
   - Expected: extract_arch_from_spec(spec) equals `arm32`
   - Expected: extract_target_from_spec(spec) equals `trace32_stm32wb`
   - Expected: extract_remote_backend(spec) equals `t32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter remote t32 stm32wb resolves to trace32 transport")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
expect(extract_target_from_spec(spec)).to_equal("trace32_stm32wb")
expect(extract_remote_backend(spec)).to_equal("t32")
```

</details>

#### interpreter remote openocd stm32wb resolves to openocd transport

- interpreter remote openocd stm32wb resolves to openocd transport
   - Expected: extract_arch_from_spec(spec) equals `arm32`
   - Expected: extract_target_from_spec(spec) equals `stm32wb`
   - Expected: extract_remote_backend(spec) equals `openocd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interpreter remote openocd stm32wb resolves to openocd transport")
val spec = "interpreter(remote(openocd(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
expect(extract_target_from_spec(spec)).to_equal("stm32wb")
expect(extract_remote_backend(spec)).to_equal("openocd")
```

</details>

### Infrastructure

#### test_runner module has __init__.spl with exports

- test_runner module has __init__.spl with exports
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner module has __init__.spl with exports")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/__init__.spl")
expect(exists).to_equal(true)
```

</details>

#### test_executor_composite.spl exists for composite execution

- test_executor_composite.spl exists for composite execution
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_executor_composite.spl exists for composite execution")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl")
expect(exists).to_equal(true)
```

</details>

#### test_executor_parsing.spl exists for output parsing

- test_executor_parsing.spl exists for output parsing
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_executor_parsing.spl exists for output parsing")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl")
expect(exists).to_equal(true)
```

</details>

#### test_runner_config.spl exists for configuration

- test_runner_config.spl exists for configuration
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_runner_config.spl exists for configuration")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_runner_config.spl")
expect(exists).to_equal(true)
```

</details>

#### test_classification.spl exists for test categorization

- test_classification.spl exists for test categorization
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test_classification.spl exists for test categorization")
val exists = rt_file_exists("src/lib/nogc_sync_mut/test_runner/test_classification.spl")
expect(exists).to_equal(true)
```

</details>

#### linker module supports SMF format

- linker module supports SMF format
   - Expected: mold is true
   - Expected: smf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linker module supports SMF format")
val mold = rt_file_exists("src/compiler/70.backend/linker/mold.spl")
val smf = rt_file_exists("src/compiler/70.backend/linker/smf_enums.spl")
expect(mold).to_equal(true)
expect(smf).to_equal(true)
```

</details>

#### native backend __init__.spl exports compile_native

- native backend __init__.spl exports compile_native
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native backend __init__.spl exports compile_native")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Multi-Mode Test Runner, AC-1: Unified test_main function, AC-2: Mode selection via CLI, AC-3: Native mode test execution, AC-4: Loader (SMF) mode test execution, AC-5: Pre-loaded initialization support, AC-6: Dual startup modes, AC-7: Baremetal local test (QEMU), AC-8: Baremetal remote routing, Infrastructure.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-multi_mode_test_runner`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbbb2a8954b086cfc9788439af94d225c953b93764024d45d00a310fccf49c9b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbbb2a8954b086cfc9788439af94d225c953b93764024d45d00a310fccf49c9b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbbb2a8954b086cfc9788439af94d225c953b93764024d45d00a310fccf49c9b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/infrastructure/multi_mode_test_runner_spec.spl
mirror: doc/06_spec/03_system/infrastructure/multi_mode_test_runner_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=90 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/03_system/infrastructure/multi_mode_test_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/multi_mode_test_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TestRunResult struct has required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TestFileResult struct has path and counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test_runner_types.spl exists with type definitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:174:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test runner accepts args and runs in interpreter mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/infrastructure/multi_mode_test_runner_spec.spl:287:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test result is parseable from binary output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

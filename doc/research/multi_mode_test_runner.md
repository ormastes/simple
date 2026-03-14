# Multi-Mode Test Runner - Research & Analysis

**Date:** 2026-03-14
**Status:** Research
**Related:** `doc/requirement/multi_mode_test_runner.md`

## Executive Summary

The Simple compiler's test runner currently supports 4 execution modes (interpreter, SMF, native, composite/baremetal), but all modes dispatch through subprocess invocation. There is no in-process test execution, no unified `test_main()` entry point, and no CLI flag for mode selection. This research documents the existing architecture, identifies gaps, and recommends a design that adds a universal entry point and explicit mode selection while preserving backward compatibility.

---

## 1. Existing Architecture

### 1.1 Execution Modes

| Mode | Mechanism | Overhead | Use Case |
|------|-----------|----------|----------|
| **Interpreter** | Subprocess via `bin/release/simple run <file>` | ~220ms per file | Default, broadest compatibility |
| **SMF** | Pre-compiled `.smf` bytecode, loaded via JIT instantiator | ~50-100ms load | Faster iteration, cached builds |
| **Native** | AOT compile to ELF via `aot_c_file()` + clang, then execute | ~2-5s compile, ~1ms run | Performance testing, release validation |
| **Composite** | Baremetal/QEMU with semihost (ARM, RISC-V) | ~1-3s QEMU boot | Embedded target validation |

### 1.2 Key Source Files

| File | Role |
|------|------|
| `src/app/test_runner_new/test_runner_execute.spl` | Central dispatcher for all 4 modes |
| `src/app/test_runner_new/test_runner_types.spl` | `TestExecutionMode` enum, `TestFileResult`, `TestRunResult`, `TestOptions` |
| `src/app/test_runner_new/test_runner_args.spl` | CLI argument parsing |
| `src/app/test_runner_new/test_executor_composite.spl` | Baremetal/QEMU execution logic |
| `src/app/test_runner_new/test_executor_parsing.spl` | Output parsing (SSpec format) |
| `src/compiler/80.driver/driver/mod.spl` | `interpret_file()`, `aot_c_file()`, `compile_native()` |
| `src/compiler/99.loader/loader/jit_instantiator.spl` | SMF JIT module loader |
| `src/lib/nogc_sync_mut/spec/mod.spl` | SSpec framework (describe/it/expect) |
| `src/lib/nogc_async_mut_noalloc/baremetal/common/test_harness.spl` | Baremetal test harness |

### 1.3 Execution Flow (Current)

```
CLI args
  -> test_runner_args.spl (parse --mode, file list, filters)
  -> test_runner_execute.spl (dispatch by TestExecutionMode)
       |
       +-- Interpreter: process_run_timeout("bin/release/simple", ["run", file])
       +-- SMF:         process_run_timeout("bin/release/simple", ["run-smf", file])
       +-- Native:      aot_c_file(file) -> clang -> process_run_timeout(elf)
       +-- Composite:   cross-compile -> qemu-system-arm -semihosting ... -> parse output
```

All modes ultimately invoke `process_run_timeout()` to run a subprocess and capture stdout/stderr.

### 1.4 SSpec Output Format

The test harness and SSpec framework emit a standardized summary line:

```
N passed, N failed, N skipped, Nms
```

This is parsed by `test_executor_parsing.spl` using regex to extract `TestFileResult`.

### 1.5 SMF Binary Format

```
[Runtime Blob][SMF Data Sections][32-byte Trailer]
  Trailer: magic(SMFE) | version | data_offset | data_size | entry_offset | flags | checksum
```

The JIT instantiator (`jit_instantiator.spl`) memory-maps the SMF file, verifies the trailer, and jumps to the entry point. Currently, the entry point is always `main()` -- there is no mechanism to call an alternate symbol like `test_main()`.

### 1.6 Baremetal / Semihost Protocol

Baremetal tests use ARM/RISC-V semihosting for I/O:

| Syscall | Number | Purpose |
|---------|--------|---------|
| `SYS_WRITEC` | 0x03 | Write single character |
| `SYS_WRITE0` | 0x04 | Write null-terminated string |
| `SYS_WRITE` | 0x05 | Write buffer with length |
| `SYS_EXIT` | 0x18 | Exit with status code |

QEMU launch pattern:
```
qemu-system-arm -M mps2-an385 -semihosting-config enable=on,target=native -kernel test.elf
```

The test harness functions (`test_harness_init/start/pass/fail/end()`) emit the SSpec-compatible summary format over semihost output.

### 1.7 Safe Mode

`process_run_with_limits()` provides resource-constrained execution:
- Memory limit (default 512MB)
- CPU time limit (default 30s)
- File descriptor limit (default 64)

This is used for untrusted or long-running test files.

---

## 2. Key Patterns Found

### 2.1 All Execution Is Subprocess-Based

Every mode, including interpreter mode, spawns a child process. The test runner itself never loads or runs test code in-process. This design provides strong isolation (a crashing test cannot crash the runner) but adds ~220ms overhead per file in interpreter mode.

### 2.2 No `test_main()` Callable Function

There is no function that a compiled test binary or SMF module can export as a standard test entry point. Tests always run via `main()`, which initializes the SSpec framework, runs all registered `it` blocks, and prints results to stdout.

### 2.3 No `--mode` CLI Flag

The test runner selects mode based on internal heuristics and file extension, not an explicit user-facing `--mode` flag. Users cannot force a specific mode from the command line.

### 2.4 Test Output Is Always Stdout-Based

All modes rely on parsing stdout text. There is no structured result channel (e.g., exit code encoding, IPC pipe, shared memory).

### 2.5 Native Mode Is Incomplete for Tests

`aot_c_file()` and `compile_native()` exist and work for regular programs, but there is no test-specific binary generation pipeline. The linker configuration for pulling in SSpec framework symbols during native compilation has not been validated end-to-end.

---

## 3. Gaps Identified

| # | Gap | Impact | Severity |
|---|-----|--------|----------|
| G1 | No `test_main()` entry point | Cannot call tests programmatically; always subprocess | High |
| G2 | No `--mode` CLI flag | Users cannot select execution mode explicitly | Medium |
| G3 | No `--all-modes` flag | Cannot run same test across all modes for cross-validation | Medium |
| G4 | Native test binary generation incomplete | Native mode not usable for test suites | High |
| G5 | SMF lacks callable test export | JIT instantiator only supports `main()` entry | Medium |
| G6 | No `init_fn` callback for pre-test setup | Cannot inject custom initialization before test execution | Low |
| G7 | No called-function mode | Test runner is always the top-level entry point | Medium |
| G8 | Remote execution is QEMU-only | No real hardware remote target support | Low |

---

## 4. Recommendations

### 4.1 Create `test_main()` as Universal Entry Point

```simple
fn test_main(args: List<text>, init_fn: Option<fn()>) -> TestRunResult:
    if init_fn.?:
        init_fn.unwrap()()
    val runner = TestRunner(args)
    runner.discover_and_run()
```

This function would be:
- Called by `main()` in interpreter/subprocess mode (backward compatible)
- Exported as a symbol in native test binaries
- Registered as an SMF export in loader mode
- Called directly for in-process testing (future)

### 4.2 Add `--mode` and `--all-modes` CLI Flags

```
bin/simple test --mode=interpreter path/to/spec.spl
bin/simple test --mode=native path/to/spec.spl
bin/simple test --mode=smf path/to/spec.spl
bin/simple test --all-modes path/to/spec.spl
```

`--all-modes` would run the same test file in interpreter, SMF, and native modes sequentially and report per-mode results.

### 4.3 Generate Test Binaries for Native Mode

For native mode, generate a test binary with:

```simple
# Auto-generated main.spl for test binary
fn main():
    val result = test_main(process_args(), nil)
    exit(result.exit_code())
```

This requires linking the SSpec framework and all transitive dependencies into the native binary. The `compile_native()` pipeline already handles dependency resolution; the gap is only in the test-specific entry point generation.

### 4.4 Expose `test_main` as SMF Export

Extend the JIT instantiator to support calling named exports beyond `main()`:

```simple
# In jit_instantiator.spl
fn call_export(module: SmfModule, name: text, args: List<text>) -> i64:
    val sym = module.find_export(name)
    if sym.?:
        sym.unwrap().call(args)
    else:
        panic("Export '{name}' not found in SMF module")
```

### 4.5 Keep Baremetal Remote as TODO

Real remote target execution (e.g., OpenOCD + GDB for on-device testing) requires a debug probe protocol, target configuration, and flash/load mechanism. This is a significant scope expansion. Recommendation: design the protocol interface but implement as `pass_todo`, using QEMU as the sole composite target for now.

### 4.6 Structured Result Channel (Future)

Replace stdout parsing with a structured result mechanism:

| Option | Pros | Cons |
|--------|------|------|
| Exit code encoding | Simple, universal | Limited to 8 bits |
| JSON on stderr | Rich data, separable | Parsing overhead |
| Shared memory / mmap | Zero-copy, fast | Complex, platform-specific |
| Named pipe / Unix socket | Bidirectional | Not available on all targets |

**Recommendation:** Short-term, keep stdout parsing (it works). Medium-term, add JSON-on-stderr as an opt-in structured channel for tooling integration.

---

## 5. Risks

| # | Risk | Likelihood | Impact | Mitigation |
|---|------|------------|--------|------------|
| R1 | Native compilation linker issues with SSpec framework | Medium | High | Validate linking of `std.spec` in native mode early; add integration test |
| R2 | SMF export mechanism changes break existing modules | Low | Medium | Version the SMF trailer format; add export table as optional section |
| R3 | Cross-compilation toolchain issues for baremetal | Low | Medium | Already handled by existing composite mode; no new risk |
| R4 | Remote protocol design complexity causes scope creep | High | Medium | Strict TODO boundary -- design interface only, no implementation |
| R5 | In-process test execution crashes the runner | Medium | High | Keep subprocess as default; in-process only for trusted code |
| R6 | `--all-modes` multiplies test time significantly | High | Low | Make it opt-in; document expected time multiplier (~3x) |

---

## 6. Related Work

### 6.1 Comparable Test Runners

| System | Multi-Mode Support | Entry Point | Mode Selection |
|--------|--------------------|-------------|----------------|
| **Cargo test (Rust)** | Native only (debug/release profiles) | `#[test]` attribute + harness | `--profile`, `--release` |
| **Go test** | Native only | `func TestXxx(t *testing.T)` | Build flags |
| **Jest (JS)** | V8 only (can swap transformers) | `test()` / `describe()` | `--config` |
| **pytest (Python)** | Interpreter only | `def test_xxx()` | Plugins for remote |
| **Zig test** | Native + cross-compile + QEMU | `test "name" {}` | `-target`, `--test-cmd` |

Zig's test runner is the closest analogue: it supports cross-compilation to bare-metal targets and uses QEMU for execution, similar to Simple's composite mode. Zig's `--test-cmd` flag allows specifying an external command to run the test binary, which is analogous to the proposed `--mode` flag.

### 6.2 Internal References

- `doc/requirement/multi_mode_test_runner.md` -- Requirements specification (cross-reference)
- `doc/research/testing_infrastructure_comprehensive_2026.md` -- Broader testing infrastructure analysis
- `doc/research/execution_strategy_comparison.md` -- Execution strategy trade-offs
- `doc/research/fuzzing_mutation_testing_2026.md` -- Advanced testing techniques
- `doc/research/sandbox_implementation_strategies.md` -- Sandboxed execution for safe mode

---

## 7. Summary of Recommendations

| Priority | Recommendation | Effort | Impact |
|----------|---------------|--------|--------|
| **P0** | Create `test_main()` universal entry point | Medium | High -- enables all other improvements |
| **P0** | Add `--mode` CLI flag | Low | Medium -- user-facing mode selection |
| **P1** | Generate native test binaries with `test_main()` | Medium | High -- completes native mode |
| **P1** | Expose `test_main` as SMF export | Medium | Medium -- completes SMF mode |
| **P2** | Add `--all-modes` cross-validation flag | Low | Medium -- quality assurance |
| **P2** | Add `init_fn` callback support | Low | Low -- extensibility |
| **P3** | Design remote target protocol interface | Low | Low -- future-proofing |
| **P3** | Structured result channel (JSON-on-stderr) | Medium | Medium -- tooling integration |

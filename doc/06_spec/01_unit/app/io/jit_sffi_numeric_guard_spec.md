# Jit Sffi Numeric Guard Specification

> Tests covering jit sffi numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Sffi Numeric Guard Specification

## Scenarios

### jit sffi numeric guard

#### guards integer execution output parsing

- guards integer execution output parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guards integer execution output parsing")
val source = read_file_text("src/app/io/jit_sffi.spl")

expect(source).to_contain("val parsed = out.to_int()")
expect(source).to_contain("if parsed == nil:")
expect(source).to_contain("return (false, 0, \"Execution returned non-integer output\")")
expect(source).to_contain("(true, parsed, \"\")")
expect_not(source.contains("val error = rt_exec_manager_get_last_error"))
```

</details>

#### uses canonical runtime ABI names

- uses canonical runtime ABI names


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses canonical runtime ABI names")
val jit_source = read_file_text("src/app/io/jit_sffi.spl")
val io_source = read_file_text("src/app/io/mod.spl")
val cuda_source = read_file_text("src/lib/nogc_sync_mut/io/cuda_sffi.spl")

expect(jit_source).to_contain("use std.io_runtime.")
expect(jit_source).to_contain("file_write")
expect(jit_source).to_contain("file_write(fpath, content)")
expect_not(jit_source.contains("rt_file_write("))
expect(io_source).to_contain("extern fn rt_volatile_read_u64(addr: i64) -> i64")
expect_not(io_source.contains("rt_read_volatile_i64"))
expect(io_source).to_contain("extern fn rt_volatile_write_u64(addr: i64, value: i64)")
expect_not(io_source.contains("rt_write_volatile_i64"))
expect(cuda_source).to_contain("extern fn rt_cuda_mem_alloc(size: i64) -> i64")
expect(cuda_source).to_contain("extern fn rt_cuda_mem_free(ptr: i64) -> i64")
expect(cuda_source).to_contain("rt_cuda_mem_free(mem.ptr) == 0")
expect_not(cuda_source.contains("rt_cuda_malloc"))
expect_not(cuda_source.contains("rt_cuda_free"))

val closure_source = read_file_text("src/app/io/jit_ffi.spl") +
    read_file_text("src/app/io/feature_registry.spl") +
    read_file_text("src/os/ml/model.spl") +
    read_file_text("src/os/ml/gpu_tensor.spl") +
    read_file_text("src/lib/nogc_async_mut/engine/physics/backend_gpu/gpu_solver.spl") +
    read_file_text("src/lib/nogc_sync_mut/fuzz.spl")
expect_not(closure_source.contains("extern fn rt_file_write("))
expect_not(closure_source.contains("rt_cuda_malloc"))
expect_not(closure_source.contains("rt_cuda_free"))
```

</details>

#### reports only capabilities implemented by the soft manager

- reports only capabilities implemented by the soft manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports only capabilities implemented by the soft manager")
val source = read_file_text("src/app/io/jit_sffi.spl")

expect(source).to_contain("backend == \"auto\" or backend == \"interpreter\"")
expect(source).to_contain("if backend != \"auto\" and backend != \"interpreter\":")
expect(source).to_contain("if handle > 0: \"interpreter\" else: \"unknown\"")
expect(source).to_contain("handle > 0 and level == 0")
expect_not(source.contains("true  # accepted; actual backend is interpreted"))
expect_not(source.contains("true  # accept but ignore"))
```

</details>

#### keeps empty string distinct from string execution failure

- keeps empty string distinct from string execution failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps empty string distinct from string execution failure")
val source = read_file_text("src/app/io/jit_sffi.spl")

expect(source).to_contain("fn exec_manager_call_string(manager: ExecManager, function_name: text, args: [text]) -> Result<text, text>:")
expect(source).to_contain("return Err(\"No compiled source\")")
expect(source).to_contain("return Err(\"Execution failed\")")
expect(source).to_contain("Ok(out)")
expect_not(source.contains("fn rt_exec_manager_execute_string"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/jit_sffi_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering jit sffi numeric guard.
- jit sffi numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8aed37956f2bca4c7d500f99594b0eec061f2106f4a2097ad437ad0275ee12fe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8aed37956f2bca4c7d500f99594b0eec061f2106f4a2097ad437ad0275ee12fe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8aed37956f2bca4c7d500f99594b0eec061f2106f4a2097ad437ad0275ee12fe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/io/jit_sffi_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/io/jit_sffi_numeric_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/jit_sffi_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/jit_sffi_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/jit_sffi_numeric_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards integer execution output parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/jit_sffi_numeric_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses canonical runtime ABI names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/jit_sffi_numeric_guard_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports only capabilities implemented by the soft manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

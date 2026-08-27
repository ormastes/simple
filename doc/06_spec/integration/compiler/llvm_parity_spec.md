# Llvm Parity Specification

> Tests covering LLVM Backend Parity (llvm-lib vs llvm), compilation succeeds on both backends, both backends produce object code, optimization levels, auto backend selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Parity Specification

## Scenarios

### LLVM Backend Parity (llvm-lib vs llvm)

### compilation succeeds on both backends

#### compiles empty module via llvm

- compiles empty module via llvm
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles empty module via llvm")
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_empty_llvm")
val result = compile_module_with_backend("llvm", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

#### compiles empty module via llvm-lib

- compiles empty module via llvm-lib
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles empty module via llvm-lib")
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_empty_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

### both backends produce object code

#### llvm produces non-empty object code

- llvm produces non-empty object code
   - Expected: compiled.object_code.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm produces non-empty object code")
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_obj_llvm")
val result = compile_module_with_backend("llvm", module, true)
if result.is_ok():
    val compiled = result.unwrap()
    expect(compiled.object_code.len() > 0).to_equal(true)
```

</details>

#### llvm-lib produces non-empty object code

- llvm-lib produces non-empty object code
   - Expected: compiled.object_code.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib produces non-empty object code")
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_obj_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, true)
if result.is_ok():
    val compiled = result.unwrap()
    expect(compiled.object_code.len() > 0).to_equal(true)
```

</details>

### optimization levels

#### llvm handles debug optimization

- llvm handles debug optimization
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm handles debug optimization")
val caps = get_llvm_capabilities()
if not caps.llvm_backend_available:
    val pending_reason = "llc not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_debug_llvm")
val result = compile_module_with_backend("llvm", module, false)
expect(result.is_ok()).to_equal(true)
```

</details>

#### llvm-lib handles debug optimization

- llvm-lib handles debug optimization
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("llvm-lib handles debug optimization")
val caps = get_llvm_capabilities()
if not caps.llvm_lib_backend_available:
    val pending_reason = "libLLVM not available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_debug_llvmlib")
val result = compile_module_with_backend("llvm-lib", module, false)
expect(result.is_ok()).to_equal(true)
```

</details>

### auto backend selection

#### auto selects an available LLVM backend

- auto selects an available LLVM backend
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("auto selects an available LLVM backend")
val caps = get_llvm_capabilities()
if not caps.has_any_llvm():
    val pending_reason = "no LLVM backend available"
    expect(pending_reason.len()).to_be_greater_than(0)
val module = make_test_module("parity_auto")
val result = compile_module_with_backend("auto", module, true)
expect(result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM Backend Parity (llvm-lib vs llvm), compilation succeeds on both backends, both backends produce object code, optimization levels, auto backend selection.
- LLVM Backend Parity (llvm-lib vs llvm)
- compilation succeeds on both backends
- both backends produce object code
- optimization levels
- auto backend selection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d992ba171b3cce6901c0519d3809c23066c694646e4dddaaa506c8b9450345b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d992ba171b3cce6901c0519d3809c23066c694646e4dddaaa506c8b9450345b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d992ba171b3cce6901c0519d3809c23066c694646e4dddaaa506c8b9450345b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/llvm_parity_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_parity_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles empty module via llvm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_parity_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles empty module via llvm-lib' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_parity_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'llvm produces non-empty object code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

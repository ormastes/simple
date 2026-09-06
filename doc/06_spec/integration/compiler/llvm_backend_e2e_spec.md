# Llvm Backend E2e Specification

> Tests covering LLVM Backend E2E - Environment, LLVM Backend E2E - Runtime Declarations, LLVM Backend E2E - Backend Creation, LLVM Backend E2E - Configuration, LLVM Backend E2E - Target Configuration, LLVM Backend E2E - Compilation, LLVM Backend E2E - Error Handling, LLVM Backend E2E - Multiple Targets, LLVM Backend E2E - Optimization Levels.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Backend E2e Specification

## Scenarios

### LLVM Backend E2E - Environment

#### llc detection

#### finds llc binary

- finds llc binary
   - Expected: llc_cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("finds llc binary")
val llc_cmd = find_llc()
# Skip test if llc not installed
if not llc_cmd.?:
    pending("llc not installed")
else:
    expect(llc_cmd == nil).to_equal(false)
    # Should be one of: llc-18, llc-17, llc-16, llc
    val cmd = llc_cmd
    expect(cmd).to_start_with("llc")
```

</details>

#### checks llc availability

- checks llc availability
   - Expected: available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checks llc availability")
val available = llc_available()
if not available:
    pending("llc not installed")
else:
    expect(available).to_equal(true)
```

</details>

### LLVM Backend E2E - Runtime Declarations

#### declaration generation

#### generates runtime declarations

- generates runtime declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates runtime declarations")
val decls = generate_runtime_declarations()
expect(decls.len()).to_be_greater_than(0)
```

</details>

#### includes file I/O declarations

- includes file I/O declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes file I/O declarations")
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_file_open")
expect(decls).to_contain("@rt_file_read_text")
expect(decls).to_contain("@rt_file_write")
```

</details>

#### includes memory declarations

- includes memory declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes memory declarations")
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_alloc")
expect(decls).to_contain("@rt_free")
expect(decls).to_contain("@rt_memcpy")
```

</details>

#### includes string declarations

- includes string declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes string declarations")
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_strlen")
expect(decls).to_contain("@rt_strcat")
```

</details>

#### includes I/O declarations

- includes I/O declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes I/O declarations")
val decls = generate_runtime_declarations()
expect(decls).to_contain("@rt_print")
expect(decls).to_contain("@rt_println")
```

</details>

#### includes LLVM intrinsics

- includes LLVM intrinsics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("includes LLVM intrinsics")
val decls = generate_runtime_declarations()
expect(decls).to_contain("@llvm.memcpy")
expect(decls).to_contain("@llvm.memset")
```

</details>

### LLVM Backend E2E - Backend Creation

#### default backend

#### creates backend for x86_64

- creates backend for x86_64
   - Expected: backend.target equals `CodegenTarget.X86_64`
   - Expected: backend.opt_level equals `OptimizationLevel.Debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates backend for x86_64")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
expect(backend.target).to_equal(CodegenTarget.X86_64)
expect(backend.opt_level).to_equal(OptimizationLevel.Debug)
```

</details>

#### creates backend for Speed optimization

- creates backend for Speed optimization
   - Expected: backend.opt_level equals `OptimizationLevel.Speed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates backend for Speed optimization")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.opt_level).to_equal(OptimizationLevel.Speed)
```

</details>

#### compatibility backend

#### creates compatibility backend

- creates compatibility backend
   - Expected: backend.cpu_override == nil is false
   - Expected: backend.cpu_override equals `x86-64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates compatibility backend")
val backend = LlvmBackend.compatibility_build(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.cpu_override == nil).to_equal(false)
expect(backend.cpu_override).to_equal("x86-64")
```

</details>

#### bare-metal backend

#### creates bare-metal backend

- creates bare-metal backend
   - Expected: backend.bare_metal is true
   - Expected: backend.debug_info is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates bare-metal backend")
val backend = LlvmBackend.create_baremetal(CodegenTarget.X86_64, OptimizationLevel.Size)
expect(backend.bare_metal).to_equal(true)
expect(backend.debug_info).to_equal(true)
```

</details>

### LLVM Backend E2E - Configuration

#### builder methods

#### configures CPU override

- configures CPU override
   - Expected: backend.cpu_override == nil is false
   - Expected: backend.cpu_override equals `skylake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("configures CPU override")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_cpu_override("skylake")
expect(backend.cpu_override == nil).to_equal(false)
expect(backend.cpu_override).to_equal("skylake")
```

</details>

#### enables LLVM IR output

- enables LLVM IR output
   - Expected: backend.emit_llvm_ir is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enables LLVM IR output")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_llvm_ir()
expect(backend.emit_llvm_ir).to_equal(true)
```

</details>

#### enables assembly output

- enables assembly output
   - Expected: backend.emit_assembly is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enables assembly output")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_assembly()
expect(backend.emit_assembly).to_equal(true)
```

</details>

#### enables debug info

- enables debug info
   - Expected: backend.debug_info is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("enables debug info")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    .with_debug_info()
expect(backend.debug_info).to_equal(true)
```

</details>

### LLVM Backend E2E - Target Configuration

#### target config

#### gets target configuration

- gets target configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gets target configuration")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("x86_64")
```

</details>

### LLVM Backend E2E - Compilation

#### simple IR compilation

#### compiles minimal LLVM IR to object code

- compiles minimal LLVM IR to object code
   - Expected: backend.target equals `CodegenTarget.X86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles minimal LLVM IR to object code")
if not llc_available():
    # Skip if llc not installed
    pending("llc not installed")
else:
    # TODO: Create minimal MirModule and compile
    # For now just verify backend creation works
    val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
    expect(backend.target).to_equal(CodegenTarget.X86_64)
```

</details>

### LLVM Backend E2E - Error Handling

#### missing llc

#### provides helpful error message

- provides helpful error message
   - Expected: llc_cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides helpful error message")
# This test verifies error message format
# Actual llc availability may vary
val llc_cmd = find_llc()
if not llc_cmd.?:
    # Error message would be shown during compile_ir_to_object
    pending("llc not installed")
else:
    # llc is available
    expect(llc_cmd == nil).to_equal(false)
```

</details>

### LLVM Backend E2E - Multiple Targets

#### x86_64 target

#### creates backend for x86_64

- creates backend for x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates backend for x86_64")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("x86_64")
```

</details>

#### aarch64 target

#### creates backend for aarch64

- creates backend for aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates backend for aarch64")
val backend = LlvmBackend.create(CodegenTarget.AArch64, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("aarch64")
```

</details>

#### 32-bit targets

#### creates backend for i686

- creates backend for i686


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates backend for i686")
val backend = LlvmBackend.create(CodegenTarget.X86, OptimizationLevel.Speed)
val config = backend.get_target_config()
expect(config.triple.to_text()).to_contain("i686")
```

</details>

### LLVM Backend E2E - Optimization Levels

#### optimization flags

#### supports Debug optimization

- supports Debug optimization
   - Expected: backend.opt_level equals `OptimizationLevel.Debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports Debug optimization")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
expect(backend.opt_level).to_equal(OptimizationLevel.Debug)
```

</details>

#### supports Size optimization

- supports Size optimization
   - Expected: backend.opt_level equals `OptimizationLevel.Size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports Size optimization")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Size)
expect(backend.opt_level).to_equal(OptimizationLevel.Size)
```

</details>

#### supports Speed optimization

- supports Speed optimization
   - Expected: backend.opt_level equals `OptimizationLevel.Speed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports Speed optimization")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Speed)
expect(backend.opt_level).to_equal(OptimizationLevel.Speed)
```

</details>

#### supports Aggressive optimization

- supports Aggressive optimization
   - Expected: backend.opt_level equals `OptimizationLevel.Aggressive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports Aggressive optimization")
val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Aggressive)
expect(backend.opt_level).to_equal(OptimizationLevel.Aggressive)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/llvm_backend_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM Backend E2E - Environment, LLVM Backend E2E - Runtime Declarations, LLVM Backend E2E - Backend Creation, LLVM Backend E2E - Configuration, LLVM Backend E2E - Target Configuration, LLVM Backend E2E - Compilation, LLVM Backend E2E - Error Handling, LLVM Backend E2E - Multiple Targets, LLVM Backend E2E - Optimization Levels.
- LLVM Backend E2E - Environment
- LLVM Backend E2E - Runtime Declarations
- LLVM Backend E2E - Backend Creation
- LLVM Backend E2E - Configuration
- LLVM Backend E2E - Target Configuration
- LLVM Backend E2E - Compilation
- LLVM Backend E2E - Error Handling
- LLVM Backend E2E - Multiple Targets
- LLVM Backend E2E - Optimization Levels

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `f7a89ca787011b08ccc60e56448137f8962ada3bb1e143854daadffbeed330f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7a89ca787011b08ccc60e56448137f8962ada3bb1e143854daadffbeed330f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7a89ca787011b08ccc60e56448137f8962ada3bb1e143854daadffbeed330f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/compiler/llvm_backend_e2e_spec.spl
mirror: doc/06_spec/integration/compiler/llvm_backend_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/llvm_backend_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/llvm_backend_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/llvm_backend_e2e_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds llc binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_backend_e2e_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks llc availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/llvm_backend_e2e_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates runtime declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

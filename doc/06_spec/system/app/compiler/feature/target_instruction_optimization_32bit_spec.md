# Target Instruction Optimization 32bit Specification

> Tests covering Target instruction optimization and 32-bit support, REQ-TGT-001: target families, REQ-TGT-001b: target family enum and feature set, REQ-TGT-002: instruction family enable matrix, REQ-X86-001: x86_64 32-bit-form legality, REQ-TGT-003: optimization planner, REQ-TGT-004: unsupported feature rejection, REQ-PERF-001: x86_64 optimization non-regression, REQ-TGT-005: profitability rewrite gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Instruction Optimization 32bit Specification

## Scenarios

### Target instruction optimization and 32-bit support

### REQ-TGT-001: target families

#### should classify x86_64 triple

- should classify x86_64 triple
   - Expected: f equals `X86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TGT-001
# @req REQ-TGT-001b
# @req REQ-TGT-002
# @req REQ-X86-001
# @req REQ-TGT-003
# @req REQ-TGT-004
# @req REQ-PERF-001
# @req REQ-TGT-005
# @req REQ-SSPEC-SYSTEM
step("should classify x86_64 triple")
val f = target_family_from_triple("x86_64-unknown-linux-gnu")
expect(f).to_equal("X86_64")
```

</details>

#### should classify x86_32 triple via i686

- should classify x86_32 triple via i686
   - Expected: f equals `X86_32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify x86_32 triple via i686")
val f = target_family_from_triple("i686-unknown-linux-gnu")
expect(f).to_equal("X86_32")
```

</details>

#### should classify aarch64 triple

- should classify aarch64 triple
   - Expected: f equals `Aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify aarch64 triple")
val f = target_family_from_triple("aarch64-unknown-linux-gnu")
expect(f).to_equal("Aarch64")
```

</details>

#### should classify arm32 triple via armv7

- should classify arm32 triple via armv7
   - Expected: f equals `Arm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify arm32 triple via armv7")
val f = target_family_from_triple("armv7-unknown-linux-gnueabi")
expect(f).to_equal("Arm32")
```

</details>

#### should classify rv64 triple

- should classify rv64 triple
   - Expected: f equals `Rv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify rv64 triple")
val f = target_family_from_triple("riscv64gc-unknown-linux-gnu")
expect(f).to_equal("Rv64")
```

</details>

#### should classify rv32 triple

- should classify rv32 triple
   - Expected: f equals `Rv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify rv32 triple")
val f = target_family_from_triple("riscv32imac-unknown-none-elf")
expect(f).to_equal("Rv32")
```

</details>

#### should return Unknown for malformed triple

- should return Unknown for malformed triple
   - Expected: f equals `Unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return Unknown for malformed triple")
val f = target_family_from_triple("garbage-not-a-triple")
expect(f).to_equal("Unknown")
```

</details>

#### should return Unknown for empty triple

- should return Unknown for empty triple
   - Expected: f equals `Unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return Unknown for empty triple")
val f = target_family_from_triple("")
expect(f).to_equal("Unknown")
```

</details>

### REQ-TGT-001b: target family enum and feature set

#### should produce TargetFamily enum from triple

- should produce TargetFamily enum from triple
   - Expected: nm equals `X86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce TargetFamily enum from triple")
val fam = target_family_enum_from_triple("x86_64-unknown-linux-gnu")
val nm = target_family_name(fam)
expect(nm).to_equal("X86_64")
```

</details>

#### should build a TargetFeatureSet from triple and flags

- should build a TargetFeatureSet from triple and flags
   - Expected: fs.triple equals `x86_64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build a TargetFeatureSet from triple and flags")
var flags = ["avx2", "bmi2"]
val fs = target_feature_set_new("x86_64-unknown-linux-gnu", flags)
expect(fs.triple).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### should build a TargetFeatureSet with empty flags

- should build a TargetFeatureSet with empty flags
   - Expected: fs.triple equals `aarch64-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build a TargetFeatureSet with empty flags")
var empty_flags: [text] = []
val fs = target_feature_set_new("aarch64-unknown-linux-gnu", empty_flags)
expect(fs.triple).to_equal("aarch64-unknown-linux-gnu")
```

</details>

### REQ-TGT-002: instruction family enable matrix

#### should enable x86 narrow-form family on x86_64

- should enable x86 narrow-form family on x86_64
   - Expected: d.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enable x86 narrow-form family on x86_64")
var flags: [text] = []
val m = target_enable_matrix("x86_64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(true)
```

</details>

#### should disable unsupported rv vector family on rv32 without V extension

- should disable unsupported rv vector family on rv32 without V extension
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should disable unsupported rv vector family on rv32 without V extension")
var flags: [text] = []
val m = target_enable_matrix("riscv32imac-unknown-none-elf", flags)
val d = matrix_decision(m, "riscv.vector.v")
expect(d.enabled).to_equal(false)
expect(d.reason).to_contain("missing feature")
```

</details>

#### should disable x86-only families on aarch64

- should disable x86-only families on aarch64
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should disable x86-only families on aarch64")
var flags: [text] = []
val m = target_enable_matrix("aarch64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
expect(d.reason).to_contain("target")
```

</details>

#### should disable x86-only families on arm32

- should disable x86-only families on arm32
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should disable x86-only families on arm32")
var flags: [text] = []
val m = target_enable_matrix("armv7-unknown-linux-gnueabi", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

### REQ-X86-001: x86_64 32-bit-form legality

#### should allow 32-bit forms for proven narrow u32 values

- should allow 32-bit forms for proven narrow u32 values
   - Expected: p.result equals `legal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow 32-bit forms for proven narrow u32 values")
val p = prove_x86_64_narrow_form("u32_add_zero_extended")
expect(p.result).to_equal("legal")
```

</details>

#### should allow 32-bit forms for proven narrow i32 values

- should allow 32-bit forms for proven narrow i32 values
   - Expected: p.result equals `legal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow 32-bit forms for proven narrow i32 values")
val p = prove_x86_64_narrow_form("i32_mul_sign_extended")
expect(p.result).to_equal("legal")
```

</details>

#### should reject 32-bit forms for LP64 pointers

- should reject 32-bit forms for LP64 pointers
   - Expected: p.result equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject 32-bit forms for LP64 pointers")
val p = prove_x86_64_narrow_form("lp64_pointer_add")
expect(p.result).to_equal("rejected")
expect(p.reason).to_contain("pointer")
```

</details>

#### should reject 32-bit forms for unknown-width operands

- should reject 32-bit forms for unknown-width operands
   - Expected: p.result equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject 32-bit forms for unknown-width operands")
val p = prove_x86_64_narrow_form("unknown_width_op")
expect(p.result).to_equal("rejected")
expect(p.reason).to_contain("unknown")
```

</details>

### REQ-TGT-003: optimization planner

#### should produce a non-empty plan for x86_64

- should produce a non-empty plan for x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce a non-empty plan for x86_64")
var flags: [text] = []
val fs = target_feature_set_new("x86_64-unknown-linux-gnu", flags)
val m = target_enable_matrix("x86_64-unknown-linux-gnu", flags)
val plan = plan_target_optimizations(fs, m)
expect(plan.len()).to_be_greater_than(0)
```

</details>

#### should produce an empty plan for unknown triple

- should produce an empty plan for unknown triple
   - Expected: plan.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce an empty plan for unknown triple")
var flags: [text] = []
val fs = target_feature_set_new("garbage-not-a-triple", flags)
val m = target_enable_matrix("garbage-not-a-triple", flags)
val plan = plan_target_optimizations(fs, m)
expect(plan.len()).to_equal(0)
```

</details>

#### should include narrow_form in x86_64 plan

- should include narrow_form in x86_64 plan
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should include narrow_form in x86_64 plan")
var flags: [text] = []
val fs = target_feature_set_new("x86_64-unknown-linux-gnu", flags)
val m = target_enable_matrix("x86_64-unknown-linux-gnu", flags)
val plan = plan_target_optimizations(fs, m)
var found = false
var i = 0
while i < plan.len():
    if plan[i] == "x86.narrow_form":
        found = true
    i = i + 1
expect(found).to_equal(true)
```

</details>

### REQ-TGT-004: unsupported feature rejection

#### should reject x86 narrow-form on aarch64

- should reject x86 narrow-form on aarch64
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject x86 narrow-form on aarch64")
var flags: [text] = []
val m = target_enable_matrix("aarch64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

#### should reject x86 narrow-form on rv64

- should reject x86 narrow-form on rv64
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject x86 narrow-form on rv64")
var flags: [text] = []
val m = target_enable_matrix("riscv64gc-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

#### should reject x86 narrow-form on rv32

- should reject x86 narrow-form on rv32
   - Expected: d.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject x86 narrow-form on rv32")
var flags: [text] = []
val m = target_enable_matrix("riscv32imac-unknown-none-elf", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

### REQ-PERF-001: x86_64 optimization non-regression

#### should record baseline and optimized benchmark runs

- should record baseline and optimized benchmark runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record baseline and optimized benchmark runs")
val r = compare_target_optimization_benchmark("x86_64", "integer_loop")
expect(r.baseline_runs).to_be_greater_than(0)
expect(r.optimized_runs).to_be_greater_than(0)
```

</details>

#### should record benchmark for narrow-form kernel

- should record benchmark for narrow-form kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record benchmark for narrow-form kernel")
val r = compare_target_optimization_benchmark("x86_64", "narrow_form_arithmetic")
expect(r.baseline_runs).to_be_greater_than(0)
expect(r.optimized_runs).to_be_greater_than(0)
```

</details>

### REQ-TGT-005: profitability rewrite gate

#### should indicate rewrite is profitable for positive score

- should indicate rewrite is profitable for positive score
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should indicate rewrite is profitable for positive score")
val ok = should_rewrite(10)
expect(ok).to_equal(true)
```

</details>

#### should indicate rewrite is not profitable for non-positive score

- should indicate rewrite is not profitable for non-positive score
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should indicate rewrite is not profitable for non-positive score")
val ok = should_rewrite(0)
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Target instruction optimization and 32-bit support, REQ-TGT-001: target families, REQ-TGT-001b: target family enum and feature set, REQ-TGT-002: instruction family enable matrix, REQ-X86-001: x86_64 32-bit-form legality, REQ-TGT-003: optimization planner, REQ-TGT-004: unsupported feature rejection, REQ-PERF-001: x86_64 optimization non-regression, REQ-TGT-005: profitability rewrite gate.
- Target instruction optimization and 32-bit support
- REQ-TGT-001: target families
- REQ-TGT-001b: target family enum and feature set
- REQ-TGT-002: instruction family enable matrix
- REQ-X86-001: x86_64 32-bit-form legality
- REQ-TGT-003: optimization planner
- REQ-TGT-004: unsupported feature rejection
- REQ-PERF-001: x86_64 optimization non-regression
- REQ-TGT-005: profitability rewrite gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TGT-001`
- `REQ-TGT-001b`
- `REQ-TGT-002`
- `REQ-X86-001`
- `REQ-TGT-003`
- `REQ-TGT-004`
- `REQ-PERF-001`
- `REQ-TGT-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9ae64df6d200634d228100ee7651ec3e55be8d69c0597f567e0121af5b68f03c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ae64df6d200634d228100ee7651ec3e55be8d69c0597f567e0121af5b68f03c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ae64df6d200634d228100ee7651ec3e55be8d69c0597f567e0121af5b68f03c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/target_instruction_optimization_32bit_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/compiler/feature/target_instruction_optimization_32bit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/target_instruction_optimization_32bit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:15:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify x86_64 triple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify x86_64 triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify x86_32 triple via i686' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify x86_32 triple via i686' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify aarch64 triple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify aarch64 triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify arm32 triple via armv7' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify rv64 triple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify rv32 triple' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

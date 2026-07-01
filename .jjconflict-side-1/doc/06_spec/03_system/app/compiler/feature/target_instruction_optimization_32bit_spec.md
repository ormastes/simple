# Target Instruction Optimization 32bit Specification

> <details>

<!-- sdn-diagram:id=target_instruction_optimization_32bit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_instruction_optimization_32bit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_instruction_optimization_32bit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_instruction_optimization_32bit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("x86_64-unknown-linux-gnu")
expect(f).to_equal("X86_64")
```

</details>

#### should classify x86_32 triple via i686

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("i686-unknown-linux-gnu")
expect(f).to_equal("X86_32")
```

</details>

#### should classify aarch64 triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("aarch64-unknown-linux-gnu")
expect(f).to_equal("Aarch64")
```

</details>

#### should classify arm32 triple via armv7

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("armv7-unknown-linux-gnueabi")
expect(f).to_equal("Arm32")
```

</details>

#### should classify rv64 triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("riscv64gc-unknown-linux-gnu")
expect(f).to_equal("Rv64")
```

</details>

#### should classify rv32 triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("riscv32imac-unknown-none-elf")
expect(f).to_equal("Rv32")
```

</details>

#### should return Unknown for malformed triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("garbage-not-a-triple")
expect(f).to_equal("Unknown")
```

</details>

#### should return Unknown for empty triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = target_family_from_triple("")
expect(f).to_equal("Unknown")
```

</details>

### REQ-TGT-001b: target family enum and feature set

#### should produce TargetFamily enum from triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fam = target_family_enum_from_triple("x86_64-unknown-linux-gnu")
val nm = target_family_name(fam)
expect(nm).to_equal("X86_64")
```

</details>

#### should build a TargetFeatureSet from triple and flags

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags = ["avx2", "bmi2"]
val fs = target_feature_set_new("x86_64-unknown-linux-gnu", flags)
expect(fs.triple).to_equal("x86_64-unknown-linux-gnu")
```

</details>

#### should build a TargetFeatureSet with empty flags

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty_flags: [text] = []
val fs = target_feature_set_new("aarch64-unknown-linux-gnu", empty_flags)
expect(fs.triple).to_equal("aarch64-unknown-linux-gnu")
```

</details>

### REQ-TGT-002: instruction family enable matrix

#### should enable x86 narrow-form family on x86_64

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("x86_64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(true)
```

</details>

#### should disable unsupported rv vector family on rv32 without V extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("riscv32imac-unknown-none-elf", flags)
val d = matrix_decision(m, "riscv.vector.v")
expect(d.enabled).to_equal(false)
expect(d.reason).to_contain("missing feature")
```

</details>

#### should disable x86-only families on aarch64

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("aarch64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
expect(d.reason).to_contain("target")
```

</details>

#### should disable x86-only families on arm32

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("armv7-unknown-linux-gnueabi", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

### REQ-X86-001: x86_64 32-bit-form legality

#### should allow 32-bit forms for proven narrow u32 values

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = prove_x86_64_narrow_form("u32_add_zero_extended")
expect(p.result).to_equal("legal")
```

</details>

#### should allow 32-bit forms for proven narrow i32 values

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = prove_x86_64_narrow_form("i32_mul_sign_extended")
expect(p.result).to_equal("legal")
```

</details>

#### should reject 32-bit forms for LP64 pointers

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = prove_x86_64_narrow_form("lp64_pointer_add")
expect(p.result).to_equal("rejected")
expect(p.reason).to_contain("pointer")
```

</details>

#### should reject 32-bit forms for unknown-width operands

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = prove_x86_64_narrow_form("unknown_width_op")
expect(p.result).to_equal("rejected")
expect(p.reason).to_contain("unknown")
```

</details>

### REQ-TGT-003: optimization planner

#### should produce a non-empty plan for x86_64

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val fs = target_feature_set_new("x86_64-unknown-linux-gnu", flags)
val m = target_enable_matrix("x86_64-unknown-linux-gnu", flags)
val plan = plan_target_optimizations(fs, m)
expect(plan.len()).to_be_greater_than(0)
```

</details>

#### should produce an empty plan for unknown triple

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val fs = target_feature_set_new("garbage-not-a-triple", flags)
val m = target_enable_matrix("garbage-not-a-triple", flags)
val plan = plan_target_optimizations(fs, m)
expect(plan.len()).to_equal(0)
```

</details>

#### should include narrow_form in x86_64 plan

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("aarch64-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

#### should reject x86 narrow-form on rv64

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("riscv64gc-unknown-linux-gnu", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

#### should reject x86 narrow-form on rv32

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: [text] = []
val m = target_enable_matrix("riscv32imac-unknown-none-elf", flags)
val d = matrix_decision(m, "x86.narrow_form")
expect(d.enabled).to_equal(false)
```

</details>

### REQ-PERF-001: x86_64 optimization non-regression

#### should record baseline and optimized benchmark runs

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compare_target_optimization_benchmark("x86_64", "integer_loop")
expect(r.baseline_runs).to_be_greater_than(0)
expect(r.optimized_runs).to_be_greater_than(0)
```

</details>

#### should record benchmark for narrow-form kernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compare_target_optimization_benchmark("x86_64", "narrow_form_arithmetic")
expect(r.baseline_runs).to_be_greater_than(0)
expect(r.optimized_runs).to_be_greater_than(0)
```

</details>

### REQ-TGT-005: profitability rewrite gate

#### should indicate rewrite is profitable for positive score

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = should_rewrite(10)
expect(ok).to_equal(true)
```

</details>

#### should indicate rewrite is not profitable for non-positive score

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = should_rewrite(0)
expect(ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

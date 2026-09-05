# Backend Bench Matrix Specification

> Tests covering BenchMatrix — x86-64 narrow-form encoding size gate, BenchMatrix — x86-64-v3 cost table self-consistency, BenchMatrix — aarch64+crypto cost table self-consistency, BenchMatrix — rv64gcv_zvkn cost table self-consistency, BenchMatrix — arm32 neon+crypto cost table self-consistency, BenchMatrix — rv32 scalar crypto cost table self-consistency, BenchMatrix — cross-arch narrow-vs-wide gate summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Bench Matrix Specification

## Scenarios

### BenchMatrix — x86-64 narrow-form encoding size gate

#### r32 ADD is strictly smaller than r64 ADD

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- r32 ADD is strictly smaller than r64 ADD


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("r32 ADD is strictly smaller than r64 ADD")
expect(bench_add_r32_bytes()).to_be_less_than(bench_add_r64_bytes())
```

</details>

#### narrow gate passes for add+42 (legal + shorter)

- narrow gate passes for add+42 (legal + shorter)
   - Expected: bench_narrow_gate_passes("add", 42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow gate passes for add+42 (legal + shorter)")
expect(bench_narrow_gate_passes("add", 42)).to_equal(true)
```

</details>

#### narrow gate passes for xor+0 (legal + shorter)

- narrow gate passes for xor+0 (legal + shorter)
   - Expected: bench_narrow_gate_passes("xor", 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow gate passes for xor+0 (legal + shorter)")
expect(bench_narrow_gate_passes("xor", 0)).to_equal(true)
```

</details>

#### narrow gate rejects mul regardless of value (prohibited)

- narrow gate rejects mul regardless of value (prohibited)
   - Expected: bench_narrow_gate_passes("mul", 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow gate rejects mul regardless of value (prohibited)")
expect(bench_narrow_gate_passes("mul", 1)).to_equal(false)
```

</details>

#### narrow gate rejects add with huge value (value overflow)

- narrow gate rejects add with huge value (value overflow)
   - Expected: bench_narrow_gate_passes("add", 5000000000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow gate rejects add with huge value (value overflow)")
expect(bench_narrow_gate_passes("add", 5000000000)).to_equal(false)
```

</details>

#### narrow_form_is_same_or_shorter is reflexive (equal is ok)

- narrow_form_is_same_or_shorter is reflexive (equal is ok)
   - Expected: narrow_form_is_same_or_shorter(3, 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow_form_is_same_or_shorter is reflexive (equal is ok)")
expect(narrow_form_is_same_or_shorter(3, 3)).to_equal(true)
```

</details>

#### narrow_form_is_same_or_shorter rejects strictly larger narrow

- narrow_form_is_same_or_shorter rejects strictly larger narrow
   - Expected: narrow_form_is_same_or_shorter(3, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("narrow_form_is_same_or_shorter rejects strictly larger narrow")
expect(narrow_form_is_same_or_shorter(3, 5)).to_equal(false)
```

</details>

### BenchMatrix — x86-64-v3 cost table self-consistency

#### AesEnc cost is non-negative

- AesEnc cost is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc cost is non-negative")
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative

- RotateLeft cost is non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft cost is non-negative")
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 is unsupported on x86_64-v3 (cost sentinel)

- Sha512Rounds2 is unsupported on x86_64-v3 (cost sentinel)
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 is unsupported on x86_64-v3 (cost sentinel)")
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — aarch64+crypto cost table self-consistency

#### AesEnc cost is non-negative on aarch64+crypto

- AesEnc cost is non-negative on aarch64+crypto


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc cost is non-negative on aarch64+crypto")
val caps = aarch64_caps_from_target("aarch64+crypto")
val cost = aarch64_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 cost is non-negative on armv8.4-A+crypto+sha3

- Sha512Rounds2 cost is non-negative on armv8.4-A+crypto+sha3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 cost is non-negative on armv8.4-A+crypto+sha3")
val caps = aarch64_caps_from_target("armv8.4-A+crypto+sha3")
val cost = aarch64_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### AesEnc unsupported on bare aarch64 baseline

- AesEnc unsupported on bare aarch64 baseline
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc unsupported on bare aarch64 baseline")
val caps = aarch64_caps_from_target("aarch64")
val cost = aarch64_instruction_cost(caps, TargetIdiom.AesEnc)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — rv64gcv_zvkn cost table self-consistency

#### AesEnc cost is non-negative on rv64gcv_zvkn

- AesEnc cost is non-negative on rv64gcv_zvkn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc cost is non-negative on rv64gcv_zvkn")
val caps = rv64_caps_from_target("rv64gcv_zvkn")
val cost = rv64_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative with Zbb

- RotateLeft cost is non-negative with Zbb


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft cost is non-negative with Zbb")
val caps = rv64_caps_from_target("rv64gc_zbb")
val cost = rv64_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### CRC32 is unsupported on RV64 (always)

- CRC32 is unsupported on RV64 (always)
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32 is unsupported on RV64 (always)")
val caps = rv64_caps_from_target("rv64gcv_zvkn")
val cost = rv64_instruction_cost(caps, TargetIdiom.Crc32U32)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — arm32 neon+crypto cost table self-consistency

#### AesEnc cost is non-negative with AES extension

- AesEnc cost is non-negative with AES extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc cost is non-negative with AES extension")
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative on ARM32

- RotateLeft cost is non-negative on ARM32


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft cost is non-negative on ARM32")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val cost = arm_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 is unsupported on any ARM32 target

- Sha512Rounds2 is unsupported on any ARM32 target
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 is unsupported on any ARM32 target")
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

#### SimdI32x8 is unsupported on ARM32

- SimdI32x8 is unsupported on ARM32
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x8 is unsupported on ARM32")
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.SimdI32x8)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — rv32 scalar crypto cost table self-consistency

#### AesEnc cost is non-negative with Zkne

- AesEnc cost is non-negative with Zkne


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc cost is non-negative with Zkne")
val caps = rv32_caps_from_target("riscv32imac_zkne")
val cost = rv32_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative with Zbb

- RotateLeft cost is non-negative with Zbb


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft cost is non-negative with Zbb")
val caps = rv32_caps_from_target("riscv32imac_zbb")
val cost = rv32_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512 is unsupported on RV32 (64-bit ops unavailable)

- Sha512 is unsupported on RV32 (64-bit ops unavailable)
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512 is unsupported on RV32 (64-bit ops unavailable)")
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
val cost = rv32_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

#### CRC32 is always unsupported on RV32

- CRC32 is always unsupported on RV32
   - Expected: cost.latency equals `unsupported.latency`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32 is always unsupported on RV32")
val caps = rv32_caps_from_target("riscv32imac")
val cost = rv32_instruction_cost(caps, TargetIdiom.Crc32U32)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — cross-arch narrow-vs-wide gate summary

#### x86-64 narrow ADD is strictly shorter (2 bytes vs 4 bytes proxy)

- x86-64 narrow ADD is strictly shorter (2 bytes vs 4 bytes proxy)
   - Expected: narrow_form_is_same_or_shorter(wide, narrow) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86-64 narrow ADD is strictly shorter (2 bytes vs 4 bytes proxy)")
val narrow = bench_add_r32_bytes()
val wide = bench_add_r64_bytes()
expect(narrow_form_is_same_or_shorter(wide, narrow)).to_equal(true)
```

</details>

#### benchmark gate passes for all approved ops with values fitting in 32 bits

- benchmark gate passes for all approved ops with values fitting in 32 bits
   - Expected: bench_narrow_gate_passes("sub",  1000) is true
   - Expected: bench_narrow_gate_passes("and",  0xFF) is true
   - Expected: bench_narrow_gate_passes("or",   0x0F) is true
   - Expected: bench_narrow_gate_passes("xor",  0xAB) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("benchmark gate passes for all approved ops with values fitting in 32 bits")
expect(bench_narrow_gate_passes("sub",  1000)).to_equal(true)
expect(bench_narrow_gate_passes("and",  0xFF)).to_equal(true)
expect(bench_narrow_gate_passes("or",   0x0F)).to_equal(true)
expect(bench_narrow_gate_passes("xor",  0xAB)).to_equal(true)
```

</details>

#### benchmark gate rejects all prohibited ops

- benchmark gate rejects all prohibited ops
   - Expected: bench_narrow_gate_passes("div",     1) is false
   - Expected: bench_narrow_gate_passes("idiv",    1) is false
   - Expected: bench_narrow_gate_passes("syscall", 0) is false
   - Expected: bench_narrow_gate_passes("rdtsc",   0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("benchmark gate rejects all prohibited ops")
expect(bench_narrow_gate_passes("div",     1)).to_equal(false)
expect(bench_narrow_gate_passes("idiv",    1)).to_equal(false)
expect(bench_narrow_gate_passes("syscall", 0)).to_equal(false)
expect(bench_narrow_gate_passes("rdtsc",   0)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/backend_bench_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BenchMatrix — x86-64 narrow-form encoding size gate, BenchMatrix — x86-64-v3 cost table self-consistency, BenchMatrix — aarch64+crypto cost table self-consistency, BenchMatrix — rv64gcv_zvkn cost table self-consistency, BenchMatrix — arm32 neon+crypto cost table self-consistency, BenchMatrix — rv32 scalar crypto cost table self-consistency, BenchMatrix — cross-arch narrow-vs-wide gate summary.
- BenchMatrix — x86-64 narrow-form encoding size gate
- BenchMatrix — x86-64-v3 cost table self-consistency
- BenchMatrix — aarch64+crypto cost table self-consistency
- BenchMatrix — rv64gcv_zvkn cost table self-consistency
- BenchMatrix — arm32 neon+crypto cost table self-consistency
- BenchMatrix — rv32 scalar crypto cost table self-consistency
- BenchMatrix — cross-arch narrow-vs-wide gate summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `2de926355a16f11992aa039566968d02cf618128e813c446529f0c961a79a6c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2de926355a16f11992aa039566968d02cf618128e813c446529f0c961a79a6c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2de926355a16f11992aa039566968d02cf618128e813c446529f0c961a79a6c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/backend/backend_bench_matrix_spec.spl
mirror: doc/06_spec/unit/compiler/backend/backend_bench_matrix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/backend_bench_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/backend_bench_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/backend_bench_matrix_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'r32 ADD is strictly smaller than r64 ADD' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_bench_matrix_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrow gate passes for add+42 (legal + shorter)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_bench_matrix_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'narrow gate passes for xor+0 (legal + shorter)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

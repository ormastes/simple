# Backend Bench Matrix Specification

> <details>

<!-- sdn-diagram:id=backend_bench_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_bench_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_bench_matrix_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_bench_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Bench Matrix Specification

## Scenarios

### BenchMatrix — x86-64 narrow-form encoding size gate

#### r32 ADD is strictly smaller than r64 ADD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_add_r32_bytes()).to_be_less_than(bench_add_r64_bytes())
```

</details>

#### narrow gate passes for add+42 (legal + shorter)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("add", 42)).to_equal(true)
```

</details>

#### narrow gate passes for xor+0 (legal + shorter)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("xor", 0)).to_equal(true)
```

</details>

#### narrow gate rejects mul regardless of value (prohibited)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("mul", 1)).to_equal(false)
```

</details>

#### narrow gate rejects add with huge value (value overflow)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("add", 5000000000)).to_equal(false)
```

</details>

#### narrow_form_is_same_or_shorter is reflexive (equal is ok)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(narrow_form_is_same_or_shorter(3, 3)).to_equal(true)
```

</details>

#### narrow_form_is_same_or_shorter rejects strictly larger narrow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(narrow_form_is_same_or_shorter(3, 5)).to_equal(false)
```

</details>

### BenchMatrix — x86-64-v3 cost table self-consistency

#### AesEnc cost is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 is unsupported on x86_64-v3 (cost sentinel)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
val cost = x86_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — aarch64+crypto cost table self-consistency

#### AesEnc cost is non-negative on aarch64+crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = aarch64_caps_from_target("aarch64+crypto")
val cost = aarch64_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 cost is non-negative on armv8.4-A+crypto+sha3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = aarch64_caps_from_target("armv8.4-A+crypto+sha3")
val cost = aarch64_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### AesEnc unsupported on bare aarch64 baseline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = aarch64_caps_from_target("aarch64")
val cost = aarch64_instruction_cost(caps, TargetIdiom.AesEnc)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — rv64gcv_zvkn cost table self-consistency

#### AesEnc cost is non-negative on rv64gcv_zvkn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gcv_zvkn")
val cost = rv64_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative with Zbb

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gc_zbb")
val cost = rv64_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### CRC32 is unsupported on RV64 (always)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gcv_zvkn")
val cost = rv64_instruction_cost(caps, TargetIdiom.Crc32U32)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — arm32 neon+crypto cost table self-consistency

#### AesEnc cost is non-negative with AES extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val cost = arm_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512Rounds2 is unsupported on any ARM32 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

#### SimdI32x8 is unsupported on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val cost = arm_instruction_cost(caps, TargetIdiom.SimdI32x8)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — rv32 scalar crypto cost table self-consistency

#### AesEnc cost is non-negative with Zkne

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zkne")
val cost = rv32_instruction_cost(caps, TargetIdiom.AesEnc)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### RotateLeft cost is non-negative with Zbb

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
val cost = rv32_instruction_cost(caps, TargetIdiom.RotateLeft)
expect(cost.latency).to_be_greater_than(0)
```

</details>

#### Sha512 is unsupported on RV32 (64-bit ops unavailable)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
val cost = rv32_instruction_cost(caps, TargetIdiom.Sha512Rounds2)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

#### CRC32 is always unsupported on RV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
val cost = rv32_instruction_cost(caps, TargetIdiom.Crc32U32)
val unsupported = instruction_cost_unsupported()
expect(cost.latency).to_equal(unsupported.latency)
```

</details>

### BenchMatrix — cross-arch narrow-vs-wide gate summary

#### x86-64 narrow ADD is strictly shorter (2 bytes vs 4 bytes proxy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val narrow = bench_add_r32_bytes()
val wide = bench_add_r64_bytes()
expect(narrow_form_is_same_or_shorter(wide, narrow)).to_equal(true)
```

</details>

#### benchmark gate passes for all approved ops with values fitting in 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bench_narrow_gate_passes("sub",  1000)).to_equal(true)
expect(bench_narrow_gate_passes("and",  0xFF)).to_equal(true)
expect(bench_narrow_gate_passes("or",   0x0F)).to_equal(true)
expect(bench_narrow_gate_passes("xor",  0xAB)).to_equal(true)
```

</details>

#### benchmark gate rejects all prohibited ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/backend/backend_bench_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

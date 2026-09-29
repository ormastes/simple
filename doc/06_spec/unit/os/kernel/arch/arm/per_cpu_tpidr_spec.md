# Per Cpu Tpidr Specification

> Tests covering AArch64 Per-CPU TPIDR_EL1 Register Convention, TPIDR_EL1 write at boot — baremetal path, TPIDR_EL1 NOT written in hosted (non-baremetal) build, TPIDR_EL0 — userspace thread pointer simulation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Cpu Tpidr Specification

## Scenarios

### AArch64 Per-CPU TPIDR_EL1 Register Convention

### TPIDR_EL1 write at boot — baremetal path

#### AC: TPIDR_EL1 is set to per_cpu_base + core_id * per_cpu_slot_size for core 0

- AC: TPIDR_EL1 is set to per_cpu_base + core_id * per_cpu_slot_size for core 0
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: TPIDR_EL1 is set to per_cpu_base + core_id * per_cpu_slot_size for core 0")
val core_id = 0u32
val per_cpu_base = 0x81000000u64
val per_cpu_shift = 12u32
simulate_tpidr_el1_write_baremetal(core_id, per_cpu_base, per_cpu_shift)
val tpidr_value = read_tpidr_el1_test()
val expected = per_cpu_base + (0u64 << per_cpu_shift)
expect(tpidr_value).to_equal(expected)
```

</details>

#### AC: TPIDR_EL1 is set correctly for secondary core (core 1)

- AC: TPIDR_EL1 is set correctly for secondary core (core 1)
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: TPIDR_EL1 is set correctly for secondary core (core 1)")
val core_id = 1u32
val per_cpu_base = 0x81000000u64
val per_cpu_shift = 12u32
simulate_tpidr_el1_write_baremetal(core_id, per_cpu_base, per_cpu_shift)
val tpidr_value = read_tpidr_el1_test()
val expected = per_cpu_base + (1u64 << per_cpu_shift)
expect(tpidr_value).to_equal(expected)
```

</details>

#### AC: TPIDR_EL1 differs across core IDs — no aliasing

- AC: TPIDR_EL1 differs across core IDs — no aliasing
   - Expected: tpidr_core0 equals `base`
   - Expected: tpidr_core1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: TPIDR_EL1 differs across core IDs — no aliasing")
val base = 0x81000000u64
val shift = 12u32
simulate_tpidr_el1_write_baremetal(0u32, base, shift)
val tpidr_core0 = read_tpidr_el1_test()
simulate_tpidr_el1_write_baremetal(1u32, base, shift)
val tpidr_core1 = read_tpidr_el1_test()
expect(tpidr_core0).to_equal(base)
expect(tpidr_core1).to_equal(base + 4096u64)
```

</details>

#### AC: shift=0 gives per_cpu_base + core_id (one-byte stride)

- AC: shift=0 gives per_cpu_base + core_id (one-byte stride)
   - Expected: tpidr_value equals `base + 3u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: shift=0 gives per_cpu_base + core_id (one-byte stride)")
val base = 0xC0000000u64
simulate_tpidr_el1_write_baremetal(3u32, base, 0u32)
val tpidr_value = read_tpidr_el1_test()
expect(tpidr_value).to_equal(base + 3u64)
```

</details>

#### AC: large shift (16) produces 64 KiB per-CPU slots

- AC: large shift (16) produces 64 KiB per-CPU slots
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: large shift (16) produces 64 KiB per-CPU slots")
val base = 0x80000000u64
val shift = 16u32
simulate_tpidr_el1_write_baremetal(2u32, base, shift)
val tpidr_value = read_tpidr_el1_test()
val expected = base + (2u64 << 16u64)
expect(tpidr_value).to_equal(expected)
```

</details>

### TPIDR_EL1 NOT written in hosted (non-baremetal) build

#### AC: simulate_tpidr_write_hosted does NOT modify TPIDR_EL1

- AC: simulate_tpidr_write_hosted does NOT modify TPIDR_EL1
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: simulate_tpidr_write_hosted does NOT modify TPIDR_EL1")
simulate_tpidr_el1_write_baremetal(0u32, 0x81000000u64, 12u32)
val before = read_tpidr_el1_test()
simulate_tpidr_write_hosted()
val after = read_tpidr_el1_test()
expect(after).to_equal(before)
```

</details>

### TPIDR_EL0 — userspace thread pointer simulation

#### AC: TPIDR_EL0 write stores the value independently from TPIDR_EL1

- AC: TPIDR_EL0 write stores the value independently from TPIDR_EL1
   - Expected: el0_value equals `0xDEADBEEF00000000u64`
   - Expected: el1_after equals `el1_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: TPIDR_EL0 write stores the value independently from TPIDR_EL1")
simulate_tpidr_el1_write_baremetal(0u32, 0x81000000u64, 12u32)
val el1_before = read_tpidr_el1_test()
simulate_tpidr_el0_write(0xDEADBEEF00000000u64)
val el0_value = read_tpidr_el0_test()
val el1_after = read_tpidr_el1_test()
expect(el0_value).to_equal(0xDEADBEEF00000000u64)
expect(el1_after).to_equal(el1_before)
```

</details>

#### AC: TPIDR_EL0 can be updated independently (thread migration simulation)

- AC: TPIDR_EL0 can be updated independently (thread migration simulation)
   - Expected: first equals `0x1000u64`
   - Expected: second equals `0x2000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC: TPIDR_EL0 can be updated independently (thread migration simulation)")
simulate_tpidr_el0_write(0x1000u64)
val first = read_tpidr_el0_test()
simulate_tpidr_el0_write(0x2000u64)
val second = read_tpidr_el0_test()
expect(first).to_equal(0x1000u64)
expect(second).to_equal(0x2000u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AArch64 Per-CPU TPIDR_EL1 Register Convention, TPIDR_EL1 write at boot — baremetal path, TPIDR_EL1 NOT written in hosted (non-baremetal) build, TPIDR_EL0 — userspace thread pointer simulation.
- AArch64 Per-CPU TPIDR_EL1 Register Convention
- TPIDR_EL1 write at boot — baremetal path
- TPIDR_EL1 NOT written in hosted (non-baremetal) build
- TPIDR_EL0 — userspace thread pointer simulation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `e788da6a2769ae48dc11513110097d0b1f123764e31431cef8b2a4201af24dfc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e788da6a2769ae48dc11513110097d0b1f123764e31431cef8b2a4201af24dfc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e788da6a2769ae48dc11513110097d0b1f123764e31431cef8b2a4201af24dfc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC: TPIDR_EL1 is set to per_cpu_base + core_id * per_cpu_slot_size for core 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC: TPIDR_EL1 is set correctly for secondary core (core 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC: TPIDR_EL1 differs across core IDs — no aliasing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

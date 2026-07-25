# Per Cpu Tpidr Specification

> 1. simulate tpidr el1 write baremetal

<!-- sdn-diagram:id=per_cpu_tpidr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=per_cpu_tpidr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

per_cpu_tpidr_spec -> std
per_cpu_tpidr_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=per_cpu_tpidr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. simulate tpidr el1 write baremetal
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. simulate tpidr el1 write baremetal
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. simulate tpidr el1 write baremetal
2. simulate tpidr el1 write baremetal
   - Expected: tpidr_core0 equals `base`
   - Expected: tpidr_core1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. simulate tpidr el1 write baremetal
   - Expected: tpidr_value equals `base + 3u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0xC0000000u64
simulate_tpidr_el1_write_baremetal(3u32, base, 0u32)
val tpidr_value = read_tpidr_el1_test()
expect(tpidr_value).to_equal(base + 3u64)
```

</details>

#### AC: large shift (16) produces 64 KiB per-CPU slots

1. simulate tpidr el1 write baremetal
   - Expected: tpidr_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. simulate tpidr el1 write baremetal
2. simulate tpidr write hosted
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
simulate_tpidr_el1_write_baremetal(0u32, 0x81000000u64, 12u32)
val before = read_tpidr_el1_test()
simulate_tpidr_write_hosted()
val after = read_tpidr_el1_test()
expect(after).to_equal(before)
```

</details>

### TPIDR_EL0 — userspace thread pointer simulation

#### AC: TPIDR_EL0 write stores the value independently from TPIDR_EL1

1. simulate tpidr el1 write baremetal
2. simulate tpidr el0 write
   - Expected: el0_value equals `0xDEADBEEF00000000u64`
   - Expected: el1_after equals `el1_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. simulate tpidr el0 write
2. simulate tpidr el0 write
   - Expected: first equals `0x1000u64`
   - Expected: second equals `0x2000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/kernel/arch/arm/per_cpu_tpidr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

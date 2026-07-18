# Per Cpu Tp Specification

> 1. simulate tp write baremetal

<!-- sdn-diagram:id=per_cpu_tp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=per_cpu_tp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

per_cpu_tp_spec -> std
per_cpu_tp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=per_cpu_tp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Cpu Tp Specification

## Scenarios

### Per-CPU tp Register Convention

### tp write at boot — baremetal path

#### AC-4: tp is set to per_cpu_data_base + hartid * per_cpu_slot_size for hart 0

1. simulate tp write baremetal
   - Expected: tp_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_id = 0u32
val per_cpu_base = 0x81000000u64
val per_cpu_shift = 12u32
simulate_tp_write_baremetal(hart_id, per_cpu_base, per_cpu_shift)
val tp_value = read_tp_test()
val expected = per_cpu_base + (0u64 << per_cpu_shift)
expect(tp_value).to_equal(expected)
```

</details>

#### AC-4: tp is set correctly for secondary hart (hart 1)

1. simulate tp write baremetal
   - Expected: tp_value equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_id = 1u32
val per_cpu_base = 0x81000000u64
val per_cpu_shift = 12u32
simulate_tp_write_baremetal(hart_id, per_cpu_base, per_cpu_shift)
val tp_value = read_tp_test()
val expected = per_cpu_base + (1u64 << per_cpu_shift)
expect(tp_value).to_equal(expected)
```

</details>

#### AC-4: tp differs across hart IDs (no aliasing)

1. simulate tp write baremetal
2. simulate tp write baremetal
   - Expected: tp_hart0 equals `base`
   - Expected: tp_hart1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0x81000000u64
val shift = 12u32
simulate_tp_write_baremetal(0u32, base, shift)
val tp_hart0 = read_tp_test()
simulate_tp_write_baremetal(1u32, base, shift)
val tp_hart1 = read_tp_test()
expect(tp_hart0).to_equal(base)
expect(tp_hart1).to_equal(base + 4096u64)
```

</details>

### tp NOT written in hosted (non-baremetal) build

#### AC-4: simulate_tp_write_hosted does NOT modify tp (returns original value)

1. simulate tp write hosted
   - Expected: after_tp equals `original_tp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original_tp = read_tp_test()
simulate_tp_write_hosted()
val after_tp = read_tp_test()
expect(after_tp).to_equal(original_tp)
```

</details>

### trap frame — x4 (tp) save and restore

#### AC-4: tp value is preserved across a simulated trap entry/exit round-trip

1. trap frame set tp
   - Expected: restored_tp equals `known_tp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known_tp = 0x81001000u64
val frame = trap_frame_new()
trap_frame_set_tp(frame, known_tp)
val restored_tp = trap_frame_save_restore_tp(frame)
expect(restored_tp).to_equal(known_tp)
```

</details>

#### AC-4: x4 slot in TrapFrame is at the expected register index (not aliased with gp/sp)

1. trap frame set reg
2. trap frame set reg
3. trap frame set reg
   - Expected: x4_val equals `0xBBBBu64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = trap_frame_new()
trap_frame_set_reg(frame, 3u32, 0xAAAAu64)
trap_frame_set_reg(frame, 4u32, 0xBBBBu64)
trap_frame_set_reg(frame, 5u32, 0xCCCCu64)
val x4_val = trap_frame_get_reg(frame, 4u32)
expect(x4_val).to_equal(0xBBBBu64)
```

</details>

#### AC-4: trap entry does not zero x4 — tp survives

1. trap frame set tp
   - Expected: saved equals `0x81002000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = trap_frame_new()
trap_frame_set_tp(frame, 0x81002000u64)
val saved = trap_frame_simulate_entry_exit(frame)
expect(saved).to_equal(0x81002000u64)
```

</details>

### rv32 tp convention

#### AC-4: rv32 tp write uses 32-bit per_cpu_base (upper bits zero)

1. simulate tp write baremetal rv32
   - Expected: tp_value equals `0x81000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_id = 0u32
val per_cpu_base_32 = 0x81000000u32
val per_cpu_shift = 10u32
simulate_tp_write_baremetal_rv32(hart_id, per_cpu_base_32, per_cpu_shift)
val tp_value = read_tp_test_rv32()
expect(tp_value).to_equal(0x81000000u32)
```

</details>

### production tp asm surface

#### AC-4: rv64 read/write helpers use the tp register in production source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/os/kernel/arch/riscv64/cpu.spl")
expect(source).to_contain("fn read_tp() -> u64")
expect(source).to_contain("fn write_tp(value: u64)")
expect(source).to_contain("tp (thread pointer)")
expect(source).to_contain("mv")
```

</details>

#### AC-4: rv32 read/write helpers use the tp register in production source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/os/kernel/arch/riscv32/cpu.spl")
expect(source).to_contain("fn read_tp_rv32() -> u32")
expect(source).to_contain("fn write_tp_rv32(value: u32)")
expect(source).to_contain("tp (thread pointer")
expect(source).to_contain("mv")
```

</details>

#### AC-4: baremetal startup writes tp from per_cpu_base_array and trap restores x4

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl")
expect(source).to_contain("var per_cpu_base_array: [u64; MAX_HARTS]")
expect(source).to_contain("\"mv tp, a1\"")
expect(source).to_contain("\"mv tp, a0\"")
expect(source).to_contain("\"sd x4,  24(sp)\"")
expect(source).to_contain("\"ld x4,  24(sp)\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv/per_cpu_tp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Per-CPU tp Register Convention
- tp write at boot — baremetal path
- tp NOT written in hosted (non-baremetal) build
- trap frame — x4 (tp) save and restore
- rv32 tp convention
- production tp asm surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

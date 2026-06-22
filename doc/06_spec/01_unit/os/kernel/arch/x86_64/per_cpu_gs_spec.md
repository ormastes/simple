# Per Cpu Gs Specification

> 1. simulate gs write baremetal

<!-- sdn-diagram:id=per_cpu_gs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=per_cpu_gs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

per_cpu_gs_spec -> std
per_cpu_gs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=per_cpu_gs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Cpu Gs Specification

## Scenarios

### x86_64 Per-CPU GS_BASE Register Convention

### GS_BASE write at boot — baremetal path

#### GS_BASE is set to per_cpu_base for cpu 0 (shift has no effect)

1. simulate gs write baremetal
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu_id = 0u32
val per_cpu_base = 0xFFFF800000100000u64
val per_cpu_shift = 12u32
simulate_gs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val gs = read_gs_base_test()
val expected = per_cpu_base + (0u64 << per_cpu_shift)
expect(gs).to_equal(expected)
```

</details>

#### GS_BASE is set correctly for cpu 1 (one slot up)

1. simulate gs write baremetal
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu_id = 1u32
val per_cpu_base = 0xFFFF800000100000u64
val per_cpu_shift = 12u32
simulate_gs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val gs = read_gs_base_test()
val expected = per_cpu_base + (1u64 << per_cpu_shift)
expect(gs).to_equal(expected)
```

</details>

#### GS_BASE differs across cpu IDs (no aliasing)

1. simulate gs write baremetal
2. simulate gs write baremetal
   - Expected: gs_cpu0 equals `base`
   - Expected: gs_cpu1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0xFFFF800000100000u64
val shift = 12u32
simulate_gs_write_baremetal(0u32, base, shift)
val gs_cpu0 = read_gs_base_test()
simulate_gs_write_baremetal(1u32, base, shift)
val gs_cpu1 = read_gs_base_test()
expect(gs_cpu0).to_equal(base)
expect(gs_cpu1).to_equal(base + 4096u64)
```

</details>

#### GS_BASE uses the per_cpu_shift for slot sizing

1. simulate gs write baremetal
   - Expected: gs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0xFFFF800000200000u64
val shift = 16u32
simulate_gs_write_baremetal(2u32, base, shift)
val gs = read_gs_base_test()
val expected = base + (2u64 << shift)
expect(gs).to_equal(expected)
```

</details>

### GS_BASE NOT written in hosted (non-baremetal) build

#### simulate_gs_write_hosted does NOT modify GS_BASE

1. simulate gs write baremetal
2. simulate gs write hosted
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val per_cpu_base = 0xFFFF800000300000u64
simulate_gs_write_baremetal(0u32, per_cpu_base, 12u32)
val before = read_gs_base_test()
simulate_gs_write_hosted()
val after = read_gs_base_test()
expect(after).to_equal(before)
```

</details>

### x86_64 Per-CPU FS_BASE Register Convention

### FS_BASE write at boot — baremetal path

#### FS_BASE is set to per_cpu_base for cpu 0

1. simulate fs write baremetal
   - Expected: fs equals `per_cpu_base`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu_id = 0u32
val per_cpu_base = 0xFFFF800000400000u64
val per_cpu_shift = 12u32
simulate_fs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val fs = read_fs_base_test()
expect(fs).to_equal(per_cpu_base)
```

</details>

#### FS_BASE is set correctly for cpu 1

1. simulate fs write baremetal
   - Expected: fs equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu_id = 1u32
val per_cpu_base = 0xFFFF800000400000u64
val per_cpu_shift = 12u32
simulate_fs_write_baremetal(cpu_id, per_cpu_base, per_cpu_shift)
val fs = read_fs_base_test()
val expected = per_cpu_base + 4096u64
expect(fs).to_equal(expected)
```

</details>

#### FS_BASE differs across cpu IDs (no aliasing)

1. simulate fs write baremetal
2. simulate fs write baremetal
   - Expected: fs_cpu0 equals `base`
   - Expected: fs_cpu1 equals `base + 4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0xFFFF800000400000u64
val shift = 12u32
simulate_fs_write_baremetal(0u32, base, shift)
val fs_cpu0 = read_fs_base_test()
simulate_fs_write_baremetal(1u32, base, shift)
val fs_cpu1 = read_fs_base_test()
expect(fs_cpu0).to_equal(base)
expect(fs_cpu1).to_equal(base + 4096u64)
```

</details>

### FS_BASE NOT written in hosted (non-baremetal) build

#### simulate_fs_write_hosted does NOT modify FS_BASE

1. simulate fs write baremetal
2. simulate fs write hosted
   - Expected: after equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val per_cpu_base = 0xFFFF800000500000u64
simulate_fs_write_baremetal(0u32, per_cpu_base, 12u32)
val before = read_fs_base_test()
simulate_fs_write_hosted()
val after = read_fs_base_test()
expect(after).to_equal(before)
```

</details>

### GS and FS are independent state

#### writing GS does not affect FS

1. simulate fs write baremetal
2. simulate gs write baremetal
   - Expected: fs_before equals `fs_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs_base = 0xFFFF800000600000u64
val fs_base = 0xFFFF800000700000u64
simulate_fs_write_baremetal(0u32, fs_base, 12u32)
val fs_before = read_fs_base_test()
simulate_gs_write_baremetal(3u32, gs_base, 12u32)
val fs_after = read_fs_base_test()
expect(fs_before).to_equal(fs_after)
```

</details>

#### writing FS does not affect GS

1. simulate gs write baremetal
2. simulate fs write baremetal
   - Expected: gs_before equals `gs_after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gs_base = 0xFFFF800000800000u64
val fs_base = 0xFFFF800000900000u64
simulate_gs_write_baremetal(0u32, gs_base, 12u32)
val gs_before = read_gs_base_test()
simulate_fs_write_baremetal(3u32, fs_base, 12u32)
val gs_after = read_gs_base_test()
expect(gs_before).to_equal(gs_after)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64/per_cpu_gs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 Per-CPU GS_BASE Register Convention
- GS_BASE write at boot — baremetal path
- GS_BASE NOT written in hosted (non-baremetal) build
- x86_64 Per-CPU FS_BASE Register Convention
- FS_BASE write at boot — baremetal path
- FS_BASE NOT written in hosted (non-baremetal) build
- GS and FS are independent state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

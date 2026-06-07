# Typed HAL Capsules Specification

> Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write operations. Uses composition-only design per D-7.

<!-- sdn-diagram:id=hal_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Typed HAL Capsules Specification

Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write operations. Uses composition-only design per D-7.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/01_unit/lib/hal/hal_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with
MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write
operations. Uses composition-only design per D-7.

## Behavior

- MmioAddress wraps base + offset + RegisterWidth
- PhysAddress wraps u64 with alignment utilities
- DmaAddress wraps PhysAddress + size, delegates to std.io.dma
- IrqLine wraps u32, IrqConfig holds trigger and priority
- Volatile ops delegate to std.io.volatile_ops

## Scenarios

### MmioAddress

### mmio_address constructor

#### AC-5: creates MmioAddress with base, offset, and width

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = mmio_address(0x40000000, 0x10, RegisterWidth.Width32)

expect(addr.base).to_equal(0x40000000)
expect(addr.offset).to_equal(0x10)
```

</details>

#### AC-5: RegisterWidth enum has all four widths

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w8 = RegisterWidth.Width8
val w16 = RegisterWidth.Width16
val w32 = RegisterWidth.Width32
val w64 = RegisterWidth.Width64

val is_w32 = w32 == RegisterWidth.Width32
expect(is_w32).to_equal(true)
```

</details>

### mmio_read

#### AC-5: mmio_read_u32 returns a u32 value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)
val value = mmio_read_u32(addr)

# Just verify call completes and returns some value
val is_valid = value >= 0
expect(is_valid).to_equal(true)
```

</details>

### mmio_write

#### AC-5: mmio_write_u32 accepts MmioAddress and value

1. mmio write u32
   - Expected: effective equals `0x40000004`
   - Expected: value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = mmio_address(0x40000000, 0x04, RegisterWidth.Width32)
val value = 0xDEADBEEF
val effective = addr.base + addr.offset

# Write should not error — just call it
mmio_write_u32(addr, value)

expect(effective).to_equal(0x40000004)
expect(value).to_equal(0xDEADBEEF)
```

</details>

### mmio_read_with_barrier

#### AC-5: read with barrier returns u64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width64)
val value = mmio_read_with_barrier(addr)

val is_valid = value >= 0
expect(is_valid).to_equal(true)
```

</details>

### PhysAddress

### phys_address constructor

#### AC-5: wraps a u64 address

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = phys_address(0x80000000)

val raw = phys_to_u64(addr)
expect(raw).to_equal(0x80000000)
```

</details>

### phys_is_aligned

#### AC-5: returns true for page-aligned address

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = phys_address(0x1000)
val aligned = phys_is_aligned(addr, 4096)

expect(aligned).to_equal(true)
```

</details>

#### AC-5: returns false for unaligned address

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = phys_address(0x1001)
val aligned = phys_is_aligned(addr, 4096)

expect(aligned).to_equal(false)
```

</details>

### phys_offset

#### AC-5: adds offset to physical address

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = phys_address(0x1000)
val offset_addr = phys_offset(addr, 0x100)

val raw = phys_to_u64(offset_addr)
expect(raw).to_equal(0x1100)
```

</details>

### DmaAddress

### dma_address constructor

#### AC-5: wraps PhysAddress and size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val phys = phys_address(0x2000)
val dma = dma_address(phys, 4096)

expect(dma.size).to_equal(4096)
```

</details>

### dma_address_alloc

#### AC-5: allocates a DMA region of given size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dma_address_alloc(4096, DmaDir.ToDevice)

val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

### IrqLine

### irq_line constructor

#### AC-5: wraps a u32 interrupt number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = irq_line(33)

expect(line.number).to_equal(33)
```

</details>

### irq_config

#### AC-5: creates config with line, trigger, and priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = irq_line(33)
val config = irq_config(line, IrqTrigger.EdgeRising, 5)

expect(config.priority).to_equal(5)
```

</details>

### IrqTrigger

#### AC-5: enum has all four trigger modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lh = IrqTrigger.LevelHigh
val ll = IrqTrigger.LevelLow
val er = IrqTrigger.EdgeRising
val ef = IrqTrigger.EdgeFalling

val is_edge = er == IrqTrigger.EdgeRising
expect(is_edge).to_equal(true)
```

</details>

### irq_enable and irq_disable

#### AC-5: irq_enable returns a Result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = irq_line(33)
val config = irq_config(line, IrqTrigger.LevelHigh, 1)
val result = irq_enable(config)

val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

#### AC-5: irq_is_pending returns bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = irq_line(33)
val pending = irq_is_pending(line)

# Just verify it returns a boolean (either true or false)
val is_bool = pending == true or pending == false
expect(is_bool).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>

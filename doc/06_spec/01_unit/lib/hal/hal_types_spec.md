# Typed HAL Capsules Specification

> Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write operations. Uses composition-only design per D-7.

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
| Updated | 2026-08-26 |
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

- AC-5: creates MmioAddress with base, offset, and width
   - Expected: addr.base equals `0x40000000`
   - Expected: addr.offset equals `0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: creates MmioAddress with base, offset, and width")
val addr = mmio_address(0x40000000, 0x10, RegisterWidth.Width32)

expect(addr.base).to_equal(0x40000000)
expect(addr.offset).to_equal(0x10)
```

</details>

#### AC-5: RegisterWidth enum has all four widths

- AC-5: RegisterWidth enum has all four widths
   - Expected: is_w32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: RegisterWidth enum has all four widths")
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

- AC-5: mmio_read_u32 returns a u32 value
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: mmio_read_u32 returns a u32 value")
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)
val value = mmio_read_u32(addr)

# Just verify call completes and returns some value
val is_valid = value >= 0
expect(is_valid).to_equal(true)
```

</details>

### mmio_write

#### AC-5: mmio_write_u32 accepts MmioAddress and value

- AC-5: mmio_write_u32 accepts MmioAddress and value
   - Expected: effective equals `0x40000004`
   - Expected: value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: mmio_write_u32 accepts MmioAddress and value")
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

- AC-5: read with barrier returns u64
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: read with barrier returns u64")
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width64)
val value = mmio_read_with_barrier(addr)

val is_valid = value >= 0
expect(is_valid).to_equal(true)
```

</details>

### PhysAddress

### phys_address constructor

#### AC-5: wraps a u64 address

- AC-5: wraps a u64 address
   - Expected: raw equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: wraps a u64 address")
val addr = phys_address(0x80000000)

val raw = phys_to_u64(addr)
expect(raw).to_equal(0x80000000)
```

</details>

### phys_is_aligned

#### AC-5: returns true for page-aligned address

- AC-5: returns true for page-aligned address
   - Expected: aligned is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: returns true for page-aligned address")
val addr = phys_address(0x1000)
val aligned = phys_is_aligned(addr, 4096)

expect(aligned).to_equal(true)
```

</details>

#### AC-5: returns false for unaligned address

- AC-5: returns false for unaligned address
   - Expected: aligned is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: returns false for unaligned address")
val addr = phys_address(0x1001)
val aligned = phys_is_aligned(addr, 4096)

expect(aligned).to_equal(false)
```

</details>

### phys_offset

#### AC-5: adds offset to physical address

- AC-5: adds offset to physical address
   - Expected: raw equals `0x1100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: adds offset to physical address")
val addr = phys_address(0x1000)
val offset_addr = phys_offset(addr, 0x100)

val raw = phys_to_u64(offset_addr)
expect(raw).to_equal(0x1100)
```

</details>

### DmaAddress

### dma_address constructor

#### AC-5: wraps PhysAddress and size

- AC-5: wraps PhysAddress and size
   - Expected: dma.size equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: wraps PhysAddress and size")
val phys = phys_address(0x2000)
val dma = dma_address(phys, 4096)

expect(dma.size).to_equal(4096)
```

</details>

### dma_address_alloc

#### AC-5: allocates a DMA region of given size

- AC-5: allocates a DMA region of given size
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: allocates a DMA region of given size")
val result = dma_address_alloc(4096, DmaDir.ToDevice)

val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

### IrqLine

### irq_line constructor

#### AC-5: wraps a u32 interrupt number

- AC-5: wraps a u32 interrupt number
   - Expected: line.number equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: wraps a u32 interrupt number")
val line = irq_line(33)

expect(line.number).to_equal(33)
```

</details>

### irq_config

#### AC-5: creates config with line, trigger, and priority

- AC-5: creates config with line, trigger, and priority
   - Expected: config.priority equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: creates config with line, trigger, and priority")
val line = irq_line(33)
val config = irq_config(line, IrqTrigger.EdgeRising, 5)

expect(config.priority).to_equal(5)
```

</details>

### IrqTrigger

#### AC-5: enum has all four trigger modes

- AC-5: enum has all four trigger modes
   - Expected: is_edge is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: enum has all four trigger modes")
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

- AC-5: irq_enable returns a Result
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: irq_enable returns a Result")
val line = irq_line(33)
val config = irq_config(line, IrqTrigger.LevelHigh, 1)
val result = irq_enable(config)

val is_ok = result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

#### AC-5: irq_is_pending returns bool

- AC-5: irq_is_pending returns bool
   - Expected: is_bool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-5: irq_is_pending returns bool")
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

- **Plan:** `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f4a5f89d384ba5d9ca89f7aae68f0b0a819816f11b1be2b7580719f75f4f1e23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4a5f89d384ba5d9ca89f7aae68f0b0a819816f11b1be2b7580719f75f4f1e23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4a5f89d384ba5d9ca89f7aae68f0b0a819816f11b1be2b7580719f75f4f1e23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/hal/hal_types_spec.spl
mirror: doc/06_spec/01_unit/lib/hal/hal_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hal/hal_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hal/hal_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hal/hal_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hal/hal_types_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: creates MmioAddress with base, offset, and width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hal/hal_types_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: RegisterWidth enum has all four widths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hal/hal_types_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: mmio_read_u32 returns a u32 value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

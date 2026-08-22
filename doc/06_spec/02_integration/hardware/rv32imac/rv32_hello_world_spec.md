# RV32IMAC Hello World Verification

> Verifies the SoC boots and produces UART output. Tests the full pipeline from instruction fetch to UART character output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32IMAC Hello World Verification

Verifies the SoC boots and produces UART output. Tests the full pipeline from instruction fetch to UART character output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-HELLO-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# RV32IMAC Hello World Verification

**Feature IDs:** #RV32-HELLO-001
**Category:** Hardware
**Difficulty:** 3/5
**Status:** In Progress

## Overview

Verifies the SoC boots and produces UART output.
Tests the full pipeline from instruction fetch to UART character output.

## Scenarios

### RV32 UART Model

#### starts with TX empty

- Verify: starts with TX empty
   - Expected: (lsr and 0x60) equals `0x60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: starts with TX empty")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Fresh UART model
**When:** Reading LSR
**Then:** TX empty and TX idle bits are set
"""
val uart = Rv32Uart.create()
val lsr = uart.read_reg(UART_LSR)
expect((lsr and 0x60)).to_equal(0x60)
```

</details>

#### buffers transmitted bytes

- Verify: buffers transmitted bytes
   - Expected: uart.tx_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: uart.consume_tx() equals `0x48`
   - Expected: uart.consume_tx() equals `0x65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: buffers transmitted bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** UART model
**When:** Writing to THR
**Then:** Byte appears in TX output buffer
"""
var uart = Rv32Uart.create()
uart.write_reg(UART_THR, 0x48)  # 'H'
uart.write_reg(UART_THR, 0x65)  # 'e'
expect(uart.tx_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(uart.consume_tx()).to_equal(0x48)
expect(uart.consume_tx()).to_equal(0x65)
```

</details>

### RV32 Timer Model

#### increments mtime on tick

- Verify: increments mtime on tick
   - Expected: timer.read(0xBFF8) equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: increments mtime on tick")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var timer = Rv32Clint.create(1)
timer.tick()
timer.tick()
timer.tick()
expect(timer.read(0xBFF8)).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### generates interrupt when mtime >= mtimecmp

- Verify: generates interrupt when mtime >= mtimecmp
   - Expected: timer.get_mtip(0) is false
   - Expected: timer.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: generates interrupt when mtime >= mtimecmp")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var timer = Rv32Clint.create(1)
timer.write(0x4000, 5)
timer.tick()
timer.tick()
expect(timer.get_mtip(0)).to_equal(false)
timer.tick()
timer.tick()
timer.tick()
expect(timer.get_mtip(0)).to_equal(true)
```

</details>

### RV32 SRAM Model

#### reads back written data

- Verify: reads back written data
   - Expected: sram.read32(0).value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: reads back written data")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var sram = Rv32Ram.create(16)
sram.write32(0, 0xDEADBEEF)
expect(sram.read32(0).value).to_equal(0xDEADBEEF)
```

</details>

#### supports byte-enable writes

- Verify: supports byte-enable writes
   - Expected: sram.read32(0).value and 0xFF equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: supports byte-enable writes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var sram = Rv32Ram.create(16)
sram.write32(0, 0x12345678)
sram.write8(0, 0xAA)
expect(sram.read32(0).value and 0xFF).to_equal(0xAA)
```

</details>

### RV32 Bus Address Decode

#### routes ROM addresses correctly

- Verify: routes ROM addresses correctly
   - Expected: bus.read32(0x00001000).fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: routes ROM addresses correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.read32(0x00001000).fault).to_equal(true)
```

</details>

#### routes SRAM addresses correctly

- Verify: routes SRAM addresses correctly
   - Expected: bus.write32(0x80000100, 0xABCD1234).fault is false
   - Expected: bus.read32(0x80000100).value equals `0xABCD1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: routes SRAM addresses correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.write32(0x80000100, 0xABCD1234).fault).to_equal(false)
expect(bus.read32(0x80000100).value).to_equal(0xABCD1234)
```

</details>

#### routes UART addresses correctly

- Verify: routes UART addresses correctly
   - Expected: bus.write8(platform.uart_base, 0x41).fault is false
   - Expected: bus.uart.consume_tx() equals `0x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: routes UART addresses correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val bus = Rv32Bus.create(0x1000, 1)
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(bus.write8(platform.uart_base, 0x41).fault).to_equal(false)
expect(bus.uart.consume_tx()).to_equal(0x41)
```

</details>

#### routes Timer addresses correctly

- Verify: routes Timer addresses correctly
   - Expected: bus.clint.get_mtip(0) is false
   - Expected: bus.clint.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: routes Timer addresses correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val bus = Rv32Bus.create(0x1000, 1)
val platform = RiscvPlatformProfile.qemu_virt_rv32()
bus.write32(platform.clint_base + 0x4000, 3)
bus.tick()
bus.tick()
expect(bus.clint.get_mtip(0)).to_equal(false)
bus.tick()
expect(bus.clint.get_mtip(0)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `921029dc60273e54dbeaadaff17d8f4b6b8d804dcbdb28d3afa616207250a5ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `921029dc60273e54dbeaadaff17d8f4b6b8d804dcbdb28d3afa616207250a5ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `921029dc60273e54dbeaadaff17d8f4b6b8d804dcbdb28d3afa616207250a5ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl
mirror: doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

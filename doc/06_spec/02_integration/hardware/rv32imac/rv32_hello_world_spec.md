# RV32IMAC Hello World Verification

> Verifies the SoC boots and produces UART output. Tests the full pipeline from instruction fetch to UART character output.

<!-- sdn-diagram:id=rv32_hello_world_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_hello_world_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_hello_world_spec -> std
rv32_hello_world_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_hello_world_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the SoC boots and produces UART output.
Tests the full pipeline from instruction fetch to UART character output.

## Scenarios

### RV32 UART Model

#### starts with TX empty

- starts with TX empty
   - Expected: (lsr and 0x60) equals `0x60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("starts with TX empty")
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

- buffers transmitted bytes
   - Expected: uart.tx_count equals `2`
   - Expected: uart.consume_tx() equals `0x48`
   - Expected: uart.consume_tx() equals `0x65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buffers transmitted bytes")
"""
**Given:** UART model
**When:** Writing to THR
**Then:** Byte appears in TX output buffer
"""
var uart = Rv32Uart.create()
uart.write_reg(UART_THR, 0x48)  # 'H'
uart.write_reg(UART_THR, 0x65)  # 'e'
expect(uart.tx_count).to_equal(2)
expect(uart.consume_tx()).to_equal(0x48)
expect(uart.consume_tx()).to_equal(0x65)
```

</details>

### RV32 Timer Model

#### increments mtime on tick

- increments mtime on tick
   - Expected: timer.read(0xBFF8) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("increments mtime on tick")
var timer = Rv32Clint.create(1)
timer.tick()
timer.tick()
timer.tick()
expect(timer.read(0xBFF8)).to_equal(3)
```

</details>

#### generates interrupt when mtime >= mtimecmp

- generates interrupt when mtime >= mtimecmp
   - Expected: timer.get_mtip(0) is false
5. timer tick
6. timer tick
7. timer tick
   - Expected: timer.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("generates interrupt when mtime >= mtimecmp")
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

- reads back written data
   - Expected: sram.read32(0).value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads back written data")
var sram = Rv32Ram.create(16)
sram.write32(0, 0xDEADBEEF)
expect(sram.read32(0).value).to_equal(0xDEADBEEF)
```

</details>

#### supports byte-enable writes

- supports byte-enable writes
   - Expected: sram.read32(0).value and 0xFF equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports byte-enable writes")
var sram = Rv32Ram.create(16)
sram.write32(0, 0x12345678)
sram.write8(0, 0xAA)
expect(sram.read32(0).value and 0xFF).to_equal(0xAA)
```

</details>

### RV32 Bus Address Decode

#### routes ROM addresses correctly

- routes ROM addresses correctly
   - Expected: bus.read32(0x00001000).fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes ROM addresses correctly")
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.read32(0x00001000).fault).to_equal(true)
```

</details>

#### routes SRAM addresses correctly

- routes SRAM addresses correctly
   - Expected: bus.write32(0x80000100, 0xABCD1234).fault is false
   - Expected: bus.read32(0x80000100).value equals `0xABCD1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes SRAM addresses correctly")
val bus = Rv32Bus.create(0x1000, 1)
expect(bus.write32(0x80000100, 0xABCD1234).fault).to_equal(false)
expect(bus.read32(0x80000100).value).to_equal(0xABCD1234)
```

</details>

#### routes UART addresses correctly

- routes UART addresses correctly
   - Expected: bus.write8(platform.uart_base, 0x41).fault is false
   - Expected: bus.uart.consume_tx() equals `0x41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes UART addresses correctly")
val bus = Rv32Bus.create(0x1000, 1)
val platform = RiscvPlatformProfile.qemu_virt_rv32()
expect(bus.write8(platform.uart_base, 0x41).fault).to_equal(false)
expect(bus.uart.consume_tx()).to_equal(0x41)
```

</details>

#### routes Timer addresses correctly

- routes Timer addresses correctly
   - Expected: bus.clint.get_mtip(0) is false
4. bus tick
   - Expected: bus.clint.get_mtip(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes Timer addresses correctly")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RV32IMAC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0385b56a938433d5eda0074e29361cea6575fdaf3eee9f1ffd0aacb6699ab13b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0385b56a938433d5eda0074e29361cea6575fdaf3eee9f1ffd0aacb6699ab13b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0385b56a938433d5eda0074e29361cea6575fdaf3eee9f1ffd0aacb6699ab13b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl
mirror: doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/hardware/rv32imac/rv32_hello_world_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with TX empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'buffers transmitted bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/hardware/rv32imac/rv32_hello_world_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'increments mtime on tick' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

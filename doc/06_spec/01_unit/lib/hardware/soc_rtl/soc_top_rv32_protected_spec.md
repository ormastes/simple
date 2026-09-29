# Soc Top Rv32 Protected Specification

> Tests covering RV32 protected SoC Linux interrupt and input path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Soc Top Rv32 Protected Specification

## Scenarios

### RV32 protected SoC Linux interrupt and input path

#### latches and consumes one UART receive event exactly once

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- latches and consumes one UART receive event exactly once
   - Expected: received.uart.rx_count equals `1`
   - Expected: soc_protected32_read(received, UART_BASE) equals `65`
   - Expected: consumed.uart.rx_count equals `0`
   - Expected: soc_protected32_read(consumed, UART_BASE) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("latches and consumes one UART receive event exactly once")
val initial = soc_protected32_create(16)
val received = soc_protected32_uart_push_rx(initial, 65)
expect(received.uart.rx_count).to_equal(1)
expect(soc_protected32_read(received, UART_BASE)).to_equal(65)

val consumed = soc_protected32_read_update(received, UART_BASE)
expect(consumed.uart.rx_count).to_equal(0)
expect(soc_protected32_read(consumed, UART_BASE)).to_equal(0)
```

</details>

#### maps UART receive through PLIC context zero to MEIP

- maps UART receive through PLIC context zero to MEIP
   - Expected: delivered.core.csr_m.mip & MIP_MEIP_32 equals `MIP_MEIP_32`
   - Expected: delivered.core.csr_m.mip & MIP_SEIP_32 equals `MIP_SEIP_32`
   - Expected: soc_protected32_read(delivered, PLIC_BASE + PLIC_CLAIM_OFF) equals `UART_SOURCE_32`
   - Expected: claimed.plic.pending & (1 << UART_SOURCE_32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps UART receive through PLIC context zero to MEIP")
var soc = soc_protected32_create(16)
soc.uart = uart_mmio_write(soc.uart, 1, IER_RDI)
soc.plic = plic_mmio_write(soc.plic, UART_SOURCE_32 * 4, 1)
soc.plic = plic_mmio_write(soc.plic, PLIC_ENABLE_OFF, 1 << UART_SOURCE_32)
soc.plic = plic_mmio_write(soc.plic, PLIC_ENABLE_S_OFF, 1 << UART_SOURCE_32)
soc = soc_protected32_uart_push_rx(soc, 66)

val delivered = soc_protected32_tick(soc).state
expect(delivered.core.csr_m.mip & MIP_MEIP_32).to_equal(MIP_MEIP_32)
expect(delivered.core.csr_m.mip & MIP_SEIP_32).to_equal(MIP_SEIP_32)
expect(soc_protected32_read(delivered, PLIC_BASE + PLIC_CLAIM_OFF)).to_equal(UART_SOURCE_32)

val claimed = soc_protected32_read_update(delivered, PLIC_BASE + PLIC_CLAIM_OFF)
expect(claimed.plic.pending & (1 << UART_SOURCE_32)).to_equal(0)
```

</details>

#### routes platform supervisor timer and external levels through the core owner

- routes platform supervisor timer and external levels through the core owner
   - Expected: delivered.core.csr_m.mip & MIP_STIP_32 equals `MIP_STIP_32`
   - Expected: delivered.core.csr_m.mip & MIP_SEIP_32 equals `MIP_SEIP_32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes platform supervisor timer and external levels through the core owner")
val initial = soc_protected32_create(16)
val pending = soc_protected32_set_supervisor_interrupts(initial, true, true)
val delivered = soc_protected32_tick(pending).state
expect(delivered.core.csr_m.mip & MIP_STIP_32).to_equal(MIP_STIP_32)
expect(delivered.core.csr_m.mip & MIP_SEIP_32).to_equal(MIP_SEIP_32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 protected SoC Linux interrupt and input path.
- RV32 protected SoC Linux interrupt and input path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b78f6a659014f2f3985c7ddfa39264447542dd01a3fac7921053dda082ca72bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b78f6a659014f2f3985c7ddfa39264447542dd01a3fac7921053dda082ca72bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b78f6a659014f2f3985c7ddfa39264447542dd01a3fac7921053dda082ca72bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'latches and consumes one UART receive event exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps UART receive through PLIC context zero to MEIP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/soc_rtl/soc_top_rv32_protected_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes platform supervisor timer and external levels through the core owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

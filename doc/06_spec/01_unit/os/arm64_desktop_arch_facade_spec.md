# Arm64 Desktop Arch Facade Specification

> Tests covering AArch64 desktop architecture facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Desktop Arch Facade Specification

## Scenarios

### AArch64 desktop architecture facades

#### keeps production RAMFB and UART access out of the legacy glass demo

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps production RAMFB and UART access out of the legacy glass demo


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps production RAMFB and UART access out of the legacy glass demo")
arm64_desktop_source_contract()
```

</details>

#### reads PL011 input through the shared MMIO owner

- reads PL011 input through the shared MMIO owner
   - Expected: pl011_data_ready(ARM_VIRT_PL011_BASE) equals `0u64`
   - Expected: pl011_data_ready(ARM_VIRT_PL011_BASE) equals `1u64`
   - Expected: pl011_read_char(ARM_VIRT_PL011_BASE) equals `0x41u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reads PL011 input through the shared MMIO owner")
mmio_reset_for_test()
mmio_write32(ARM_VIRT_PL011_BASE + PL011_UARTFR, PL011_FR_RXFE)
expect(pl011_data_ready(ARM_VIRT_PL011_BASE)).to_equal(0u64)

mmio_write32(ARM_VIRT_PL011_BASE + PL011_UARTFR, 0u32)
expect(pl011_data_ready(ARM_VIRT_PL011_BASE)).to_equal(1u64)

mmio_write32(ARM_VIRT_PL011_BASE + PL011_UARTDR, 0x141u32)
expect(pl011_read_char(ARM_VIRT_PL011_BASE)).to_equal(0x41u64)
mmio_disable_test_mode()
```

</details>

#### encodes and classifies the fw_cfg DMA protocol

- encodes and classifies the fw_cfg DMA protocol
   - Expected: _swap16(0x0019u16) equals `0x1900u16`
   - Expected: _swap32(0x11223344u32) equals `0x44332211u32`
   - Expected: _be32_byte(0x11223344u32, 0) equals `0x11u8`
   - Expected: _be32_byte(0x11223344u32, 1) equals `0x22u8`
   - Expected: _be32_byte(0x11223344u32, 2) equals `0x33u8`
   - Expected: _be32_byte(0x11223344u32, 3) equals `0x44u8`
   - Expected: _ramfb_dma_control(0x0121u16) equals `0x01210018u32`
   - Expected: _ramfb_dma_status(0u32) equals `1`
   - Expected: _ramfb_dma_status(1u32) equals `-1`
   - Expected: _ramfb_dma_status(0x01210018u32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes and classifies the fw_cfg DMA protocol")
expect(_swap16(0x0019u16)).to_equal(0x1900u16)
expect(_swap32(0x11223344u32)).to_equal(0x44332211u32)
expect(_be32_byte(0x11223344u32, 0)).to_equal(0x11u8)
expect(_be32_byte(0x11223344u32, 1)).to_equal(0x22u8)
expect(_be32_byte(0x11223344u32, 2)).to_equal(0x33u8)
expect(_be32_byte(0x11223344u32, 3)).to_equal(0x44u8)
expect(_ramfb_dma_control(0x0121u16)).to_equal(0x01210018u32)
expect(_ramfb_dma_status(0u32)).to_equal(1)
expect(_ramfb_dma_status(1u32)).to_equal(-1)
expect(_ramfb_dma_status(0x01210018u32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/arm64_desktop_arch_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AArch64 desktop architecture facades.
- AArch64 desktop architecture facades

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbe805470e49e6465124ded08f01ffcbe4c14b81a9a27ec06951f13bc466adc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbe805470e49e6465124ded08f01ffcbe4c14b81a9a27ec06951f13bc466adc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbe805470e49e6465124ded08f01ffcbe4c14b81a9a27ec06951f13bc466adc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/arm64_desktop_arch_facade_spec.spl
mirror: doc/06_spec/01_unit/os/arm64_desktop_arch_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/arm64_desktop_arch_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/arm64_desktop_arch_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/arm64_desktop_arch_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/arm64_desktop_arch_facade_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps production RAMFB and UART access out of the legacy glass demo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/arm64_desktop_arch_facade_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads PL011 input through the shared MMIO owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/arm64_desktop_arch_facade_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes and classifies the fw_cfg DMA protocol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

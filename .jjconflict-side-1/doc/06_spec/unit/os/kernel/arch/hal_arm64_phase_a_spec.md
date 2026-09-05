# Hal Arm64 Phase A Specification

> Tests covering hal.arm64 Phase A — console + CPU + boot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Arm64 Phase A Specification

## Scenarios

### hal.arm64 Phase A — console + CPU + boot

#### hal_address_width returns 48 for arm64

- hal_address_width returns 48 for arm64
   - Expected: expected equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hal_address_width returns 48 for arm64")
"""ARM64 with 4-level 4KB granule uses 48-bit virtual addresses."""
val expected: u32 = 48
expect(expected).to_equal(48)
```

</details>

#### PL011 UART base address is 0x09000000

- PL011 UART base address is 0x09000000
   - Expected: pl011_base equals `0x09000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PL011 UART base address is 0x09000000")
"""QEMU virt machine maps PL011 at 0x09000000."""
val pl011_base: u64 = 0x09000000
expect(pl011_base).to_equal(0x09000000)
```

</details>

#### DAIF_ALL mask covers all four interrupt types

- DAIF_ALL mask covers all four interrupt types
   - Expected: daif_all equals `0xF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DAIF_ALL mask covers all four interrupt types")
"""DAIF_ALL = 0xF masks Debug, SError, IRQ, FIQ."""
val daif_all: u64 = 0xF
expect(daif_all).to_equal(0xF)
```

</details>

#### UARTCR enable bits are CR_UARTEN | CR_TXE

- UARTCR enable bits are CR_UARTEN | CR_TXE
   - Expected: combined equals `0x101`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UARTCR enable bits are CR_UARTEN | CR_TXE")
"""Control register must set bit 0 (UARTEN) and bit 8 (TXE) to enable TX."""
val cr_uarten: u32 = 1
val cr_txe: u32 = 1 << 8
val combined: u32 = cr_uarten | cr_txe
expect(combined).to_equal(0x101)
```

</details>

#### UARTFR TXFF bit is bit 5

- UARTFR TXFF bit is bit 5
   - Expected: fr_txff equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UARTFR TXFF bit is bit 5")
"""Flag register bit 5 signals transmit FIFO full (spin condition)."""
val fr_txff: u32 = 1 << 5
expect(fr_txff).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hal.arm64 Phase A — console + CPU + boot.
- hal.arm64 Phase A — console + CPU + boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `a5be933be1c591b95e81e94e2a31ed3489a8958ae25fcc74b204840657b8f5c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5be933be1c591b95e81e94e2a31ed3489a8958ae25fcc74b204840657b8f5c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5be933be1c591b95e81e94e2a31ed3489a8958ae25fcc74b204840657b8f5c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/hal_arm64_phase_a_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/hal_arm64_phase_a_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/hal_arm64_phase_a_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hal_address_width returns 48 for arm64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PL011 UART base address is 0x09000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/hal_arm64_phase_a_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DAIF_ALL mask covers all four interrupt types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

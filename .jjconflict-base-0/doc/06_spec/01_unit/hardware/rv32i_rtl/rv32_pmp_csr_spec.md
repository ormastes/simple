# Rv32 Pmp Csr Specification

> Tests covering RV32 PMP CSRs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 Pmp Csr Specification

## Scenarios

### RV32 PMP CSRs

#### resets sixteen entries and normalizes invalid configuration bits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resets sixteen entries and normalizes invalid configuration bits
   - Expected: entries.cfg_0 equals `0`
   - Expected: entries.addr_15 equals `0`
   - Expected: pmp32_cfg_normalize(0xFF) equals `0x9F`
   - Expected: pmp32_cfg_normalize(0xE2) equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("resets sixteen entries and normalizes invalid configuration bits")
val entries = pmp32_entries_reset()
expect(entries.cfg_0).to_equal(0)
expect(entries.addr_15).to_equal(0)
expect(pmp32_cfg_normalize(0xFF)).to_equal(0x9F)
expect(pmp32_cfg_normalize(0xE2)).to_equal(0x80)
```

</details>

#### packs all four RV32 pmpcfg CSRs as four byte lanes

- packs all four RV32 pmpcfg CSRs as four byte lanes
   - Expected: first.entries.cfg_0 equals `0x01`
   - Expected: first.entries.cfg_3 equals `0x18`
   - Expected: read_first.value equals `0x18040101`
   - Expected: read_second.value equals `0x05030101`
   - Expected: read_third.value equals `0x01000080`
   - Expected: read_last.value equals `0x01000080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("packs all four RV32 pmpcfg CSRs as four byte lanes")
val reset = pmp32_entries_reset()
val first = pmp32_csr_write(reset, 0x3A0, 0x18040101)
val second = pmp32_csr_write(first.entries, 0x3A1, 0x05030101)
val third = pmp32_csr_write(second.entries, 0x3A2, 0x01000080)
val last = pmp32_csr_write(third.entries, 0x3A3, 0x01000080)
val read_first = pmp32_csr_read(last.entries, 0x3A0)
val read_second = pmp32_csr_read(last.entries, 0x3A1)
val read_third = pmp32_csr_read(last.entries, 0x3A2)
val read_last = pmp32_csr_read(last.entries, 0x3A3)
expect(first.entries.cfg_0).to_equal(0x01)
expect(first.entries.cfg_3).to_equal(0x18)
expect(read_first.value).to_equal(0x18040101)
expect(read_second.value).to_equal(0x05030101)
expect(read_third.value).to_equal(0x01000080)
expect(read_last.value).to_equal(0x01000080)
```

</details>

#### keeps locked configuration immutable

- keeps locked configuration immutable
   - Expected: cfg_write.entries.cfg_0 equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("keeps locked configuration immutable")
var entries = pmp32_entries_reset()
entries.cfg_0 = 0x80
val cfg_write = pmp32_csr_write(entries, 0x3A0, 0x0101)
expect(cfg_write.entries.cfg_0).to_equal(0x80)
```

</details>

#### locks a TOR entry predecessor address

- locks a TOR entry predecessor address
   - Expected: addr_write.entries.addr_0 equals `0x100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("locks a TOR entry predecessor address")
var entries = pmp32_entries_reset()
entries.addr_0 = 0x100
entries.cfg_1 = 0x88
val addr_write = pmp32_csr_write(entries, 0x3B0, 0x200)
expect(addr_write.entries.addr_0).to_equal(0x100)
```

</details>

#### masks pmpaddr writes and rejects unrelated CSRs

- masks pmpaddr writes and rejects unrelated CSRs
   - Expected: written.entries.addr_15 equals `0xFFFFFFFF`
   - Expected: read.value equals `0xFFFFFFFF`
   - Expected: unrelated.handled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("masks pmpaddr writes and rejects unrelated CSRs")
val entries = pmp32_entries_reset()
val written = pmp32_csr_write(entries, 0x3BF, 0xFFFFFFFF)
val read = pmp32_csr_read(written.entries, 0x3BF)
val unrelated = pmp32_csr_write(entries, 0x300, 1)
expect(written.entries.addr_15).to_equal(0xFFFFFFFF)
expect(read.value).to_equal(0xFFFFFFFF)
expect(unrelated.handled).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 PMP CSRs.
- RV32 PMP CSRs

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

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e19eaee76d5071a4d072d44f5b8ada5e4d5ac3b4113ee205ee7f73d6f6dd681`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e19eaee76d5071a4d072d44f5b8ada5e4d5ac3b4113ee205ee7f73d6f6dd681`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e19eaee76d5071a4d072d44f5b8ada5e4d5ac3b4113ee205ee7f73d6f6dd681`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets sixteen entries and normalizes invalid configuration bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs all four RV32 pmpcfg CSRs as four byte lanes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_pmp_csr_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps locked configuration immutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

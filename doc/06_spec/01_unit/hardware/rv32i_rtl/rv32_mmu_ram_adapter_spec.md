# Rv32 Mmu Ram Adapter Specification

> Tests covering RV32 legacy RamState MMU adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 Mmu Ram Adapter Specification

## Scenarios

### RV32 legacy RamState MMU adapter

#### preserves bare identity translation through the public facade

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves bare identity translation through the public facade
   - Expected: result.paddr equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("preserves bare identity translation through the public facade")
val result = mmu_translate(mmu_create(), 0x12345678,
    ACCESS_LOAD, PRIV_S, ram_create(0))
expect(result.fault).to_be(false)
expect(result.paddr).to_equal(0x12345678)
```

</details>

#### preserves the former two-level in-memory Sv32 walk

- preserves the former two-level in-memory Sv32 walk
   - Expected: result.paddr equals `0x00003020`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("preserves the former two-level in-memory Sv32 walk")
var ram = ram_create(4096)
ram = ram_write(ram, 0x1004, 0x00000801, 2)
ram = ram_write(ram, 0x2004, 0x00000C43, 2)
val mmu = mmu_set_satp(mmu_create(), 0x80000001)
val result = mmu_translate(mmu, 0x00401020, ACCESS_LOAD, PRIV_S, ram)
expect(result.fault).to_be(false)
expect(result.paddr).to_equal(0x00003020)
```

</details>

#### preserves the former load page-fault cause

- preserves the former load page-fault cause
   - Expected: result.fault_cause equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("preserves the former load page-fault cause")
val mmu = mmu_set_satp(mmu_create(), 0x80000001)
val result = mmu_translate(mmu, 0x00401020,
    ACCESS_LOAD, PRIV_S, ram_create(4096))
expect(result.fault).to_be(true)
expect(result.fault_cause).to_equal(13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 legacy RamState MMU adapter.
- RV32 legacy RamState MMU adapter

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

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9aab0e436268a43a13f2bd67f5874aa8df0de283da983d649772de1b4167e36`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9aab0e436268a43a13f2bd67f5874aa8df0de283da983d649772de1b4167e36`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9aab0e436268a43a13f2bd67f5874aa8df0de283da983d649772de1b4167e36`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves bare identity translation through the public facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the former two-level in-memory Sv32 walk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv32i_rtl/rv32_mmu_ram_adapter_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the former load page-fault cause' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

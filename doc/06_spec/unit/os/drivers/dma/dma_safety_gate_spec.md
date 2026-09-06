# Dma Safety Gate Specification

> Tests covering dma safety gate hardening acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dma Safety Gate Specification

## Scenarios

### dma safety gate hardening acceptance

#### accepts the direct DMA path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the direct DMA path
   - Expected: gate.effective_path() equals `dma`
   - Expected: gate.hardening_acceptance_ready() is true
   - Expected: gate.hardening_acceptance_reason() equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the direct DMA path")
val gate = DisplayDmaFallbackGate.with_dma()
expect(gate.effective_path()).to_equal("dma")
expect(gate.hardening_acceptance_ready()).to_equal(true)
expect(gate.hardening_acceptance_reason()).to_equal("ready")
```

</details>

#### keeps framebuffer fallback diagnostic-only

- keeps framebuffer fallback diagnostic-only
   - Expected: gate.effective_path() equals `framebuffer`
   - Expected: gate.hardening_acceptance_ready() is false
   - Expected: gate.hardening_acceptance_reason() equals `display-dma-fallback-diagnostic:framebuffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps framebuffer fallback diagnostic-only")
val gate = DisplayDmaFallbackGate.fallback_only()
expect(gate.effective_path()).to_equal("framebuffer")
expect(gate.hardening_acceptance_ready()).to_equal(false)
expect(gate.hardening_acceptance_reason()).to_equal("display-dma-fallback-diagnostic:framebuffer")
```

</details>

#### accepts SR-IOV hardening only with IOMMU isolation

- accepts SR-IOV hardening only with IOMMU isolation
   - Expected: gate.can_proceed() is true
   - Expected: gate.hardening_acceptance_ready() is true
   - Expected: gate.hardening_acceptance_reason() equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts SR-IOV hardening only with IOMMU isolation")
val gate = SriovIsolationGate.request_vf(true)
expect(gate.can_proceed()).to_equal(true)
expect(gate.hardening_acceptance_ready()).to_equal(true)
expect(gate.hardening_acceptance_reason()).to_equal("ready")
```

</details>

#### keeps trusted no-IOMMU SR-IOV diagnostic-only

- keeps trusted no-IOMMU SR-IOV diagnostic-only
   - Expected: gate.can_proceed() is false
   - Expected: gate.hardening_acceptance_ready() is false
   - Expected: gate.hardening_acceptance_reason() equals `sriov-trust-mode-diagnostic:trusted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps trusted no-IOMMU SR-IOV diagnostic-only")
val gate = SriovIsolationGate.trusted_no_iommu()
expect(gate.can_proceed()).to_equal(false)
expect(gate.hardening_acceptance_ready()).to_equal(false)
expect(gate.hardening_acceptance_reason()).to_equal("sriov-trust-mode-diagnostic:trusted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/dma/dma_safety_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dma safety gate hardening acceptance.
- dma safety gate hardening acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ac08121f4e03302f53d491b1a7a4e68c4cb8ac728472cb8748fccb7960958f2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac08121f4e03302f53d491b1a7a4e68c4cb8ac728472cb8748fccb7960958f2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac08121f4e03302f53d491b1a7a4e68c4cb8ac728472cb8748fccb7960958f2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/dma/dma_safety_gate_spec.spl
mirror: doc/06_spec/unit/os/drivers/dma/dma_safety_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/dma/dma_safety_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/dma/dma_safety_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/dma/dma_safety_gate_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the direct DMA path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/dma/dma_safety_gate_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps framebuffer fallback diagnostic-only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/dma/dma_safety_gate_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts SR-IOV hardening only with IOMMU isolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

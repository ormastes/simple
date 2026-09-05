# Resource Grant Specification

> Tests covering driver supervisor resource grants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Grant Specification

## Scenarios

### driver supervisor resource grants

#### rejects zero token BAR IRQ and DMA grants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects zero token BAR IRQ and DMA grants
   - Expected: bar.grant(0, 0xFEB90000, 4096, true, false) equals `error: invalid token`
   - Expected: bar.has_issued_token() is false
   - Expected: bar.grant(10, 0xFEB90000, 0, true, false) equals `error: invalid size`
   - Expected: bar.grant(10, 0xFEB90000, 4096, true, false) equals `ok`
   - Expected: bar.has_issued_token() is true
   - Expected: irq.grant(0) equals `error: invalid token`
   - Expected: irq.has_issued_token() is false
   - Expected: irq.grant(11) equals `ok`
   - Expected: irq.has_issued_token() is true
   - Expected: dma.grant(0, 0x100000, 0x200000) equals `error: invalid token`
   - Expected: dma.has_issued_token() is false
   - Expected: dma.grant(12, 0x100000, 0x200000) equals `ok`
   - Expected: dma.has_issued_token() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects zero token BAR IRQ and DMA grants")
var bar = BarGrant.request(0, 2, 0, 0)
expect(bar.grant(0, 0xFEB90000, 4096, true, false)).to_equal("error: invalid token")
expect(bar.has_issued_token()).to_equal(false)
expect(bar.grant(10, 0xFEB90000, 0, true, false)).to_equal("error: invalid size")
expect(bar.grant(10, 0xFEB90000, 4096, true, false)).to_equal("ok")
expect(bar.has_issued_token()).to_equal(true)

var irq = IrqGrant.request_legacy(11, 42)
expect(irq.grant(0)).to_equal("error: invalid token")
expect(irq.has_issued_token()).to_equal(false)
expect(irq.grant(11)).to_equal("ok")
expect(irq.has_issued_token()).to_equal(true)

var dma = DmaGrant.request(8192, "bidirectional", 7)
expect(dma.grant(0, 0x100000, 0x200000)).to_equal("error: invalid token")
expect(dma.has_issued_token()).to_equal(false)
expect(dma.grant(12, 0x100000, 0x200000)).to_equal("ok")
expect(dma.has_issued_token()).to_equal(true)
```

</details>

#### does not grant a resource set from a placeholder base token

- does not grant a resource set from a placeholder base token
   - Expected: grants.add_bar(0) equals `added bar slot 0`
   - Expected: grants.add_irq(11) equals `added irq slot 0`
   - Expected: grants.add_dma(8192) equals `added dma slot 0`
   - Expected: grants.grant_all(0) equals `0`
   - Expected: grants.all_granted_with_tokens() is false
   - Expected: grants.grant_all(100) equals `3`
   - Expected: grants.all_granted_with_tokens() is true
   - Expected: grants.b0_token equals `100`
   - Expected: grants.i0_token equals `101`
   - Expected: grants.d0_token equals `102`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not grant a resource set from a placeholder base token")
var grants = ResourceGrantSet.create("nvme-user", 77)
expect(grants.add_bar(0)).to_equal("added bar slot 0")
expect(grants.add_irq(11)).to_equal("added irq slot 0")
expect(grants.add_dma(8192)).to_equal("added dma slot 0")
expect(grants.grant_all(0)).to_equal(0)
expect(grants.all_granted_with_tokens()).to_equal(false)

expect(grants.grant_all(100)).to_equal(3)
expect(grants.all_granted_with_tokens()).to_equal(true)
expect(grants.b0_token).to_equal(100)
expect(grants.i0_token).to_equal(101)
expect(grants.d0_token).to_equal(102)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/services/driver_supervisor/resource_grant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver supervisor resource grants.
- driver supervisor resource grants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `913028e086d51b7354736d32f9fc51a9e715baaa6b5806c0523ab2bb55080ee4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `913028e086d51b7354736d32f9fc51a9e715baaa6b5806c0523ab2bb55080ee4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `913028e086d51b7354736d32f9fc51a9e715baaa6b5806c0523ab2bb55080ee4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/services/driver_supervisor/resource_grant_spec.spl
mirror: doc/06_spec/unit/os/services/driver_supervisor/resource_grant_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/driver_supervisor/resource_grant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/driver_supervisor/resource_grant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/driver_supervisor/resource_grant_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/services/driver_supervisor/resource_grant_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects zero token BAR IRQ and DMA grants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/driver_supervisor/resource_grant_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not grant a resource set from a placeholder base token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

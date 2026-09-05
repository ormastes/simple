# Grant Broker Specification

> Tests covering driver supervisor grant broker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grant Broker Specification

## Scenarios

### driver supervisor grant broker

#### does not issue grants when the broker token cursor is invalid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not issue grants when the broker token cursor is invalid
   - Expected: broker.register_driver("nvme-user", 42) equals ``
   - Expected: broker.grant_bar("nvme-user", 0) equals `0`
   - Expected: broker.grant_irq("nvme-user", 11) equals `0`
   - Expected: broker.grant_dma("nvme-user", 8192) equals `0`
   - Expected: broker.g0_bar_count equals `0`
   - Expected: broker.g0_irq_count equals `0`
   - Expected: broker.g0_dma_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not issue grants when the broker token cursor is invalid")
var broker = GrantBroker.create()
expect(broker.register_driver("nvme-user", 42)).to_equal("")
broker.next_token = 0
expect(broker.grant_bar("nvme-user", 0)).to_equal(0)
expect(broker.grant_irq("nvme-user", 11)).to_equal(0)
expect(broker.grant_dma("nvme-user", 8192)).to_equal(0)
expect(broker.g0_bar_count).to_equal(0)
expect(broker.g0_irq_count).to_equal(0)
expect(broker.g0_dma_count).to_equal(0)
```

</details>

#### rejects raw passthrough without issued broker tokens

- rejects raw passthrough without issued broker tokens
   - Expected: grant.grant_passthrough(0) equals `error: invalid broker token`
   - Expected: grant.has_issued_tokens() is false
   - Expected: grant.grant_passthrough(30) equals `passthrough granted tok=30`
   - Expected: grant.has_issued_tokens() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects raw passthrough without issued broker tokens")
var grant = RawDeviceGrant.request(0, 2, 0, 77)
expect(grant.grant_passthrough(0)).to_equal("error: invalid broker token")
expect(grant.has_issued_tokens()).to_equal(false)
expect(grant.grant_passthrough(30)).to_equal("passthrough granted tok=30")
expect(grant.has_issued_tokens()).to_equal(true)
```

</details>

#### requires a positive broker token for exokernel lane readiness

- requires a positive broker token for exokernel lane readiness
   - Expected: lane.is_ready() is false
   - Expected: lane.is_ready() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a positive broker token for exokernel lane readiness")
var lane = ExokernelLaneStatus.create()
lane.has_contract = true
lane.has_tests = true
lane.has_docs = true
lane.has_reviewer = true
lane.bar_ready = true
lane.irq_ready = true
lane.dma_ready = true
lane.iommu_ready = true
lane.broker_ready = true
lane.broker_token = 0
expect(lane.is_ready()).to_equal(false)
expect(lane.report()).to_contain("broker_tok=0")
lane.broker_token = 30
expect(lane.is_ready()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/services/driver_supervisor/grant_broker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver supervisor grant broker.
- driver supervisor grant broker

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5fbc2165332b01fbc2e8358dcfe846ddbcf86b09e403e5bdf4e9350eda8afb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5fbc2165332b01fbc2e8358dcfe846ddbcf86b09e403e5bdf4e9350eda8afb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5fbc2165332b01fbc2e8358dcfe846ddbcf86b09e403e5bdf4e9350eda8afb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/services/driver_supervisor/grant_broker_spec.spl
mirror: doc/06_spec/unit/os/services/driver_supervisor/grant_broker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/driver_supervisor/grant_broker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/driver_supervisor/grant_broker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/driver_supervisor/grant_broker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/services/driver_supervisor/grant_broker_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not issue grants when the broker token cursor is invalid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/driver_supervisor/grant_broker_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects raw passthrough without issued broker tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/driver_supervisor/grant_broker_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a positive broker token for exokernel lane readiness' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

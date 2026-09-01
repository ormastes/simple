# Simple Device Event Specification

> Tests covering shared device event ring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Device Event Specification

## Scenarios

### shared device event ring

#### orders timestamps and assigns stable sequence numbers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- orders timestamps and assigns stable sequence numbers
   - Expected: events.publish(20u64, 1u64, 4, 2, 9u64, "audio-submit", "submitted") equals `published`
   - Expected: events.publish(10u64, 2u64, 4, 2, 10u64, "audio-period", "completed") equals `published`
   - Expected: drained.len() equals `2`
   - Expected: drained[0].sequence equals `1u64`
   - Expected: drained[1].sequence equals `2u64`
   - Expected: drained[1].monotonic_ns equals `20u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("orders timestamps and assigns stable sequence numbers")
var events = SimpleDeviceEventRing.create(3)
expect(events.publish(20u64, 1u64, 4, 2, 9u64, "audio-submit", "submitted")).to_equal("published")
expect(events.publish(10u64, 2u64, 4, 2, 10u64, "audio-period", "completed")).to_equal("published")
val drained = events.drain()
expect(drained.len()).to_equal(2)
expect(drained[0].sequence).to_equal(1u64)
expect(drained[1].sequence).to_equal(2u64)
expect(drained[1].monotonic_ns).to_equal(20u64)
```

</details>

#### bounds capacity and fails closed after shutdown

- bounds capacity and fails closed after shutdown
   - Expected: events.publish(1u64, 0u64, 1, 1, 1u64, "one", "ready") equals `published`
   - Expected: events.publish(2u64, 0u64, 1, 1, 2u64, "two", "ready") equals `published`
   - Expected: events.publish(3u64, 0u64, 1, 1, 3u64, "three", "ready") equals `queue-full`
   - Expected: events.shutdown(4u64, 1) equals `completed`
   - Expected: events.publish(5u64, 0u64, 1, 1, 4u64, "late", "ready") equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds capacity and fails closed after shutdown")
var events = SimpleDeviceEventRing.create(2)
expect(events.publish(1u64, 0u64, 1, 1, 1u64, "one", "ready")).to_equal("published")
expect(events.publish(2u64, 0u64, 1, 1, 2u64, "two", "ready")).to_equal("published")
expect(events.publish(3u64, 0u64, 1, 1, 3u64, "three", "ready")).to_equal("queue-full")
expect(events.shutdown(4u64, 1)).to_equal("completed")
expect(events.publish(5u64, 0u64, 1, 1, 4u64, "late", "ready")).to_equal("shutdown")
```

</details>

#### clamps unsafe capacities and records shutdown when space remains

- clamps unsafe capacities and records shutdown when space remains
   - Expected: events.capacity equals `2`
   - Expected: events.shutdown(7u64, 8) equals `completed`
   - Expected: drained.len() equals `1`
   - Expected: drained[0].kind equals `shutdown`
   - Expected: drained[0].device_id equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps unsafe capacities and records shutdown when space remains")
var events = SimpleDeviceEventRing.create(0)
expect(events.capacity).to_equal(2)
expect(events.shutdown(7u64, 8)).to_equal("completed")
val drained = events.drain()
expect(drained.len()).to_equal(1)
expect(drained[0].kind).to_equal("shutdown")
expect(drained[0].device_id).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/io/simple_device_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared device event ring.
- shared device event ring

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

- Canonical SPipe generation for source `4fb23de67a91f0501ded40332ed04420592aa1090cf020b53189e113149fa9ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fb23de67a91f0501ded40332ed04420592aa1090cf020b53189e113149fa9ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fb23de67a91f0501ded40332ed04420592aa1090cf020b53189e113149fa9ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/io/simple_device_event_spec.spl
mirror: doc/06_spec/01_unit/lib/common/io/simple_device_event_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/io/simple_device_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/io/simple_device_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/io/simple_device_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/io/simple_device_event_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders timestamps and assigns stable sequence numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/io/simple_device_event_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds capacity and fails closed after shutdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/io/simple_device_event_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps unsafe capacities and records shutdown when space remains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

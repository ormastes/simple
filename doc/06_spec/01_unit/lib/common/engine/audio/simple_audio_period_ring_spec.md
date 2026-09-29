# Simple Audio Period Ring Specification

> Tests covering bounded audio period ring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Audio Period Ring Specification

## Scenarios

### bounded audio period ring

#### clamps capacity and cycles one period through device ownership

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clamps capacity and cycles one period through device ownership
   - Expected: ring.capacity equals `2`
   - Expected: ring.prepare(0, 7u64, 11u64) equals `prepared`
   - Expected: ring.submit(0, 7u64) equals `submitted`
   - Expected: ring.complete(0, 7u64) equals `completed`
   - Expected: ring.release(0, 7u64) equals `released`
   - Expected: ring.live_count equals `0`
   - Expected: ring.high_water equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps capacity and cycles one period through device ownership")
var ring = SimpleAudioPeriodRing.create(1)
expect(ring.capacity).to_equal(2)
expect(ring.prepare(0, 7u64, 11u64)).to_equal("prepared")
expect(ring.submit(0, 7u64)).to_equal("submitted")
expect(ring.complete(0, 7u64)).to_equal("completed")
expect(ring.release(0, 7u64)).to_equal("released")
expect(ring.live_count).to_equal(0)
expect(ring.high_water).to_equal(1)
```

</details>

#### rejects invalid indices state transitions and stale generations

- rejects invalid indices state transitions and stale generations
   - Expected: ring.prepare(-1, 1u64, 1u64) equals `invalid-index`
   - Expected: ring.submit(0, 1u64) equals `stale-generation`
   - Expected: ring.prepare(0, 2u64, 1u64) equals `prepared`
   - Expected: ring.prepare(0, 2u64, 2u64) equals `invalid-state`
   - Expected: ring.submit(0, 1u64) equals `stale-generation`
   - Expected: ring.complete(0, 2u64) equals `invalid-state`
   - Expected: ring.cancel(0, 2u64) equals `cancelled`
   - Expected: ring.cancel(0, 3u64) equals `invalid-state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid indices state transitions and stale generations")
var ring = SimpleAudioPeriodRing.create(4)
expect(ring.prepare(-1, 1u64, 1u64)).to_equal("invalid-index")
expect(ring.submit(0, 1u64)).to_equal("stale-generation")
expect(ring.prepare(0, 2u64, 1u64)).to_equal("prepared")
expect(ring.prepare(0, 2u64, 2u64)).to_equal("invalid-state")
expect(ring.submit(0, 1u64)).to_equal("stale-generation")
expect(ring.complete(0, 2u64)).to_equal("invalid-state")
expect(ring.cancel(0, 2u64)).to_equal("cancelled")
expect(ring.cancel(0, 3u64)).to_equal("invalid-state")
```

</details>

#### tracks high water and cancels all live periods on shutdown

- tracks high water and cancels all live periods on shutdown
   - Expected: ring.capacity equals `64`
   - Expected: ring.prepare(0, 1u64, 1u64) equals `prepared`
   - Expected: ring.prepare(1, 1u64, 2u64) equals `prepared`
   - Expected: ring.submit(1, 1u64) equals `submitted`
   - Expected: ring.high_water equals `2`
   - Expected: ring.shutdown() equals `2`
   - Expected: ring.live_count equals `0`
   - Expected: ring.states[0] equals `free`
   - Expected: ring.states[1] equals `free`
   - Expected: ring.prepare(0, 3u64, 3u64) equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tracks high water and cancels all live periods on shutdown")
var ring = SimpleAudioPeriodRing.create(100)
expect(ring.capacity).to_equal(64)
expect(ring.prepare(0, 1u64, 1u64)).to_equal("prepared")
expect(ring.prepare(1, 1u64, 2u64)).to_equal("prepared")
expect(ring.submit(1, 1u64)).to_equal("submitted")
expect(ring.high_water).to_equal(2)
expect(ring.shutdown()).to_equal(2)
expect(ring.live_count).to_equal(0)
expect(ring.states[0]).to_equal("free")
expect(ring.states[1]).to_equal("free")
expect(ring.prepare(0, 3u64, 3u64)).to_equal("shutdown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded audio period ring.
- bounded audio period ring

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
- `REQ-003`
- `REQ-005`
- `REQ-008`
- `REQ-014`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d70c36bbf24192ce59b4347e768f0991a4ac43948e9ff5e7a60ae6d94fe8631c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d70c36bbf24192ce59b4347e768f0991a4ac43948e9ff5e7a60ae6d94fe8631c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d70c36bbf24192ce59b4347e768f0991a4ac43948e9ff5e7a60ae6d94fe8631c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl
mirror: doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps capacity and cycles one period through device ownership' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid indices state transitions and stale generations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/engine/audio/simple_audio_period_ring_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks high water and cancels all live periods on shutdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

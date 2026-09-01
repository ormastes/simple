# Async Trace Ring Specification

> Tests covering bounded single-owner async trace ring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Trace Ring Specification

## Scenarios

### bounded single-owner async trace ring

#### rejects invalid creation arguments with exact errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(AsyncTraceRing.create(
    0u64, 2, AsyncTraceFullPolicy.RejectNewest
)).to_equal(Err(AsyncTraceRingError.InvalidOwner))
expect(AsyncTraceRing.create(
    1u64, 0, AsyncTraceFullPolicy.RejectNewest
)).to_equal(Err(AsyncTraceRingError.InvalidCapacity))
expect(AsyncTraceRing.create(
    1u64, -1, AsyncTraceFullPolicy.DropOldest
)).to_equal(Err(AsyncTraceRingError.InvalidCapacity))
```

</details>

#### requires the owner to seal once and reports honest evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = match AsyncTraceRing.create(
    41u64, 3, AsyncTraceFullPolicy.RejectNewest
):
    case Ok(value): value
    case Err(_): panic("create failed")
expect(ring.phase()).to_equal(AsyncTraceRingPhase.Configuring)
expect(ring.seal(9u64)).to_equal(Err(AsyncTraceRingError.WrongOwner))
val receipt = match ring.seal(41u64):
    case Ok(value): value
    case Err(_): panic("seal failed")
expect(receipt.owner_id).to_equal(41u64)
expect(receipt.capacity).to_equal(3u64)
expect(receipt.hosted_preallocated).to_be(true)
expect(receipt.link_time_static_proven).to_be(false)
expect(ring.phase()).to_equal(AsyncTraceRingPhase.Ready)
expect(ring.seal(41u64)).to_equal(Err(AsyncTraceRingError.AlreadyReady))
```

</details>

#### rejects append and take before Ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = match AsyncTraceRing.create(
    41u64, 2, AsyncTraceFullPolicy.RejectNewest
):
    case Ok(value): value
    case Err(_): panic("create failed")
expect(ring.append(41u64, trace_event(1u64))).to_equal(
    Err(AsyncTraceRingError.NotReady))
expect(ring.take(41u64)).to_equal(Err(AsyncTraceRingError.NotReady))
```

</details>

#### enforces one owner for every runtime operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(2, AsyncTraceFullPolicy.RejectNewest)
expect(ring.append(99u64, trace_event(1u64))).to_equal(
    Err(AsyncTraceRingError.WrongOwner))
expect(ring.take(99u64)).to_equal(Err(AsyncTraceRingError.WrongOwner))
expect(ring.occupancy()).to_equal(0u64)
```

</details>

#### rejects malformed canonical events without changing occupancy

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(2, AsyncTraceFullPolicy.RejectNewest)
var missing_task = trace_event(1u64)
missing_task.task_id = 0u64
expect(ring.append(41u64, missing_task)).to_equal(
    Err(AsyncTraceRingError.InvalidEvent(RingContractError.InvalidTaskFrame)))
var stale_token = trace_event(2u64)
stale_token.operation_token = RingToken(
    ring_id: 7u64, slot: 1u64,
    generation: RingGeneration(value: 0u64))
expect(ring.append(41u64, stale_token)).to_equal(
    Err(AsyncTraceRingError.InvalidEvent(RingContractError.InvalidGeneration)))
expect(ring.occupancy()).to_equal(0u64)
```

</details>

#### preserves FIFO order through cursor wrap without scanning

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(3, AsyncTraceFullPolicy.RejectNewest)
expect(ring.append(41u64, trace_event(1u64))).to_equal(
    Ok(AsyncTraceAppendOutcome.Appended))
expect(ring.append(41u64, trace_event(2u64))).to_equal(
    Ok(AsyncTraceAppendOutcome.Appended))
val first = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
expect(first?.sequence).to_equal(1u64)
expect(ring.append(41u64, trace_event(3u64))).to_equal(
    Ok(AsyncTraceAppendOutcome.Appended))
expect(ring.append(41u64, trace_event(4u64))).to_equal(
    Ok(AsyncTraceAppendOutcome.Appended))
val second = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
val third = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
val fourth = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
expect(second?.sequence).to_equal(2u64)
expect(third?.sequence).to_equal(3u64)
expect(fourth?.sequence).to_equal(4u64)
expect(ring.take(41u64)).to_equal(Ok(nil))
```

</details>

#### reject-newest policy keeps admitted data and records full drop telemetry

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(2, AsyncTraceFullPolicy.RejectNewest)
ring.append(41u64, trace_event(1u64))
ring.append(41u64, trace_event(2u64))
expect(ring.append(41u64, trace_event(3u64))).to_equal(
    Err(AsyncTraceRingError.Full))
val telemetry = ring.telemetry()
expect(telemetry.occupancy).to_equal(2u64)
expect(telemetry.high_water).to_equal(2u64)
expect(telemetry.appended).to_equal(2u64)
expect(telemetry.full_events).to_equal(1u64)
expect(telemetry.dropped_events).to_equal(1u64)
val first = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
expect(first?.sequence).to_equal(1u64)
```

</details>

#### drop-oldest policy replaces exactly one event and preserves order

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(2, AsyncTraceFullPolicy.DropOldest)
ring.append(41u64, trace_event(1u64))
ring.append(41u64, trace_event(2u64))
expect(ring.append(41u64, trace_event(3u64))).to_equal(
    Ok(AsyncTraceAppendOutcome.ReplacedOldest))
val first = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
val second = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
expect(first?.sequence).to_equal(2u64)
expect(second?.sequence).to_equal(3u64)
val telemetry = ring.telemetry()
expect(telemetry.full_events).to_equal(1u64)
expect(telemetry.dropped_events).to_equal(1u64)
expect(telemetry.appended).to_equal(3u64)
expect(telemetry.taken).to_equal(2u64)
expect(telemetry.occupancy).to_equal(0u64)
```

</details>

#### capacity one repeatedly wraps while keeping bounded telemetry

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ring = ready_ring(1, AsyncTraceFullPolicy.DropOldest)
ring.append(41u64, trace_event(1u64))
ring.append(41u64, trace_event(2u64))
ring.append(41u64, trace_event(3u64))
val last = match ring.take(41u64):
    case Ok(value): value
    case Err(_): panic("take failed")
expect(last?.sequence).to_equal(3u64)
val telemetry = ring.telemetry()
expect(telemetry.high_water).to_equal(1u64)
expect(telemetry.full_events).to_equal(2u64)
expect(telemetry.dropped_events).to_equal(2u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded single-owner async trace ring.
- bounded single-owner async trace ring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f1bec272b8f8a6ca6a317fbc694577abdf93f29525012ea4408aa200cfccb26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f1bec272b8f8a6ca6a317fbc694577abdf93f29525012ea4408aa200cfccb26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f1bec272b8f8a6ca6a317fbc694577abdf93f29525012ea4408aa200cfccb26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects invalid creation arguments with exact errors' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:48:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'requires the owner to seal once and reports honest evidence' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects append and take before Ready' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_async_mut_noalloc/async/async_trace_ring_spec.spl:76:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'enforces one owner for every runtime operation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

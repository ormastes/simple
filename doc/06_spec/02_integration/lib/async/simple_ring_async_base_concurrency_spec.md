# Simple Ring Async Base Concurrency Specification

> Tests covering SimpleRing deterministic concurrency interleavings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Async Base Concurrency Specification

## Scenarios

### SimpleRing deterministic concurrency interleavings

#### lets an independent ring finish while another ring remains in flight

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lets an independent ring finish while another ring remains in flight
   - Expected: fast_completion.task_key equals `8201u64`
   - Expected: slow_ring.occupancy() equals `1u64`
   - Expected: slow_completion.task_key equals `8101u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("lets an independent ring finish while another ring remains in flight")
val slow_ring = match SimpleRing<text, text>.create(801u64, 81u64, 1):
    case Ok(value): value
    case Err(_): fail("slow ring construction failed")
val fast_ring = match SimpleRing<text, text>.create(802u64, 82u64, 1):
    case Ok(value): value
    case Err(_): fail("fast ring construction failed")
val slow_provider = match SoftwareRingProvider<text, text>.create(901u64, 1):
    case Ok(value): value
    case Err(_): fail("slow provider construction failed")
val fast_provider = match SoftwareRingProvider<text, text>.create(902u64, 1):
    case Ok(value): value
    case Err(_): fail("fast provider construction failed")

val slow_reservation = match slow_ring.reserve(81u64, 8101u64):
    case Ok(value): value
    case Err(_): fail("slow reservation failed")
val fast_reservation = match fast_ring.reserve(82u64, 8201u64):
    case Ok(value): value
    case Err(_): fail("fast reservation failed")
match slow_ring.commit(81u64, slow_reservation, "slow"):
    case Ok(_): ()
    case Err(_): fail("slow commit failed")
match fast_ring.commit(82u64, fast_reservation, "fast"):
    case Ok(_): ()
    case Err(_): fail("fast commit failed")
val slow_submission = match slow_provider.take_one(slow_ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("slow submission missing")
    case Err(_): fail("slow take failed")
val fast_submission = match fast_provider.take_one(fast_ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("fast submission missing")
    case Err(_): fail("fast take failed")

match fast_provider.complete_success(fast_ring, fast_submission, "fast-done"):
    case Ok(wake): expect(wake.wake_key).to_equal(8201u64)
    case Err(_): fail("fast completion failed")
val fast_completion = match fast_ring.take_completion(82u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("fast completion missing")
    case Err(_): fail("fast completion take failed")
expect(fast_completion.task_key).to_equal(8201u64)
expect(slow_ring.occupancy()).to_equal(1u64)
match slow_ring.take_completion(81u64):
    case Ok(nil): ()
    case Ok(Some(_)): fail("slow ring completed without provider publication")
    case Err(_): fail("slow empty completion check failed")

match slow_provider.complete_success(slow_ring, slow_submission, "slow-done"):
    case Ok(wake): expect(wake.wake_key).to_equal(8101u64)
    case Err(_): fail("slow completion failed")
val slow_completion = match slow_ring.take_completion(81u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("slow completion missing")
    case Err(_): fail("slow completion take failed")
expect(slow_completion.task_key).to_equal(8101u64)
```

</details>

#### keeps exact wake keys under an interleaved completion order

- keeps exact wake keys under an interleaved completion order
   - Expected: completion_two.task_key equals `8302u64`
   - Expected: completion_one.task_key equals `8301u64`
   - Expected: completion_three.task_key equals `8303u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps exact wake keys under an interleaved completion order")
val ring = match SimpleRing<i64, i64>.create(803u64, 83u64, 3):
    case Ok(value): value
    case Err(_): fail("wake ring construction failed")
val provider = match SoftwareRingProvider<i64, i64>.create(903u64, 3):
    case Ok(value): value
    case Err(_): fail("wake provider construction failed")
val first = match ring.reserve(83u64, 8301u64):
    case Ok(value): value
    case Err(_): fail("first wake reservation failed")
val second = match ring.reserve(83u64, 8302u64):
    case Ok(value): value
    case Err(_): fail("second wake reservation failed")
val third = match ring.reserve(83u64, 8303u64):
    case Ok(value): value
    case Err(_): fail("third wake reservation failed")
match ring.commit(83u64, first, 1):
    case Ok(_): ()
    case Err(_): fail("first wake commit failed")
match ring.commit(83u64, second, 2):
    case Ok(_): ()
    case Err(_): fail("second wake commit failed")
match ring.commit(83u64, third, 3):
    case Ok(_): ()
    case Err(_): fail("third wake commit failed")
val submission_one = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("first wake submission missing")
    case Err(_): fail("first wake take failed")
val submission_two = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("second wake submission missing")
    case Err(_): fail("second wake take failed")
val submission_three = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("third wake submission missing")
    case Err(_): fail("third wake take failed")

match provider.complete_success(ring, submission_two, 20):
    case Ok(wake): expect(wake.wake_key).to_equal(8302u64)
    case Err(_): fail("second interleaved completion failed")
match provider.complete_success(ring, submission_one, 10):
    case Ok(wake): expect(wake.wake_key).to_equal(8301u64)
    case Err(_): fail("first interleaved completion failed")
match provider.complete_success(ring, submission_three, 30):
    case Ok(wake): expect(wake.wake_key).to_equal(8303u64)
    case Err(_): fail("third interleaved completion failed")
val completion_two = match ring.take_completion(83u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("second interleaved result missing")
    case Err(_): fail("second interleaved result failed")
val completion_one = match ring.take_completion(83u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("first interleaved result missing")
    case Err(_): fail("first interleaved result failed")
val completion_three = match ring.take_completion(83u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("third interleaved result missing")
    case Err(_): fail("third interleaved result failed")
expect(completion_two.task_key).to_equal(8302u64)
expect(completion_one.task_key).to_equal(8301u64)
expect(completion_three.task_key).to_equal(8303u64)
```

</details>

#### reports bounded saturation and admits again only after terminal consumption

- reports bounded saturation and admits again only after terminal consumption
   - Expected: ring.telemetry().full_events equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports bounded saturation and admits again only after terminal consumption")
val ring = match SimpleRing<i64, i64>.create(804u64, 84u64, 1):
    case Ok(value): value
    case Err(_): fail("bounded ring construction failed")
val provider = match SoftwareRingProvider<i64, i64>.create(904u64, 1):
    case Ok(value): value
    case Err(_): fail("bounded provider construction failed")
val reservation = match ring.reserve(84u64, 8401u64):
    case Ok(value): value
    case Err(_): fail("bounded reservation failed")
match ring.reserve(84u64, 8402u64):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("saturated ring admitted a second reservation")
match ring.commit(84u64, reservation, 41):
    case Ok(_): ()
    case Err(_): fail("bounded commit failed")
val submission = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("bounded submission missing")
    case Err(_): fail("bounded take failed")
match provider.complete_success(ring, submission, 42):
    case Ok(_): ()
    case Err(_): fail("bounded completion failed")
match ring.reserve(84u64, 8402u64):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("terminal result was overwritten before consumption")
match ring.take_completion(84u64):
    case Ok(Some(value)): expect(value.task_key).to_equal(8401u64)
    case Ok(nil): fail("bounded terminal result missing")
    case Err(_): fail("bounded terminal result take failed")
match ring.reserve(84u64, 8402u64):
    case Ok(_): ()
    case Err(_): fail("released slot was not admitted again")
expect(ring.telemetry().full_events).to_equal(2u64)
```

</details>

#### rejects a completion from the generation invalidated by reset

- rejects a completion from the generation invalidated by reset
   - Expected: ring.telemetry().stale_rejects equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a completion from the generation invalidated by reset")
val ring = match SimpleRing<text, text>.create(805u64, 85u64, 1):
    case Ok(value): value
    case Err(_): fail("reset ring construction failed")
val provider = match SoftwareRingProvider<text, text>.create(905u64, 1):
    case Ok(value): value
    case Err(_): fail("reset provider construction failed")
val reservation = match ring.reserve(85u64, 8501u64):
    case Ok(value): value
    case Err(_): fail("reset reservation failed")
match ring.commit(85u64, reservation, "old-generation"):
    case Ok(_): ()
    case Err(_): fail("reset commit failed")
val stale_submission = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("reset submission missing")
    case Err(_): fail("reset take failed")
match ring.reset(85u64):
    case Ok(receipt): expect(receipt.invalidated).to_equal(1u64)
    case Err(_): fail("ring reset failed")
match provider.complete_success(ring, stale_submission, "late"):
    case Err(error): expect(error).to_equal(SimpleRingError.StaleToken)
    case Ok(_): fail("stale generation published a completion")
match ring.take_completion(85u64):
    case Ok(nil): ()
    case Ok(Some(_)): fail("reset retained a stale completion")
    case Err(_): fail("reset completion check failed")
expect(ring.telemetry().stale_rejects).to_equal(1u64)
```

</details>

#### makes cancellation terminal once and rejects duplicate publication

- makes cancellation terminal once and rejects duplicate publication
   - Expected: token.generation.value equals `reserved.token.generation.value`
   - Expected: token.generation.value equals `active_token.generation.value`
   - Expected: completion.task_key equals `8602u64`
   - Expected: completion.kind equals `RingTerminalKind.Cancelled`
   - Expected: ring.telemetry().duplicate_rejects equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("makes cancellation terminal once and rejects duplicate publication")
val ring = match SimpleRing<text, text>.create(806u64, 86u64, 2):
    case Ok(value): value
    case Err(_): fail("cancel ring construction failed")
val provider = match SoftwareRingProvider<text, text>.create(906u64, 2):
    case Ok(value): value
    case Err(_): fail("cancel provider construction failed")
val reserved = match ring.reserve(86u64, 8601u64):
    case Ok(value): value
    case Err(_): fail("precommit cancellation reservation failed")
match ring.cancel(86u64, reserved.token):
    case RingCancelOutcome.CancelledBeforeCommit(token):
        expect(token.generation.value).to_equal(reserved.token.generation.value)
    case _: fail("reserved work did not cancel before commit")

val active = match ring.reserve(86u64, 8602u64):
    case Ok(value): value
    case Err(_): fail("active cancellation reservation failed")
val active_token = match ring.commit(86u64, active, "active"):
    case Ok(value): value
    case Err(_): fail("active cancellation commit failed")
val submission = match provider.take_one(ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("active cancellation submission missing")
    case Err(_): fail("active cancellation take failed")
match ring.cancel(86u64, active_token):
    case RingCancelOutcome.ProviderCancelRequested(token):
        expect(token.generation.value).to_equal(active_token.generation.value)
    case _: fail("in-flight cancellation was not routed to provider")
match provider.complete_cancelled(ring, submission, "cancel accepted"):
    case Ok(wake): expect(wake.wake_key).to_equal(8602u64)
    case Err(_): fail("cancel terminal publication failed")
match provider.complete_success(ring, submission, "duplicate"):
    case Err(error): expect(error).to_equal(SimpleRingError.TerminalAlreadyPublished)
    case Ok(_): fail("duplicate terminal publication succeeded")
match ring.cancel(86u64, active_token):
    case RingCancelOutcome.AlreadyTerminal(_): ()
    case _: fail("terminal cancellation state was not stable")
val completion = match ring.take_completion(86u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("cancel terminal result missing")
    case Err(_): fail("cancel terminal result take failed")
expect(completion.task_key).to_equal(8602u64)
expect(completion.kind).to_equal(RingTerminalKind.Cancelled)
expect(ring.telemetry().duplicate_rejects).to_equal(1u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing deterministic concurrency interleavings.
- SimpleRing deterministic concurrency interleavings

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `22fd28728fb383d549643c6c993551dff70df0d2e4ff6867a05ec6ac85307066`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22fd28728fb383d549643c6c993551dff70df0d2e4ff6867a05ec6ac85307066`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22fd28728fb383d549643c6c993551dff70df0d2e4ff6867a05ec6ac85307066`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl
mirror: doc/06_spec/02_integration/lib/async/simple_ring_async_base_concurrency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/async/simple_ring_async_base_concurrency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/async/simple_ring_async_base_concurrency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets an independent ring finish while another ring remains in flight' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps exact wake keys under an interleaved completion order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_async_base_concurrency_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports bounded saturation and admits again only after terminal consumption' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

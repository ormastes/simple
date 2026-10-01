# Simple Ring Async Base Integration Specification

> Tests covering SimpleRing software provider integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Async Base Integration Specification

## Scenarios

### SimpleRing software provider integration

#### records bounded provider kicks and caller-clock completion latency

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records bounded provider kicks and caller-clock completion latency
   - Expected: telemetry.completion_latency_samples equals `1u64`
   - Expected: telemetry.completion_latency_total equals `50u64`
   - Expected: telemetry.completion_latency_max equals `50u64`
   - Expected: provider.counters().kicks equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records bounded provider kicks and caller-clock completion latency")
val ring = match SimpleRing<i64, i64>.create(303u64, 33u64, 1):
    case Ok(value): value
    case Err(_): fail("timed ring construction failed")
val provider = match SoftwareRingProvider<i64, i64>.create(703u64, 1):
    case Ok(value): value
    case Err(_): fail("timed provider construction failed")
val held = match ring.reserve(33u64, 3001u64):
    case Ok(value): value
    case Err(_): fail("timed reservation failed")
match ring.commit(33u64, held, 7):
    case Ok(_): ()
    case Err(_): fail("timed commit failed")
val submission = match provider.take_one_at(ring, 100u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("timed submission missing")
    case Err(_): fail("timed take failed")
match provider.complete_success_at(ring, submission, 8, 99u64):
    case Err(error): expect(error).to_equal(SimpleRingError.InvalidTimestamp)
    case Ok(_): fail("backward completion timestamp accepted")
match provider.complete_success_at(ring, submission, 8, 150u64):
    case Ok(wake): expect(wake.wake_key).to_equal(3001u64)
    case Err(_): fail("timed completion failed")
val telemetry = ring.telemetry()
expect(telemetry.completion_latency_samples).to_equal(1u64)
expect(telemetry.completion_latency_total).to_equal(50u64)
expect(telemetry.completion_latency_max).to_equal(50u64)
expect(provider.counters().kicks).to_equal(1u64)
```

</details>

#### keeps typed rings bounded, FIFO, exactly woken, and independently progressing

- keeps typed rings bounded, FIFO, exactly woken, and independently progressing
   - Expected: common_admission.mapping equals `RingMappingGrade.Software`
   - Expected: common_admission.provider_depth equals `2`
   - Expected: common_admission.requested_depth equals `2`
   - Expected: common_admission.fallback_fact equals `software-grade-selected`
   - Expected: common_admission.fallback_reason equals `software ring provider selected`
   - Expected: depth_rejection.provider_depth equals `2`
   - Expected: depth_rejection.requested_depth equals `3`
   - Expected: mission_admission.fallback_reason equals `direct ring mapping required`
   - Expected: first_submission.operation equals `10`
   - Expected: first_submission.task_key equals `1001u64`
   - Expected: wake.wake_key equals `2001u64`
   - Expected: wake.kind equals `RingTerminalKind.Failure`
   - Expected: wake.wake_key equals `2002u64`
   - Expected: wake.kind equals `RingTerminalKind.Cancelled`
   - Expected: failure_completion.task_key equals `2001u64`
   - Expected: failure_completion.kind equals `RingTerminalKind.Failure`
   - Expected: failure_completion.error equals `device fault`
   - Expected: cancelled_completion.task_key equals `2002u64`
   - Expected: cancelled_completion.kind equals `RingTerminalKind.Cancelled`
   - Expected: cancelled_completion.error equals `caller cancelled`
   - Expected: second_submission.operation equals `20`
   - Expected: second_submission.task_key equals `1002u64`
   - Expected: wake.provider_id equals `701u64`
   - Expected: wake.wake_key equals `1001u64`
   - Expected: wake.kind equals `RingTerminalKind.Success`
   - Expected: first_completion.task_key equals `1001u64`
   - Expected: first_completion.kind equals `RingTerminalKind.Success`
   - Expected: value equals `first`
   - Expected: second_completion.task_key equals `1002u64`
   - Expected: second_completion.kind equals `RingTerminalKind.Success`
   - Expected: value equals `second`
   - Expected: primary_provider.counters().admissions equals `3u64`
   - Expected: primary_provider.counters().rejections equals `2u64`
   - Expected: primary_provider.counters().kicks equals `2u64`
   - Expected: primary_provider.counters().takes equals `2u64`
   - Expected: primary_provider.counters().successes equals `2u64`
   - Expected: primary_provider.counters().wakes equals `2u64`
   - Expected: secondary_provider.counters().takes equals `2u64`
   - Expected: secondary_provider.counters().kicks equals `2u64`
   - Expected: secondary_provider.counters().failures equals `1u64`
   - Expected: secondary_provider.counters().cancellations equals `1u64`
   - Expected: secondary_provider.counters().wakes equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 159 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps typed rings bounded, FIFO, exactly woken, and independently progressing")
val primary = match SimpleRing<i64, text>.create(101u64, 11u64, 2):
    case Ok(value): value
    case Err(_): fail("primary ring construction failed")
val primary_provider = match SoftwareRingProvider<i64, text>.create(701u64, 2):
    case Ok(value): value
    case Err(_): fail("primary provider construction failed")

val common_admission = primary_provider.admit(async_profile_common_v1())
match common_admission.status:
    case SoftwareProviderAdmissionStatus.Admitted:
        expect(common_admission.mapping).to_equal(RingMappingGrade.Software)
        expect(common_admission.bounded).to_be(true)
        expect(common_admission.provider_depth).to_equal(2)
        expect(common_admission.requested_depth).to_equal(2)
        expect(common_admission.fallback_fact).to_equal("software-grade-selected")
        expect(common_admission.fallback_reason).to_equal("software ring provider selected")
    case SoftwareProviderAdmissionStatus.Rejected: fail("common profile rejected")
val depth_rejection = primary_provider.admit_for_depth(async_profile_common_v1(), 3)
match depth_rejection.status:
    case SoftwareProviderAdmissionStatus.Rejected:
        expect(depth_rejection.fallback_reason).to_equal(
            "requested ring depth exceeds provider bound")
        expect(depth_rejection.provider_depth).to_equal(2)
        expect(depth_rejection.requested_depth).to_equal(3)
    case SoftwareProviderAdmissionStatus.Admitted:
        fail("provider admitted a ring deeper than its bound")
match primary_provider.admit(async_profile_script_v1()).status:
    case SoftwareProviderAdmissionStatus.Admitted: ()
    case SoftwareProviderAdmissionStatus.Rejected: fail("script profile rejected")
match primary_provider.admit(async_profile_server_v1()).status:
    case SoftwareProviderAdmissionStatus.Admitted: ()
    case SoftwareProviderAdmissionStatus.Rejected: fail("server profile rejected")
val mission_admission = primary_provider.admit(async_profile_mission_pool_v1())
match mission_admission.status:
    case SoftwareProviderAdmissionStatus.Rejected:
        expect(mission_admission.fallback_reason).to_equal("direct ring mapping required")
    case SoftwareProviderAdmissionStatus.Admitted: fail("direct-required mission profile admitted")

val first_reservation = match primary.reserve(11u64, 1001u64):
    case Ok(value): value
    case Err(_): fail("first primary reservation failed")
val second_reservation = match primary.reserve(11u64, 1002u64):
    case Ok(value): value
    case Err(_): fail("second primary reservation failed")
match primary.reserve(11u64, 1003u64):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("full primary ring admitted work")
match primary.commit(11u64, first_reservation, 10):
    case Ok(_): ()
    case Err(_): fail("first primary commit failed")
match primary.commit(11u64, second_reservation, 20):
    case Ok(_): ()
    case Err(_): fail("second primary commit failed")
val first_submission = match primary_provider.take_one(primary):
    case Ok(Some(value)): value
    case Ok(nil): fail("first primary submission missing")
    case Err(_): fail("first primary take failed")
expect(first_submission.operation).to_equal(10)
expect(first_submission.task_key).to_equal(1001u64)

val secondary = match SimpleRing<text, i64>.create(202u64, 22u64, 2):
    case Ok(value): value
    case Err(_): fail("secondary ring construction failed")
val secondary_provider = match SoftwareRingProvider<text, i64>.create(702u64, 2):
    case Ok(value): value
    case Err(_): fail("secondary provider construction failed")
val failure_reservation = match secondary.reserve(22u64, 2001u64):
    case Ok(value): value
    case Err(_): fail("failure reservation failed")
val cancelled_reservation = match secondary.reserve(22u64, 2002u64):
    case Ok(value): value
    case Err(_): fail("cancelled reservation failed")
match secondary.commit(22u64, failure_reservation, "fail"):
    case Ok(_): ()
    case Err(_): fail("failure commit failed")
match secondary.commit(22u64, cancelled_reservation, "cancel"):
    case Ok(_): ()
    case Err(_): fail("cancelled commit failed")
val failure_submission = match secondary_provider.take_one(secondary):
    case Ok(Some(value)): value
    case Ok(nil): fail("failure submission missing")
    case Err(_): fail("failure take failed")
match secondary_provider.complete_failure(secondary, failure_submission, "device fault"):
    case Ok(wake):
        expect(wake.wake_key).to_equal(2001u64)
        expect(wake.kind).to_equal(RingTerminalKind.Failure)
    case Err(_): fail("failure completion failed")
val cancelled_submission = match secondary_provider.take_one(secondary):
    case Ok(Some(value)): value
    case Ok(nil): fail("cancelled submission missing")
    case Err(_): fail("cancelled take failed")
match secondary_provider.complete_cancelled(secondary, cancelled_submission, "caller cancelled"):
    case Ok(wake):
        expect(wake.wake_key).to_equal(2002u64)
        expect(wake.kind).to_equal(RingTerminalKind.Cancelled)
    case Err(_): fail("cancelled completion failed")
val failure_completion = match secondary.take_completion(22u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("failure completion missing")
    case Err(_): fail("failure completion take failed")
expect(failure_completion.task_key).to_equal(2001u64)
expect(failure_completion.kind).to_equal(RingTerminalKind.Failure)
expect(failure_completion.error).to_equal("device fault")
val cancelled_completion = match secondary.take_completion(22u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("cancelled completion missing")
    case Err(_): fail("cancelled completion take failed")
expect(cancelled_completion.task_key).to_equal(2002u64)
expect(cancelled_completion.kind).to_equal(RingTerminalKind.Cancelled)
expect(cancelled_completion.error).to_equal("caller cancelled")

val second_submission = match primary_provider.take_one(primary):
    case Ok(Some(value)): value
    case Ok(nil): fail("second primary submission missing")
    case Err(_): fail("second primary take failed")
expect(second_submission.operation).to_equal(20)
expect(second_submission.task_key).to_equal(1002u64)
match primary_provider.complete_success(primary, first_submission, "first"):
    case Ok(wake):
        expect(wake.provider_id).to_equal(701u64)
        expect(wake.wake_key).to_equal(1001u64)
        expect(wake.kind).to_equal(RingTerminalKind.Success)
    case Err(_): fail("first success completion failed")
match primary_provider.complete_success(primary, second_submission, "second"):
    case Ok(wake): expect(wake.wake_key).to_equal(1002u64)
    case Err(_): fail("second success completion failed")
val first_completion = match primary.take_completion(11u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("first primary completion missing")
    case Err(_): fail("first primary completion take failed")
expect(first_completion.task_key).to_equal(1001u64)
expect(first_completion.kind).to_equal(RingTerminalKind.Success)
if val value = first_completion.value:
    expect(value).to_equal("first")
else:
    fail("first completion value missing")
val second_completion = match primary.take_completion(11u64):
    case Ok(Some(value)): value
    case Ok(nil): fail("second primary completion missing")
    case Err(_): fail("second primary completion take failed")
expect(second_completion.task_key).to_equal(1002u64)
expect(second_completion.kind).to_equal(RingTerminalKind.Success)
if val value = second_completion.value:
    expect(value).to_equal("second")
else:
    fail("second completion value missing")
expect(primary_provider.counters().admissions).to_equal(3u64)
expect(primary_provider.counters().rejections).to_equal(2u64)
expect(primary_provider.counters().kicks).to_equal(2u64)
expect(primary_provider.counters().takes).to_equal(2u64)
expect(primary_provider.counters().successes).to_equal(2u64)
expect(primary_provider.counters().wakes).to_equal(2u64)
expect(secondary_provider.counters().takes).to_equal(2u64)
expect(secondary_provider.counters().kicks).to_equal(2u64)
expect(secondary_provider.counters().failures).to_equal(1u64)
expect(secondary_provider.counters().cancellations).to_equal(1u64)
expect(secondary_provider.counters().wakes).to_equal(2u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing software provider integration.
- SimpleRing software provider integration

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5bb9810fc9de7265219be25c8791d3689e8d2820fc2682fbf70edeef77e71e25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5bb9810fc9de7265219be25c8791d3689e8d2820fc2682fbf70edeef77e71e25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5bb9810fc9de7265219be25c8791d3689e8d2820fc2682fbf70edeef77e71e25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl
mirror: doc/06_spec/02_integration/lib/async/simple_ring_async_base_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/async/simple_ring_async_base_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/async/simple_ring_async_base_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records bounded provider kicks and caller-clock completion latency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_async_base_integration_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps typed rings bounded, FIFO, exactly woken, and independently progressing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

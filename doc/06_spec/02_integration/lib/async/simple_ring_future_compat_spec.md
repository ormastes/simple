# Simple Ring Future Compat Specification

> Tests covering SimpleRing legacy Future compatibility adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Future Compat Specification

## Scenarios

### SimpleRing legacy Future compatibility adapter

#### maps ready without waiting or creating a scheduler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps ready without waiting or creating a scheduler


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("maps ready without waiting or creating a scheduler")
val receipt = match poll_future_compat(Future<i64>.from_value(42), compat_token()):
    case Ok(value): value
    case Err(_): fail("ready future compatibility failed")
match receipt.poll_result:
    case TaskPollResult.Ready(value): expect(value).to_equal(42)
    case TaskPollResult.Pending(_): fail("ready future became pending")
expect(receipt.waited).to_be(false)
expect(receipt.blocking_used).to_be(false)
expect(receipt.scheduler_created).to_be(false)
```

</details>

#### preserves the exact admitted token for pending wakeup

- preserves the exact admitted token for pending wakeup
   - Expected: actual.ring_id equals `token.ring_id`
   - Expected: actual.slot equals `token.slot`
   - Expected: actual.generation.value equals `token.generation.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves the exact admitted token for pending wakeup")
val token = compat_token()
val receipt = match poll_future_compat(Future<i64>.pending(), token):
    case Ok(value): value
    case Err(_): fail("pending future compatibility failed")
match receipt.poll_result:
    case TaskPollResult.Pending(actual):
        expect(actual.ring_id).to_equal(token.ring_id)
        expect(actual.slot).to_equal(token.slot)
        expect(actual.generation.value).to_equal(token.generation.value)
    case TaskPollResult.Ready(_): fail("pending future became ready")
expect(receipt.waited).to_be(true)
expect(receipt.blocking_used).to_be(false)
expect(receipt.scheduler_created).to_be(false)
```

</details>

#### fails closed instead of manufacturing an invalid wait token

- fails closed instead of manufacturing an invalid wait token


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed instead of manufacturing an invalid wait token")
val invalid = RingToken(
    ring_id: 0u64, slot: 0, generation: RingGeneration(value: 1u64))
match poll_future_compat(Future<i64>.pending(), invalid):
    case Err(error): expect(error).to_equal(FutureCompatError.InvalidWaitToken)
    case Ok(_): fail("invalid compatibility token accepted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/async/simple_ring_future_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing legacy Future compatibility adapter.
- SimpleRing legacy Future compatibility adapter

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d88560ef51418ba08d5ce9f93bf4748bc738a039bdb656b3e0c40cd1cfd49e92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d88560ef51418ba08d5ce9f93bf4748bc738a039bdb656b3e0c40cd1cfd49e92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d88560ef51418ba08d5ce9f93bf4748bc738a039bdb656b3e0c40cd1cfd49e92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/lib/async/simple_ring_future_compat_spec.spl
mirror: doc/06_spec/02_integration/lib/async/simple_ring_future_compat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/async/simple_ring_future_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/async/simple_ring_future_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/async/simple_ring_future_compat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/lib/async/simple_ring_future_compat_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps ready without waiting or creating a scheduler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_future_compat_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the exact admitted token for pending wakeup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_future_compat_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed instead of manufacturing an invalid wait token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

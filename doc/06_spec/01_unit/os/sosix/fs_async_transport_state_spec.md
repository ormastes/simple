# fs_async_transport_state_spec

> SOSIX filesystem async transport correlation and one-completion state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_async_transport_state_spec

SOSIX filesystem async transport correlation and one-completion state.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/fs_async_transport_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX filesystem async transport correlation and one-completion state.

## Scenarios

### SOSIX filesystem async transport state

#### correlates partial progress and exactly one completion notification

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- correlates partial progress and exactly one completion notification
- Submit a generated operation with a unique request token
   - Expected: submitted.key.operation_generation equals `1`
   - Expected: submitted.key.request_token equals `1`
- Record monotonic partial progress without publishing a notification
   - Expected: progressed.state.notification_event equals `0`
- Publish one correlated completion and notification event
   - Expected: completed.event.notification_event equals `1`
- Reject a duplicate completion without advancing the event
   - Expected: duplicate.reason equals `completion-already-published`
   - Expected: duplicate.state.notification_event equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("correlates partial progress and exactly one completion notification")
step("Submit a generated operation with a unique request token")
val submitted = sosix_fs_transport_submit(
    sosix_fs_transport_state_new(), operation(7, 1), 16)
expect(submitted.accepted).to_be(true)
expect(submitted.key.operation_generation).to_equal(1)
expect(submitted.key.request_token).to_equal(1)

step("Record monotonic partial progress without publishing a notification")
val progressed = sosix_fs_transport_record_progress(
    submitted.state, submitted.key, 7
)
expect(progressed.accepted).to_be(true)
expect(progressed.state.partial_progress).to_be(true)
expect(progressed.state.notification_event).to_equal(0)

step("Publish one correlated completion and notification event")
val completed = sosix_fs_transport_complete(
    progressed.state, submitted.key, 0, 7
)
expect(completed.accepted).to_be(true)
expect(completed.event.partial_progress).to_be(true)
expect(completed.event.notification_event).to_equal(1)

step("Reject a duplicate completion without advancing the event")
val duplicate = sosix_fs_transport_complete(
    completed.state, submitted.key, 0, 7
)
expect(duplicate.accepted).to_be(false)
expect(duplicate.reason).to_equal("completion-already-published")
expect(duplicate.state.notification_event).to_equal(1)
```

</details>

#### rejects a mismatched request token while leaving the request pending

- rejects a mismatched request token while leaving the request pending
   - Expected: rejected.reason equals `correlation-mismatch`
   - Expected: rejected.state.phase equals `SOSIX_FS_TRANSPORT_PENDING`
   - Expected: rejected.state.notification_event equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a mismatched request token while leaving the request pending")
val submitted = sosix_fs_transport_submit(
    sosix_fs_transport_state_new(), operation(3, 1), 8)
val wrong = SosixFsRequestKey(
    operation_slot: 3,
    operation_generation: submitted.key.operation_generation,
    request_token: submitted.key.request_token + 1
)
val rejected = sosix_fs_transport_complete(submitted.state, wrong, 0, 8)
expect(rejected.accepted).to_be(false)
expect(rejected.reason).to_equal("correlation-mismatch")
expect(rejected.state.phase).to_equal(SOSIX_FS_TRANSPORT_PENDING)
expect(rejected.state.notification_event).to_equal(0)
```

</details>

#### accepts the next canonical operation generation and advances its request token

- accepts the next canonical operation generation and advances its request token
- Complete, consume, and release the first operation
   - Expected: released.state.active_operation_generation equals `0`
- Submit the next generation and reject the old correlation key
   - Expected: second.key.operation_generation equals `2`
   - Expected: second.key.request_token equals `2`
   - Expected: stale.reason equals `correlation-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts the next canonical operation generation and advances its request token")
step("Complete, consume, and release the first operation")
val first = sosix_fs_transport_submit(
    sosix_fs_transport_state_new(), operation(5, 1), 4)
val completed = sosix_fs_transport_complete(first.state, first.key, 0, 4)
val consumed = sosix_fs_transport_consume(completed.state, first.key)
val released = sosix_fs_transport_release(consumed.state, first.key)
expect(released.accepted).to_be(true)
expect(released.state.active_operation_generation).to_equal(0)

step("Submit the next generation and reject the old correlation key")
val second = sosix_fs_transport_submit(released.state, operation(5, 2), 4)
expect(second.key.operation_generation).to_equal(2)
expect(second.key.request_token).to_equal(2)
val stale = sosix_fs_transport_complete(second.state, first.key, 0, 4)
expect(stale.accepted).to_be(false)
expect(stale.reason).to_equal("correlation-mismatch")
```

</details>

#### rejects regressing or overflowing progress

- rejects regressing or overflowing progress
   - Expected: regressed.reason equals `invalid-progress`
   - Expected: overflowed.reason equals `invalid-progress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects regressing or overflowing progress")
val submitted = sosix_fs_transport_submit(
    sosix_fs_transport_state_new(), operation(9, 1), 10)
val progressed = sosix_fs_transport_record_progress(
    submitted.state, submitted.key, 6
)
val regressed = sosix_fs_transport_record_progress(
    progressed.state, submitted.key, 5
)
expect(regressed.accepted).to_be(false)
expect(regressed.reason).to_equal("invalid-progress")
val overflowed = sosix_fs_transport_complete(
    progressed.state, submitted.key, 0, 11
)
expect(overflowed.accepted).to_be(false)
expect(overflowed.reason).to_equal("invalid-progress")
```

</details>

#### requires consumption before release

- requires consumption before release
   - Expected: early.reason equals `completion-not-consumed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires consumption before release")
val submitted = sosix_fs_transport_submit(
    sosix_fs_transport_state_new(), operation(1, 1), 1)
val completed = sosix_fs_transport_complete(submitted.state, submitted.key, 0, 1)
val early = sosix_fs_transport_release(completed.state, submitted.key)
expect(early.accepted).to_be(false)
expect(early.reason).to_equal("completion-not-consumed")
```

</details>

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50ab65f825da4a2a5567683fb0f38ce26309886deca3ef3361cdc1f4363f5f15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50ab65f825da4a2a5567683fb0f38ce26309886deca3ef3361cdc1f4363f5f15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50ab65f825da4a2a5567683fb0f38ce26309886deca3ef3361cdc1f4363f5f15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/sosix/fs_async_transport_state_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/fs_async_transport_state_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/fs_async_transport_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/fs_async_transport_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/fs_async_transport_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/fs_async_transport_state_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'correlates partial progress and exactly one completion notification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_async_transport_state_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a mismatched request token while leaving the request pending' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_async_transport_state_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the next canonical operation generation and advances its request token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

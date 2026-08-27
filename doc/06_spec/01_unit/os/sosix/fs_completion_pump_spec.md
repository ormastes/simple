# fs_completion_pump_spec

> Authenticated SOSIX filesystem completion-pump contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_completion_pump_spec

Authenticated SOSIX filesystem completion-pump contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/fs_completion_pump_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Authenticated SOSIX filesystem completion-pump contract.

## Scenarios

### SOSIX filesystem completion pump

#### publishes one typed partial completion and one notification decision

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes one typed partial completion and one notification decision
- Create one pending read and receive an authenticated partial reply
   - Expected: result.completion.api_id equals `SOSIX_FS_READ_AT`
   - Expected: result.completion.transferred equals `3`
   - Expected: result.payload.len() equals `3`
   - Expected: result.event.notification_event equals `1`
- Feed the same terminal reply back and reject duplicate publication
   - Expected: duplicate.reason equals `completion-already-published`
   - Expected: duplicate.transport_state.notification_event equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("publishes one typed partial completion and one notification decision")
step("Create one pending read and receive an authenticated partial reply")
val fixture = _pending(7, 8)
val result = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _fixture_wire(fixture, 3, [10, 20, 30])
)
expect(result.accepted).to_be(true)
expect(result.notify).to_be(true)
expect(result.completion.api_id).to_equal(SOSIX_FS_READ_AT)
expect(result.completion.transferred).to_equal(3)
expect(result.completion.partial_progress).to_be(true)
expect(result.payload.len()).to_equal(3)
expect(result.event.notification_event).to_equal(1)

step("Feed the same terminal reply back and reject duplicate publication")
val duplicate = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    result.operation_slot,
    result.transport_state,
    _fixture_wire(fixture, 3, [10, 20, 30])
)
expect(duplicate.accepted).to_be(false)
expect(duplicate.notify).to_be(false)
expect(duplicate.reason).to_equal("completion-already-published")
expect(duplicate.transport_state.notification_event).to_equal(1)
```

</details>

#### rejects a spoofed endpoint before decoding attacker bytes

- rejects a spoofed endpoint before decoding attacker bytes
   - Expected: spoofed.reason equals `untrusted-service-source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a spoofed endpoint before decoding attacker bytes")
val fixture = _pending(2, 4)
val spoofed = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    99,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    [0]
)
expect(spoofed.accepted).to_be(false)
expect(spoofed.notify).to_be(false)
expect(spoofed.reason).to_equal("untrusted-service-source")
```

</details>

#### rejects stale and swapped request identities without notification

- rejects stale and swapped request identities without notification
   - Expected: stale.reason equals `operation-mismatch`
   - Expected: swapped.reason equals `operation-mismatch`
   - Expected: wrong_token.reason equals `request-token-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects stale and swapped request identities without notification")
val fixture = _pending(5, 4)
val stale = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _wire(SOSIX_FS_READ_AT, 5, 2, 1, 0, 4, [])
)
expect(stale.accepted).to_be(false)
expect(stale.reason).to_equal("operation-mismatch")

val swapped = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _wire(SOSIX_FS_READ_AT, 6, 1, 1, 0, 4, [])
)
expect(swapped.accepted).to_be(false)
expect(swapped.notify).to_be(false)
expect(swapped.reason).to_equal("operation-mismatch")

val wrong_token = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _wire(SOSIX_FS_READ_AT, 5, 1, 2, 0, 4, [])
)
expect(wrong_token.reason).to_equal("request-token-mismatch")
```

</details>

#### rejects swapped APIs and malformed wire messages

- rejects swapped APIs and malformed wire messages
   - Expected: swapped_api.reason equals `api-mismatch`
   - Expected: malformed.reason equals `completion-too-short`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects swapped APIs and malformed wire messages")
val fixture = _pending(3, 4)
val swapped_api = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _wire(SOSIX_FS_WRITE_AT, 3, 1, 1, 0, 4, [])
)
expect(swapped_api.reason).to_equal("api-mismatch")
val malformed = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    [1, 0, 48]
)
expect(malformed.reason).to_equal("completion-too-short")
```

</details>

#### bounds transferred bytes and payload against the pending request

- bounds transferred bytes and payload against the pending request
   - Expected: excess_transfer.reason equals `transferred-exceeds-request`
   - Expected: excess_payload.reason equals `payload-exceeds-request`
   - Expected: payload_over_transfer.reason equals `payload-exceeds-transferred`
   - Expected: full_marked_partial.reason equals `partial-flag-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("bounds transferred bytes and payload against the pending request")
val fixture = _pending(9, 4)
val excess_transfer = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _fixture_wire(fixture, 5, [])
)
expect(excess_transfer.reason).to_equal("transferred-exceeds-request")

val excess_payload = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _fixture_wire(fixture, 4, [1, 2, 3, 4, 5])
)
expect(excess_payload.reason).to_equal("payload-exceeds-request")

val payload_over_transfer = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _fixture_wire(fixture, 2, [1, 2, 3])
)
expect(payload_over_transfer.reason).to_equal("payload-exceeds-transferred")

val full_marked_partial = sosix_fs_completion_pump_receive(
    FS_SERVICE_ENDPOINT,
    FS_SERVICE_ENDPOINT,
    SOSIX_FS_READ_AT,
    fixture.operation_slot,
    fixture.transport_state,
    _fixture_wire(fixture, 4, [1, 2, 3, 4])
)
expect(full_marked_partial.reason).to_equal("partial-flag-mismatch")
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

- Canonical SPipe generation for source `b9310f41653b91676189349600cdfcc903d28ed1a408bed4901b0c9837e74234`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9310f41653b91676189349600cdfcc903d28ed1a408bed4901b0c9837e74234`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9310f41653b91676189349600cdfcc903d28ed1a408bed4901b0c9837e74234`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/sosix/fs_completion_pump_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/fs_completion_pump_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/fs_completion_pump_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/fs_completion_pump_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/fs_completion_pump_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/fs_completion_pump_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes one typed partial completion and one notification decision' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_completion_pump_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a spoofed endpoint before decoding attacker bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_completion_pump_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale and swapped request identities without notification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

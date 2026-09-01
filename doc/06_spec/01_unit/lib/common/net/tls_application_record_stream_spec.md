# Bounded TLS application-record stream

> One mutable fixed ring accepts legal TLS records fragmented down to one byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bounded TLS application-record stream

One mutable fixed ring accepts legal TLS records fragmented down to one byte.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/net/tls_application_record_stream_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

One mutable fixed ring accepts legal TLS records fragmented down to one byte.
Complete frames require a generation-bound authenticated commit before logical
head or receive sequence advances.

## Scenarios

### TLS mutable fixed-ring ownership

#### accepts a maximum legal record fragmented into one-byte reads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a maximum legal record fragmented into one-byte reads


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a maximum legal record fragmented into one-byte reads")
val record = _synthetic_tls_record(16400, 7u8)
expect(record.len()).to_be(TLS_MAX_RECORD_WIRE_LENGTH_V1)
var stream = tls_application_record_stream_new_v1(9)
var index: i64 = 0
var final_record_count: i64 = 0
var final_token: i64 = 0
while index < record.len():
    val ingested = stream.ingest([record[index]])
    expect(ingested.is_malformed()).to_be(false)
    expect(ingested.is_overflow()).to_be(false)
    final_record_count = ingested.framed_records().len()
    final_token = ingested.proposal_token()
    index = index + 1

expect(final_record_count).to_be(1)
expect(stream.has_pending_proposal()).to_be(true)
expect(stream.sequence()).to_be(9)
expect(stream.commit_authenticated(final_token, 1)).to_be(true)
expect(stream.remaining_byte_count()).to_be(0)
expect(stream.fragment_count()).to_be(0)
expect(stream.sequence()).to_be(10)
# N writes + (5N - 10) header probes + N record handoff copies.
expect(stream.byte_work()).to_be(7 * record.len() - 10)

val no_progress = stream.ingest([])
expect(no_progress.byte_work()).to_be(0)
expect(stream.byte_work()).to_be(7 * record.len() - 10)
```

</details>

#### frames coalesced records and commits only after authentication

- frames coalesced records and commits only after authentication
   - Expected: completed.framed_records() equals `[record_c]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frames coalesced records and commits only after authentication")
val record_a = _synthetic_tls_record(16, 1u8)
val record_b = _synthetic_tls_record(16, 2u8)
val record_c = _synthetic_tls_record(16, 3u8)
var stream = tls_application_record_stream_new_v1(4)
val first = stream.ingest(
    record_a + record_b + record_c.slice(0, 7))
expect(first.framed_records().len()).to_be(2)
expect(first.remaining_byte_count()).to_be(7)
expect(first.proposed_sequence()).to_be(6)
expect(stream.sequence()).to_be(4)
expect(stream.remaining_byte_count()).to_be(0)
expect(stream.commit_authenticated(
    first.proposal_token(), first.framed_records().len())).to_be(true)
expect(stream.sequence()).to_be(6)
expect(stream.remaining_byte_count()).to_be(7)

val completed = stream.ingest(record_c.slice(7, record_c.len()))
expect(completed.framed_records()).to_equal([record_c])
expect(stream.commit_authenticated(
    completed.proposal_token(), 1)).to_be(true)
expect(stream.remaining_byte_count()).to_be(0)
expect(stream.sequence()).to_be(7)
```

</details>

#### rejects concurrent ingest and stale authenticated commits

- rejects concurrent ingest and stale authenticated commits


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects concurrent ingest and stale authenticated commits")
val record = _synthetic_tls_record(16)
var stream = tls_application_record_stream_new_v1()
val proposal = stream.ingest(record)
expect(proposal.requires_commit()).to_be(true)
val blocked = stream.ingest([1u8])
expect(blocked.is_proposal_pending()).to_be(true)
expect(stream.commit_authenticated(
    proposal.proposal_token(), 2)).to_be(false)
expect(stream.is_failed()).to_be(true)
```

</details>

#### makes authentication rejection terminal for the owner

- makes authentication rejection terminal for the owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes authentication rejection terminal for the owner")
var stream = tls_application_record_stream_new_v1()
val proposal = stream.ingest(_synthetic_tls_record(16))
expect(stream.reject_authentication(
    proposal.proposal_token())).to_be(true)
expect(stream.is_failed()).to_be(true)
expect(stream.ingest([1u8]).is_malformed()).to_be(true)
```

</details>

### TLS application-record fail-closed bounds

#### rejects malformed framing without sequence advancement

- rejects malformed framing without sequence advancement


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed framing without sequence advancement")
var malformed = _synthetic_tls_record(16)
malformed[0] = 22u8
var stream = tls_application_record_stream_new_v1(3)
val rejected = stream.ingest(malformed)
expect(rejected.is_malformed()).to_be(true)
expect(rejected.framed_records().len()).to_be(0)
expect(stream.sequence()).to_be(3)
expect(stream.is_failed()).to_be(true)
```

</details>

#### checks the byte ceiling before adding untrusted input

- checks the byte ceiling before adding untrusted input


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks the byte ceiling before adding untrusted input")
var oversized: [u8] = []
var index: i64 = 0
while index <= TLS_MAX_RX_BUFFER_LENGTH_V1:
    oversized.push(0u8)
    index = index + 1
var stream = tls_application_record_stream_new_v1()
val overflow = stream.ingest(oversized)
expect(overflow.is_overflow()).to_be(true)
expect(overflow.byte_work()).to_be(0)
expect(stream.remaining_byte_count()).to_be(0)
expect(stream.is_failed()).to_be(true)
```

</details>

#### rejects receive-sequence exhaustion without wrapping

- rejects receive-sequence exhaustion without wrapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects receive-sequence exhaustion without wrapping")
var stream = tls_application_record_stream_new_v1(TLS_MAX_SEQUENCE_V1)
val exhausted = stream.ingest(_synthetic_tls_record(16))
expect(exhausted.is_sequence_exhausted()).to_be(true)
expect(exhausted.framed_records().len()).to_be(0)
expect(exhausted.proposed_sequence()).to_be(TLS_MAX_SEQUENCE_V1)
expect(stream.sequence()).to_be(TLS_MAX_SEQUENCE_V1)
expect(tls_application_record_sequence_can_advance_v1(0)).to_be(true)
expect(tls_application_record_sequence_can_advance_v1(-1)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `2bce6280560572dcb3e43728ff7145038d22ebe76f37fbe9aad64261d9733596`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2bce6280560572dcb3e43728ff7145038d22ebe76f37fbe9aad64261d9733596`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2bce6280560572dcb3e43728ff7145038d22ebe76f37fbe9aad64261d9733596`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/net/tls_application_record_stream_spec.spl
mirror: doc/06_spec/01_unit/lib/common/net/tls_application_record_stream_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/net/tls_application_record_stream_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/net/tls_application_record_stream_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/net/tls_application_record_stream_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a maximum legal record fragmented into one-byte reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/tls_application_record_stream_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'frames coalesced records and commits only after authentication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/tls_application_record_stream_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects concurrent ingest and stale authenticated commits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

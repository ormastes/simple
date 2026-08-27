# HTTP worker wire and shutdown ownership coverage.

> The worker owns socket operations, TLS state, and any open sendfile handles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP worker wire and shutdown ownership coverage.

The worker owns socket operations, TLS state, and any open sendfile handles.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The worker owns socket operations, TLS state, and any open sendfile handles.
These cases pin the fail-closed wire boundaries and observe the public cleanup
counters while runtime/socket admission remains unavailable in the static lane.

## Scenarios

### HTTP worker malformed wire handling

#### rejects a header line without a field name instead of dropping it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a header line without a field name instead of dropping it


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a header line without a field name instead of dropping it")
val parser = HttpRequestParser.new()
val result = parser.feed("GET / HTTP/1.1\r\nBroken\r\n")
match result:
    Ok(_): fail("malformed header was accepted")
    Err(_): expect(parser.error_message.starts_with("400")).to_be(true)
```

</details>

#### rejects an over-limit partial header before more buffering

- rejects an over-limit partial header before more buffering


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an over-limit partial header before more buffering")
val parser = HttpRequestParser.with_limits(8192, 8, 16, 1024)
val first = parser.feed("GET / HTTP/1.1\r\n")
match first:
    Ok(_): expect(parser.is_complete()).to_be(false)
    Err(_): fail("valid request line was rejected")
val result = parser.feed("X-Test: 12345678901234567890")
match result:
    Ok(_): fail("over-limit header was accepted")
    Err(_): expect(parser.error_message.starts_with("431")).to_be(true)
```

</details>

### HTTP/2 preface admission

#### requires the complete canonical preface

- requires the complete canonical preface


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the complete canonical preface")
val preface = h2_connection_preface_bytes()
expect(h2_validate_preface(preface)).to_be(true)
val short = preface.slice(0, 3)
expect(h2_validate_preface(short)).to_be(false)
var malformed = preface
malformed[2] = 88
expect(h2_validate_preface(malformed)).to_be(false)
```

</details>

### TLS application-record accumulation

#### retains split records and consumes multiple complete records

- retains split records and consumes multiple complete records


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains split records and consumes multiple complete records")
val record_a = synthetic_tls_record(16)
val record_b = synthetic_tls_record(16)
val first = record_a.slice(0, 7)
val tail = record_a.slice(7, record_a.len())
var split_stream = tls_application_record_stream_new_v1(1)
var first_ingest = split_stream.ingest(first)
val first_records = first_ingest.framed_records()
expect(first_ingest.is_malformed()).to_be(false)
expect(first_records.len()).to_be(0)
expect(first_ingest.remaining_byte_count()).to_be(7)
expect(split_stream.fragment_count()).to_be(1)
expect(first_ingest.requires_commit()).to_be(false)

var second_ingest = split_stream.ingest(tail)
val second_records = second_ingest.framed_records()
expect(second_ingest.is_malformed()).to_be(false)
expect(second_records.len()).to_be(1)
expect(second_ingest.remaining_byte_count()).to_be(0)
expect(second_ingest.proposed_sequence()).to_be(2)
expect(second_ingest.requires_commit()).to_be(true)
expect(split_stream.commit_authenticated(
    second_ingest.proposal_token(), second_records.len()
)).to_be(true)
expect(split_stream.remaining_byte_count()).to_be(0)
expect(split_stream.sequence()).to_be(2)

val coalesced = record_a + record_b
var multiple_stream = tls_application_record_stream_new_v1(1)
var multiple_ingest = multiple_stream.ingest(coalesced)
val multiple_records = multiple_ingest.framed_records()
expect(multiple_records.len()).to_be(2)
expect(multiple_ingest.remaining_byte_count()).to_be(0)
expect(multiple_ingest.proposed_sequence()).to_be(3)
expect(multiple_stream.commit_authenticated(
    multiple_ingest.proposal_token(), multiple_records.len()
)).to_be(true)
expect(multiple_stream.sequence()).to_be(3)
```

</details>

#### rejects malformed framing and bounded-buffer overflow

- rejects malformed framing and bounded-buffer overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed framing and bounded-buffer overflow")
var malformed = synthetic_tls_record(16)
malformed[0] = 22
var malformed_stream = tls_application_record_stream_new_v1(1)
var malformed_result = malformed_stream.ingest(malformed)
expect(malformed_result.is_malformed()).to_be(true)

val oversized_header: [u8] = [23, 3, 3, 64, 17]
var oversized_stream = tls_application_record_stream_new_v1(1)
var oversized_result = oversized_stream.ingest(oversized_header)
expect(oversized_result.is_malformed()).to_be(true)

val full_record = synthetic_tls_record(16384)
val next_header: [u8] = [23, 3, 3]
var accepted_stream = tls_application_record_stream_new_v1(1)
var accepted_result = accepted_stream.ingest(full_record + next_header)
val accepted_records = accepted_result.framed_records()
expect(accepted_result.is_malformed()).to_be(false)
expect(accepted_result.is_overflow()).to_be(false)
expect(accepted_records.len()).to_be(1)
expect(accepted_result.remaining_byte_count()).to_be(3)
expect(accepted_stream.commit_authenticated(
    accepted_result.proposal_token(), accepted_records.len()
)).to_be(true)
expect(accepted_stream.remaining_byte_count()).to_be(3)

var beyond_ceiling: [u8] = []
var i = 0
while i <= full_record.len():
    beyond_ceiling.push(0)
    i = i + 1
var overflow_stream = tls_application_record_stream_new_v1(1)
var overflow_result = overflow_stream.ingest(full_record + beyond_ceiling)
expect(overflow_result.is_overflow()).to_be(true)
```

</details>

#### rejects a second ingest while authentication is pending

- rejects a second ingest while authentication is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a second ingest while authentication is pending")
val record = synthetic_tls_record(16)
var stream = tls_application_record_stream_new_v1(0)
var proposal = stream.ingest(record)
expect(proposal.requires_commit()).to_be(true)
var blocked = stream.ingest([1])
expect(blocked.is_proposal_pending()).to_be(true)
stream.reject_authentication(proposal.proposal_token())
```

</details>

#### preserves mapped ownership through maximum one-byte fragmentation

- preserves mapped ownership through maximum one-byte fragmentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves mapped ownership through maximum one-byte fragmentation")
val record = synthetic_tls_record(16400)
var streams: Dict<i64, TlsApplicationRecordStreamV1> = {}
streams[7] = tls_application_record_stream_new_v1(0)
var framed_count = 0
var malformed = false
var overflow = false
var commit_failed = false
var index = 0
while index < record.len():
    val fragment: [u8] = [record[index]]
    # Mirror Worker ownership: take the sole value out of the Dict,
    # mutate it, then publish it back after a successful transaction.
    var stream = streams[7]
    streams.remove(7)
    var ingest = stream.ingest(fragment)
    if ingest.is_malformed():
        malformed = true
    if ingest.is_overflow():
        overflow = true
    val framed_records = ingest.framed_records()
    framed_count = framed_count + framed_records.len()
    if ingest.requires_commit():
        if not stream.commit_authenticated(
            ingest.proposal_token(), framed_records.len()):
            commit_failed = true
    streams[7] = stream
    index = index + 1
expect(malformed).to_be(false)
expect(overflow).to_be(false)
expect(commit_failed).to_be(false)
expect(framed_count).to_be(1)
expect(streams[7].remaining_byte_count()).to_be(0)
expect(streams[7].fragment_count()).to_be(0)
expect(streams[7].sequence()).to_be(1)
expect(streams[7].has_pending_proposal()).to_be(false)
expect(streams[7].is_failed()).to_be(false)
expect(streams[7].byte_work()).to_be(record.len() * 7 - 10)
```

</details>

#### rejects exhausted and invalid record sequences

- rejects exhausted and invalid record sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects exhausted and invalid record sequences")
expect(tls_application_record_sequence_can_advance_v1(0)).to_be(true)
expect(tls_application_record_sequence_can_advance_v1(9223372036854775806)).to_be(true)
expect(tls_application_record_sequence_can_advance_v1(9223372036854775807)).to_be(false)
expect(tls_application_record_sequence_can_advance_v1(-1)).to_be(false)
```

</details>

### HTTP worker shutdown ownership contract

#### cancels an unstarted owner without retaining reservations

- cancels an unstarted owner without retaining reservations


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancels an unstarted owner without retaining reservations")
var config = default_server_config()
config.worker_count = 1
val server = HttpServer.new(config)
val result = server.cancel(0)
match result:
    Ok(_):
        expect(server.active_worker_reservations()).to_be(0)
        expect(server.queue_bytes_reserved()).to_be(0)
        expect(server.result_reservations()).to_be(0)
    Err(_): fail("unstarted owner cancellation failed")
```

</details>

#### reports zero retained resources after owner abort cleanup

- reports zero retained resources after owner abort cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports zero retained resources after owner abort cleanup")
var config = default_server_config()
config.listen_addr = "127.0.0.1:0"
config.worker_count = 1
val worker_result = Worker.create(
    0, config, AsyncRouter.new(config.locations),
    build_default_pipeline(), create_default_registry(""),
    channel_new()
)
match worker_result:
    Ok(worker):
        worker.abort_start()
        val snapshot = worker.resource_snapshot()
        expect(snapshot.active_count).to_be(0)
        expect(snapshot.active_connections).to_be(0)
        expect(snapshot.h2_connections).to_be(0)
        expect(snapshot.pending_operations).to_be(0)
        expect(snapshot.pending_sendfiles).to_be(0)
        expect(snapshot.open_sendfiles).to_be(0)
        expect(snapshot.tls_sessions).to_be(0)
        expect(snapshot.tls_buffers).to_be(0)
    Err(_): fail("worker owner construction failed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `d927bc5ee0fa0ba54d6e49678644cdc1e3c5f081e0dd0450bb8bd5b4a1a71593`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d927bc5ee0fa0ba54d6e49678644cdc1e3c5f081e0dd0450bb8bd5b4a1a71593`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d927bc5ee0fa0ba54d6e49678644cdc1e3c5f081e0dd0450bb8bd5b4a1a71593`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a header line without a field name instead of dropping it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an over-limit partial header before more buffering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/worker_wire_shutdown_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires the complete canonical preface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

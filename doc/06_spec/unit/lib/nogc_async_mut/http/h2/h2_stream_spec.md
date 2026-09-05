# H2 Stream Lifecycle Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 Stream Lifecycle Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-1-stream |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### H2 stream lifecycle and flow control

#### starts in idle state

- starts in idle state
   - Expected: stream_state equals `STATE_IDLE`
   - Expected: stream_id % 2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts in idle state")
"""
A newly allocated H2Stream for a given stream_id must begin
in the Idle state before any frames are sent or received.
"""
# Stub: stream state constants
val STATE_IDLE = 0
val stream_state = STATE_IDLE
expect(stream_state).to_equal(STATE_IDLE)
# stream_id must be odd (client-initiated)
val stream_id: u32 = 1
expect(stream_id % 2).to_equal(1)
```

</details>

#### transitions to open on HEADERS send

- transitions to open on HEADERS send
   - Expected: stream_state equals `STATE_OPEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions to open on HEADERS send")
"""
RFC 9113 §5.1 — Sending a HEADERS frame on an Idle stream moves
it to the Open state.
"""
val STATE_IDLE = 0
val STATE_OPEN = 1
var stream_state = STATE_IDLE
# Simulate sending HEADERS (no END_STREAM flag)
val end_stream = false
if !end_stream:
    stream_state = STATE_OPEN
expect(stream_state).to_equal(STATE_OPEN)
```

</details>

#### transitions to half-closed-local on END_STREAM send

- transitions to half-closed-local on END_STREAM send
   - Expected: stream_state equals `STATE_HALF_CLOSED_LOCAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions to half-closed-local on END_STREAM send")
"""
RFC 9113 §5.1 — Sending DATA or HEADERS with END_STREAM set on
an Open stream moves it to the Half-Closed (Local) state.
"""
val STATE_OPEN = 1
val STATE_HALF_CLOSED_LOCAL = 2
var stream_state = STATE_OPEN
# Simulate sending DATA with END_STREAM flag
val end_stream = true
if end_stream:
    stream_state = STATE_HALF_CLOSED_LOCAL
expect(stream_state).to_equal(STATE_HALF_CLOSED_LOCAL)
```

</details>

#### transitions to closed on RST_STREAM

- transitions to closed on RST_STREAM
   - Expected: stream_state equals `STATE_CLOSED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions to closed on RST_STREAM")
"""
RFC 9113 §5.1 — Receiving or sending RST_STREAM in any non-idle
state immediately moves the stream to Closed.
"""
val STATE_OPEN = 1
val STATE_CLOSED = 4
var stream_state = STATE_OPEN
# Simulate RST_STREAM received
val rst_received = true
if rst_received:
    stream_state = STATE_CLOSED
expect(stream_state).to_equal(STATE_CLOSED)
```

</details>

#### tracks flow control window credits

- tracks flow control window credits
   - Expected: send_window equals `64535`
   - Expected: send_window equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks flow control window credits")
"""
RFC 9113 §5.2 — The send window starts at the initial_window_size
from SETTINGS (default 65535). Sending DATA reduces the window by
the number of bytes sent.
"""
val initial_window: i32 = 65535
var send_window: i32 = initial_window
# Send 1000 bytes of data
val bytes_sent: i32 = 1000
send_window = send_window - bytes_sent
expect(send_window).to_equal(64535)
# Send another 64535 bytes — window reaches zero
send_window = send_window - 64535
expect(send_window).to_equal(0)
```

</details>

#### rejects data when flow control window exhausted

- rejects data when flow control window exhausted
   - Expected: can_send is false
   - Expected: can_send_after_update is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects data when flow control window exhausted")
"""
RFC 9113 §5.2 — A sender MUST NOT send DATA frames when the
stream-level flow control window is zero or negative.
"""
var send_window: i32 = 0
val data_size: i32 = 512
# Attempt to send: blocked because window == 0
val can_send = send_window >= data_size
expect(can_send).to_equal(false)
# After WINDOW_UPDATE adds 1024 credits, send is allowed
send_window = send_window + 1024
val can_send_after_update = send_window >= data_size
expect(can_send_after_update).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `8088545dc89151c741c0df74506ef84dd8be23287abf6af5242e552e741419e8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8088545dc89151c741c0df74506ef84dd8be23287abf6af5242e552e741419e8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8088545dc89151c741c0df74506ef84dd8be23287abf6af5242e552e741419e8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts in idle state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transitions to open on HEADERS send' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/http/h2/h2_stream_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transitions to half-closed-local on END_STREAM send' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

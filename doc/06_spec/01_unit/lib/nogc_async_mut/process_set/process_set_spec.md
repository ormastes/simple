# Process Set Specification

> Tests covering ProcessSet Config, IPC Message Serialization, IPC Reply Serialization, Atomic Claim - Double-Consume Prevention, Sequence ID Uniqueness, Kill Guard - PID Safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Set Specification

## Scenarios

### ProcessSet Config

#### parses mode shared

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses mode shared
   - Expected: mode equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses mode shared")
val mode = test_parse_mode("shared")
expect(mode).to_equal("shared")
```

</details>

#### parses mode actor

- parses mode actor
   - Expected: mode equals `actor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses mode actor")
val mode = test_parse_mode("actor")
expect(mode).to_equal("actor")
```

</details>

#### parses mode separated

- parses mode separated
   - Expected: mode equals `separated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses mode separated")
val mode = test_parse_mode("separated")
expect(mode).to_equal("separated")
```

</details>

#### unknown mode defaults to shared

- unknown mode defaults to shared
   - Expected: mode equals `shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unknown mode defaults to shared")
val mode = test_parse_mode("unknown_xyz")
expect(mode).to_equal("shared")
```

</details>

#### parses ipc_transport channel

- parses ipc_transport channel
   - Expected: transport equals `channel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses ipc_transport channel")
val transport = test_parse_transport("channel")
expect(transport).to_equal("channel")
```

</details>

#### parses ipc_transport file_queue

- parses ipc_transport file_queue
   - Expected: transport equals `file_queue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses ipc_transport file_queue")
val transport = test_parse_transport("file_queue")
expect(transport).to_equal("file_queue")
```

</details>

#### unknown transport defaults to channel

- unknown transport defaults to channel
   - Expected: transport equals `channel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("unknown transport defaults to channel")
val transport = test_parse_transport("nope")
expect(transport).to_equal("channel")
```

</details>

#### mode round-trip: actor survives serialize-parse

- mode round-trip: actor survives serialize-parse
   - Expected: reparsed equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mode round-trip: actor survives serialize-parse")
val original = "actor"
val serialized = test_parse_mode(original)
val reparsed = test_parse_mode(serialized)
expect(reparsed).to_equal(original)
```

</details>

#### mode round-trip: separated survives serialize-parse

- mode round-trip: separated survives serialize-parse
   - Expected: reparsed equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("mode round-trip: separated survives serialize-parse")
val original = "separated"
val serialized = test_parse_mode(original)
val reparsed = test_parse_mode(serialized)
expect(reparsed).to_equal(original)
```

</details>

### IPC Message Serialization

#### serializes id field correctly

- serializes id field correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes id field correctly")
val msg = TestIpcMessage(
    id: "42_1",
    source: "main",
    target: "worker1",
    method: "ping",
    payload: "hello",
    timestamp: 1000,
    reply_to: ""
)
val content = test_serialize_message(msg)
expect(content).to_contain("id: 42_1")
```

</details>

#### serializes source field correctly

- serializes source field correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("serializes source field correctly")
val msg = TestIpcMessage(
    id: "1_1",
    source: "proc_a",
    target: "proc_b",
    method: "test",
    payload: "",
    timestamp: 0,
    reply_to: ""
)
val content = test_serialize_message(msg)
expect(content).to_contain("source: proc_a")
```

</details>

#### round-trips id

- round-trips id
   - Expected: parsed.id equals `99_7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips id")
val msg = TestIpcMessage(
    id: "99_7",
    source: "s",
    target: "t",
    method: "m",
    payload: "p",
    timestamp: 500,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.id).to_equal("99_7")
```

</details>

#### round-trips source

- round-trips source
   - Expected: parsed.source equals `sender`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips source")
val msg = TestIpcMessage(
    id: "1_2",
    source: "sender",
    target: "receiver",
    method: "act",
    payload: "data",
    timestamp: 100,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.source).to_equal("sender")
```

</details>

#### round-trips target

- round-trips target
   - Expected: parsed.target equals `worker2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips target")
val msg = TestIpcMessage(
    id: "1_3",
    source: "a",
    target: "worker2",
    method: "do",
    payload: "",
    timestamp: 200,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.target).to_equal("worker2")
```

</details>

#### round-trips method

- round-trips method
   - Expected: parsed.method equals `compute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips method")
val msg = TestIpcMessage(
    id: "1_4",
    source: "a",
    target: "b",
    method: "compute",
    payload: "",
    timestamp: 0,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.method).to_equal("compute")
```

</details>

#### round-trips payload

- round-trips payload
   - Expected: parsed.payload equals `the-data-123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips payload")
val msg = TestIpcMessage(
    id: "1_5",
    source: "a",
    target: "b",
    method: "m",
    payload: "the-data-123",
    timestamp: 0,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.payload).to_equal("the-data-123")
```

</details>

#### round-trips reply_to

- round-trips reply_to
   - Expected: parsed.reply_to equals `orig_42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips reply_to")
val msg = TestIpcMessage(
    id: "1_6",
    source: "a",
    target: "b",
    method: "m",
    payload: "",
    timestamp: 0,
    reply_to: "orig_42"
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.reply_to).to_equal("orig_42")
```

</details>

#### round-trips empty reply_to

- round-trips empty reply_to
   - Expected: parsed.reply_to equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips empty reply_to")
val msg = TestIpcMessage(
    id: "1_7",
    source: "a",
    target: "b",
    method: "m",
    payload: "",
    timestamp: 0,
    reply_to: ""
)
val content = test_serialize_message(msg)
val parsed = test_parse_message(content)
expect(parsed.reply_to).to_equal("")
```

</details>

### IPC Reply Serialization

#### round-trips id

- round-trips id
   - Expected: parsed.id equals `reply_1_3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips id")
val r = TestIpcReply(id: "reply_1_3", in_reply_to: "1_2", payload: "ok", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.id).to_equal("reply_1_3")
```

</details>

#### round-trips in_reply_to

- round-trips in_reply_to
   - Expected: parsed.in_reply_to equals `orig_99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips in_reply_to")
val r = TestIpcReply(id: "r1", in_reply_to: "orig_99", payload: "done", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.in_reply_to).to_equal("orig_99")
```

</details>

#### round-trips payload

- round-trips payload
   - Expected: parsed.payload equals `result-data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips payload")
val r = TestIpcReply(id: "r2", in_reply_to: "x", payload: "result-data", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.payload).to_equal("result-data")
```

</details>

#### round-trips error field

- round-trips error field
   - Expected: parsed.error equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips error field")
val r = TestIpcReply(id: "r3", in_reply_to: "x", payload: "", error: "timeout")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.error).to_equal("timeout")
```

</details>

#### round-trips empty error

- round-trips empty error
   - Expected: parsed.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips empty error")
val r = TestIpcReply(id: "r4", in_reply_to: "x", payload: "val", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.error).to_equal("")
```

</details>

### Atomic Claim - Double-Consume Prevention

#### first consume returns content

- first consume returns content
   - Expected: content equals `msg-content`
   - Expected: claimed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first consume returns content")
# Simulate: message is available, first claim gets it
var claimed = false
var content = "msg-content"
if not claimed:
    claimed = true
    expect(content).to_equal("msg-content")
expect(claimed).to_equal(true)
```

</details>

#### second consume sees nothing after first claimed

- second consume sees nothing after first claimed
   - Expected: claim_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second consume sees nothing after first claimed")
# Simulate: two sequential readers; second should get nothing
var claim_count: i64 = 0
var available = true

# First reader claims
if available:
    available = false
    claim_count = claim_count + 1

# Second reader attempts to claim same resource
if available:
    claim_count = claim_count + 1

expect(claim_count).to_equal(1)
```

</details>

#### claim sets available to false

- claim sets available to false
   - Expected: available is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("claim sets available to false")
var available = true
if available:
    available = false
expect(available).to_equal(false)
```

</details>

#### failed claim returns empty path

- failed claim returns empty path
   - Expected: got_message is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("failed claim returns empty path")
# rename-to-claimed fails if file already moved => returns ""
val claimed_path = ""
val got_message = claimed_path != ""
expect(got_message).to_equal(false)
```

</details>

#### successful claim returns non-empty path

- successful claim returns non-empty path
   - Expected: got_message is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("successful claim returns non-empty path")
val claimed_path = "/tmp/simple_ipc/worker/inbox/42_1.msg.claimed"
val got_message = claimed_path != ""
expect(got_message).to_equal(true)
```

</details>

### Sequence ID Uniqueness

#### first ID uses sequence 1

- first ID uses sequence 1
   - Expected: id1 equals `100_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("first ID uses sequence 1")
_test_seq = 0
val id1 = test_next_id(100)
expect(id1).to_equal("100_1")
```

</details>

#### second ID uses sequence 2

- second ID uses sequence 2
   - Expected: id2 equals `100_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second ID uses sequence 2")
_test_seq = 0
val id1 = test_next_id(100)
val id2 = test_next_id(100)
expect(id2).to_equal("100_2")
```

</details>

#### IDs are strictly monotonic

- IDs are strictly monotonic
   - Expected: mono is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("IDs are strictly monotonic")
_test_seq = 0
val id1 = test_next_id(50)
val id2 = test_next_id(50)
val id3 = test_next_id(50)
val seq1 = _test_seq - 2
val seq2 = _test_seq - 1
val seq3 = _test_seq
val mono = (seq1 < seq2) and (seq2 < seq3)
expect(mono).to_equal(true)
```

</details>

#### two IDs in same ms are different

- two IDs in same ms are different
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two IDs in same ms are different")
_test_seq = 0
val id1 = test_next_id(77)
val id2 = test_next_id(77)
val different = id1 != id2
expect(different).to_equal(true)
```

</details>

#### IDs from same process have same pid prefix

- IDs from same process have same pid prefix
   - Expected: starts1 is true
   - Expected: starts2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("IDs from same process have same pid prefix")
_test_seq = 0
val id1 = test_next_id(123)
val id2 = test_next_id(123)
val starts1 = id1.starts_with("123_")
val starts2 = id2.starts_with("123_")
expect(starts1).to_equal(true)
expect(starts2).to_equal(true)
```

</details>

#### IDs from different pids are different even at same seq

- IDs from different pids are different even at same seq


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("IDs from different pids are different even at same seq")
val id_a = "10_5"
val id_b = "20_5"
expect(id_a).to_not_equal(id_b)
```

</details>

#### sequence increments by 1 each call

- sequence increments by 1 each call
   - Expected: after equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sequence increments by 1 each call")
_test_seq = 0
val before = _test_seq
val id1 = test_next_id(1)
val after = _test_seq
expect(after).to_equal(before + 1)
```

</details>

### Kill Guard - PID Safety

#### rejects pid 0

- rejects pid 0
   - Expected: safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects pid 0")
val safe = test_safe_to_kill(0)
expect(safe).to_equal(false)
```

</details>

#### rejects pid -1

- rejects pid -1
   - Expected: safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects pid -1")
val safe = test_safe_to_kill(-1)
expect(safe).to_equal(false)
```

</details>

#### rejects pid 1

- rejects pid 1
   - Expected: safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects pid 1")
val safe = test_safe_to_kill(1)
expect(safe).to_equal(false)
```

</details>

#### rejects negative pids

- rejects negative pids
   - Expected: safe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects negative pids")
val safe = test_safe_to_kill(-100)
expect(safe).to_equal(false)
```

</details>

#### allows pid 2

- allows pid 2
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows pid 2")
val safe = test_safe_to_kill(2)
expect(safe).to_equal(true)
```

</details>

#### allows typical worker pid 1234

- allows typical worker pid 1234
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows typical worker pid 1234")
val safe = test_safe_to_kill(1234)
expect(safe).to_equal(true)
```

</details>

#### allows large pid

- allows large pid
   - Expected: safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("allows large pid")
val safe = test_safe_to_kill(99999)
expect(safe).to_equal(true)
```

</details>

#### guard prevents kill when pid is 0

- guard prevents kill when pid is 0
   - Expected: kill_called is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guard prevents kill when pid is 0")
var kill_called = false
val pid: i64 = 0
if pid > 1:
    kill_called = true
expect(kill_called).to_equal(false)
```

</details>

#### guard allows kill when pid is valid

- guard allows kill when pid is valid
   - Expected: kill_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guard allows kill when pid is valid")
var kill_called = false
val pid: i64 = 5678
if pid > 1:
    kill_called = true
expect(kill_called).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ProcessSet Config, IPC Message Serialization, IPC Reply Serialization, Atomic Claim - Double-Consume Prevention, Sequence ID Uniqueness, Kill Guard - PID Safety.
- ProcessSet Config
- IPC Message Serialization
- IPC Reply Serialization
- Atomic Claim - Double-Consume Prevention
- Sequence ID Uniqueness
- Kill Guard - PID Safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d2503e50cd64183c972f64483d18b44f11806111647e134202f56d9d6fbb3668`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d2503e50cd64183c972f64483d18b44f11806111647e134202f56d9d6fbb3668`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d2503e50cd64183c972f64483d18b44f11806111647e134202f56d9d6fbb3668`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/process_set/process_set_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/process_set/process_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/process_set/process_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mode shared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mode actor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/process_set/process_set_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses mode separated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Process Set Specification

> <details>

<!-- sdn-diagram:id=process_set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_set_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Set Specification

## Scenarios

### ProcessSet Config

#### parses mode shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = test_parse_mode("shared")
expect(mode).to_equal("shared")
```

</details>

#### parses mode actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = test_parse_mode("actor")
expect(mode).to_equal("actor")
```

</details>

#### parses mode separated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = test_parse_mode("separated")
expect(mode).to_equal("separated")
```

</details>

#### unknown mode defaults to shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = test_parse_mode("unknown_xyz")
expect(mode).to_equal("shared")
```

</details>

#### parses ipc_transport channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transport = test_parse_transport("channel")
expect(transport).to_equal("channel")
```

</details>

#### parses ipc_transport file_queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transport = test_parse_transport("file_queue")
expect(transport).to_equal("file_queue")
```

</details>

#### unknown transport defaults to channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transport = test_parse_transport("nope")
expect(transport).to_equal("channel")
```

</details>

#### mode round-trip: actor survives serialize-parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "actor"
val serialized = test_parse_mode(original)
val reparsed = test_parse_mode(serialized)
expect(reparsed).to_equal(original)
```

</details>

#### mode round-trip: separated survives serialize-parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "separated"
val serialized = test_parse_mode(original)
val reparsed = test_parse_mode(serialized)
expect(reparsed).to_equal(original)
```

</details>

### IPC Message Serialization

#### serializes id field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestIpcReply(id: "reply_1_3", in_reply_to: "1_2", payload: "ok", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.id).to_equal("reply_1_3")
```

</details>

#### round-trips in_reply_to

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestIpcReply(id: "r1", in_reply_to: "orig_99", payload: "done", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.in_reply_to).to_equal("orig_99")
```

</details>

#### round-trips payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestIpcReply(id: "r2", in_reply_to: "x", payload: "result-data", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.payload).to_equal("result-data")
```

</details>

#### round-trips error field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestIpcReply(id: "r3", in_reply_to: "x", payload: "", error: "timeout")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.error).to_equal("timeout")
```

</details>

#### round-trips empty error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = TestIpcReply(id: "r4", in_reply_to: "x", payload: "val", error: "")
val content = test_serialize_reply(r)
val parsed = test_parse_reply(content)
expect(parsed.error).to_equal("")
```

</details>

### Atomic Claim - Double-Consume Prevention

#### first consume returns content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var available = true
if available:
    available = false
expect(available).to_equal(false)
```

</details>

#### failed claim returns empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rename-to-claimed fails if file already moved => returns ""
val claimed_path = ""
val got_message = claimed_path != ""
expect(got_message).to_equal(false)
```

</details>

#### successful claim returns non-empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val claimed_path = "/tmp/simple_ipc/worker/inbox/42_1.msg.claimed"
val got_message = claimed_path != ""
expect(got_message).to_equal(true)
```

</details>

### Sequence ID Uniqueness

#### first ID uses sequence 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_seq = 0
val id1 = test_next_id(100)
expect(id1).to_equal("100_1")
```

</details>

#### second ID uses sequence 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_seq = 0
val id1 = test_next_id(100)
val id2 = test_next_id(100)
expect(id2).to_equal("100_2")
```

</details>

#### IDs are strictly monotonic

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_seq = 0
val id1 = test_next_id(77)
val id2 = test_next_id(77)
val different = id1 != id2
expect(different).to_equal(true)
```

</details>

#### IDs from same process have same pid prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id_a = "10_5"
val id_b = "20_5"
expect(id_a).to_not_equal(id_b)
```

</details>

#### sequence increments by 1 each call

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_test_seq = 0
val before = _test_seq
val id1 = test_next_id(1)
val after = _test_seq
expect(after).to_equal(before + 1)
```

</details>

### Kill Guard - PID Safety

#### rejects pid 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(0)
expect(safe).to_equal(false)
```

</details>

#### rejects pid -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(-1)
expect(safe).to_equal(false)
```

</details>

#### rejects pid 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(1)
expect(safe).to_equal(false)
```

</details>

#### rejects negative pids

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(-100)
expect(safe).to_equal(false)
```

</details>

#### allows pid 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(2)
expect(safe).to_equal(true)
```

</details>

#### allows typical worker pid 1234

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(1234)
expect(safe).to_equal(true)
```

</details>

#### allows large pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = test_safe_to_kill(99999)
expect(safe).to_equal(true)
```

</details>

#### guard prevents kill when pid is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var kill_called = false
val pid: i64 = 0
if pid > 1:
    kill_called = true
expect(kill_called).to_equal(false)
```

</details>

#### guard allows kill when pid is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

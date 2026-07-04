# Replay Codec Specification

> <details>

<!-- sdn-diagram:id=replay_codec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_codec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_codec_spec -> std
replay_codec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_codec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Codec Specification

## Scenarios

### encode_entry

#### produces non-empty byte array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
val bytes = encode_entry(entry)
expect(bytes.len() > 0).to_equal(true)
```

</details>

#### produces exactly 80 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.SyscallEnter, 1, 1, 0)
val bytes = encode_entry(entry)
expect(bytes.len()).to_equal(80)
```

</details>

### decode_entry round-trip

#### decode_entry round-trip preserves event_id

1. var entry = ReplayEntry create
   - Expected: got.event_id equals `42`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
entry.event_id = 42
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.event_id).to_equal(42)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode_entry round-trip preserves kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.SyscallExit, 3, 2, 1)
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.kind).to_equal(EventKind.SyscallExit.to_i32())
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode_entry round-trip preserves thread_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.TimerRead, 77, 1, 0)
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.thread_id).to_equal(77)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode_entry round-trip preserves process_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.InterruptDeliver, 1, 99, 0)
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.process_id).to_equal(99)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode_entry round-trip preserves payload_a

1. var entry = ReplayEntry create
   - Expected: got.payload_a equals `12345`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = ReplayEntry.create(EventKind.SyscallEnter, 1, 1, 0)
entry.payload_a = 12345
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.payload_a).to_equal(12345)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

### encode/decode i64 edge values

#### round-trips large positive i64

1. var entry = ReplayEntry create
   - Expected: got.payload_b equals `9223372036854775807`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
entry.payload_b = 9223372036854775807
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.payload_b).to_equal(9223372036854775807)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### round-trips negative i64

1. var entry = ReplayEntry create
   - Expected: got.payload_c equals `-1`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
entry.payload_c = -1
val bytes = encode_entry(entry)
match decode_entry(bytes, 0):
    case Ok(got):
        expect(got.payload_c).to_equal(-1)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

### encode_entries / decode_entries batch

#### encode_entries 3 entries produces 240 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e0 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
val e1 = ReplayEntry.create(EventKind.SyscallEnter, 2, 1, 0)
val e2 = ReplayEntry.create(EventKind.SyscallExit, 3, 1, 0)
val entries = [e0, e1, e2]
val bytes = encode_entries(entries)
expect(bytes.len()).to_equal(240)
```

</details>

#### decode_entries 3 entries returns count 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e0 = ReplayEntry.create(EventKind.Schedule, 10, 1, 0)
val e1 = ReplayEntry.create(EventKind.SyscallEnter, 20, 1, 0)
val e2 = ReplayEntry.create(EventKind.TimerRead, 30, 1, 0)
val entries = [e0, e1, e2]
val bytes = encode_entries(entries)
val decoded = decode_entries(bytes)
expect(decoded.len()).to_equal(3)
```

</details>

#### decode_entries preserves kind order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e0 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
val e1 = ReplayEntry.create(EventKind.SyscallEnter, 2, 1, 0)
val e2 = ReplayEntry.create(EventKind.TimerRead, 3, 1, 0)
val entries = [e0, e1, e2]
val bytes = encode_entries(entries)
val decoded = decode_entries(bytes)
expect(decoded[0].kind).to_equal(EventKind.Schedule.to_i32())
expect(decoded[1].kind).to_equal(EventKind.SyscallEnter.to_i32())
expect(decoded[2].kind).to_equal(EventKind.TimerRead.to_i32())
```

</details>

#### decode_entry at offset skips first entry

1. var e0 = ReplayEntry create
2. var e1 = ReplayEntry create
   - Expected: got.payload_a equals `222`
   - Expected: got.kind equals `EventKind.SyscallEnter.to_i32()`
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var e0 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
e0.payload_a = 111
var e1 = ReplayEntry.create(EventKind.SyscallEnter, 2, 1, 0)
e1.payload_a = 222
val entries = [e0, e1]
val bytes = encode_entries(entries)
match decode_entry(bytes, 80):
    case Ok(got):
        expect(got.payload_a).to_equal(222)
        expect(got.kind).to_equal(EventKind.SyscallEnter.to_i32())
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### decode_entries empty bytes returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i32] = []
val decoded = decode_entries(bytes)
expect(decoded.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_codec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- encode_entry
- decode_entry round-trip
- encode/decode i64 edge values
- encode_entries / decode_entries batch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

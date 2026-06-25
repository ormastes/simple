# Replay Codec Roundtrip Specification

> <details>

<!-- sdn-diagram:id=replay_codec_roundtrip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_codec_roundtrip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_codec_roundtrip_spec -> std
replay_codec_roundtrip_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_codec_roundtrip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Codec Roundtrip Specification

## Scenarios

### ReplayEntry codec roundtrip

#### encode then decode preserves event_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = ReplayEntry.create(EventKind.Schedule, 10, 20, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.event_id == e.event_id
expect(ok).to_equal(true)
```

</details>

#### encode then decode preserves thread_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = ReplayEntry.create(EventKind.SyscallEnter, 42, 1, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.thread_id == 42
expect(ok).to_equal(true)
```

</details>

#### encode then decode preserves kind

1. ok = de kind == EventKind IpcSend to i32
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = ReplayEntry.create(EventKind.IpcSend, 5, 1, 0)
val bytes = encode_entry(e)
val r = decode_entry(bytes, 0)
var ok = false
if val Ok(de) = r:
    ok = de.kind == EventKind.IpcSend.to_i32()
expect(ok).to_equal(true)
```

</details>

#### encode produces 80 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
val bytes = encode_entry(e)
expect(bytes.len()).to_equal(80)
```

</details>

#### decode_entry on insufficient bytes returns Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short: [i32] = [0, 1, 2]
val r = decode_entry(short, 0)
var is_err = true
if val Ok(_) = r:
    is_err = false
expect(is_err).to_equal(true)
```

</details>

#### encode_entries then decode_entries roundtrips two events

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = ReplayEntry.create(EventKind.ThreadCreate, 11, 1, 0)
val e2 = ReplayEntry.create(EventKind.ThreadExit, 12, 1, 0)
val entries = [e1, e2]
val bytes = encode_entries(entries)
val decoded = decode_entries(bytes)
expect(decoded.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_codec_roundtrip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ReplayEntry codec roundtrip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

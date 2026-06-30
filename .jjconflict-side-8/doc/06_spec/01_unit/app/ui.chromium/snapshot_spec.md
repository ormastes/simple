# Snapshot Specification

> _The `--record session.bin` flag surface._

<!-- sdn-diagram:id=snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

snapshot_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snapshot Specification

## Scenarios

### Chromium M11 parse_record_flag
_The `--record session.bin` flag surface._

#### empty argv yields a disabled flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = []
val flag = parse_record_flag(argv)
expect(flag.is_recording() == false).to_be_true()
```

</details>

#### argv without --record yields a disabled flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = ["ui.chromium", "--foo", "bar"]
val flag = parse_record_flag(argv)
expect(flag.is_recording() == false).to_be_true()
```

</details>

#### space-separated --record sets the path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = ["ui.chromium", "--record", "session.bin"]
val flag = parse_record_flag(argv)
expect(flag.is_recording()).to_be_true()
expect(flag.target_path() == "session.bin").to_be_true()
```

</details>

#### equals-separated --record= sets the path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = ["ui.chromium", "--record=trace.bin"]
val flag = parse_record_flag(argv)
expect(flag.is_recording()).to_be_true()
expect(flag.target_path() == "trace.bin").to_be_true()
```

</details>

#### dangling --record falls back to disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv: [text] = ["ui.chromium", "--record"]
val flag = parse_record_flag(argv)
expect(flag.is_recording() == false).to_be_true()
```

</details>

#### disabled factory reports empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = RecordFlag.disabled()
expect(flag.target_path() == "").to_be_true()
```

</details>

### Chromium M11 snapshot_hash_bytes
_Pure-Simple FNV-1a-style hash — the determinism spine of M11.""_

#### empty buffer returns the init value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect(snapshot_hash_bytes(empty) == snapshot_hash_init()).to_be_true()
```

</details>

#### hashing is stable across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [1, 2, 3, 4]
val a = snapshot_hash_bytes(bytes)
val b = snapshot_hash_bytes(bytes)
expect(a == b).to_be_true()
```

</details>

#### different content yields different hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = snapshot_hash_bytes([1, 2, 3, 4])
val b = snapshot_hash_bytes([1, 2, 3, 5])
expect(a != b).to_be_true()
```

</details>

#### step-by-step hash matches bulk hash

1. var acc = snapshot hash init
2. acc = snapshot hash step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [9, 8, 7]
var acc = snapshot_hash_init()
for byte_val in bytes:
    acc = snapshot_hash_step(acc, byte_val)
expect(acc == snapshot_hash_bytes(bytes)).to_be_true()
```

</details>

### Chromium M11 SnapshotRecorder
_Sequence assignment and inactive-mode short-circuiting._

#### inactive recorder does not append frames

1. var r = SnapshotRecorder new
2. r record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = SnapshotRecorder.new(RecordFlag.disabled())
r.record_pixels(1, 1, [0])
expect(r.frame_count() == 0).to_be_true()
```

</details>

#### active recorder assigns monotonic sequence numbers

1. var r = SnapshotRecorder new
2. r record pixels
3. r record pixels
4. r record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = SnapshotRecorder.new(RecordFlag.enabled_at("x.bin"))
r.record_pixels(1, 1, [1])
r.record_pixels(1, 1, [2])
r.record_pixels(1, 1, [3])
expect(r.frame_count() == 3).to_be_true()
expect(r.frames[0].seq == 0).to_be_true()
expect(r.frames[1].seq == 1).to_be_true()
expect(r.frames[2].seq == 2).to_be_true()
```

</details>

#### frame width and height are preserved

1. var r = SnapshotRecorder new


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = SnapshotRecorder.new(RecordFlag.enabled_at("x.bin"))
val f = r.record_pixels(4, 3, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
expect(f.width == 4).to_be_true()
expect(f.height == 3).to_be_true()
expect(f.pixel_count() == 12).to_be_true()
```

</details>

#### finalize produces a session pointing at the flag path

1. var r = SnapshotRecorder new
2. r record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = SnapshotRecorder.new(RecordFlag.enabled_at("out.bin"))
r.record_pixels(1, 1, [42])
val session = r.finalize()
expect(session.destination() == "out.bin").to_be_true()
expect(session.frame_count() == 1).to_be_true()
```

</details>

### Chromium M11 SnapshotSession wire format
_`to_wire` layout and `decode_wire` inverse property._

#### wire header starts with MAGIC and VERSION

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = build_golden_session()
val wire = session.to_wire()
expect(wire[0] == SNAPSHOT_MAGIC).to_be_true()
expect(wire[1] == SNAPSHOT_VERSION).to_be_true()
```

</details>

#### wire word count matches the predicted length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = build_golden_session()
val wire = session.to_wire()
expect(wire.len() == session.wire_word_count()).to_be_true()
```

</details>

#### wire encodes six words per frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = build_golden_session()
val wire = session.to_wire()
val payload = wire.len() - 3
val per = SNAPSHOT_FIELDS_PER_FRAME
expect(payload == session.frame_count() * per).to_be_true()
```

</details>

#### decode_wire reconstructs the same frame count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = build_golden_session()
val wire = session.to_wire()
val decoded = decode_wire(wire)
expect(decoded.is_ok()).to_be_true()
expect(decoded.frames.len() == session.frame_count()).to_be_true()
```

</details>

#### decode_wire preserves every frame field

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = build_golden_session()
val wire = session.to_wire()
val decoded = decode_wire(wire)
var ok = true
var i = 0
while i < session.frame_count():
    val orig = session.frames[i]
    val back = decoded.frames[i]
    if orig.matches(back) == false:
        ok = false
    i = i + 1
expect(ok).to_be_true()
```

</details>

### Chromium M11 decode_wire error handling
_Truncation and header validation._

#### empty buffer is reported as truncated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
val decoded = decode_wire(empty)
expect(decoded.status == REPLAY_TRUNCATED).to_be_true()
```

</details>

#### bad magic is reported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad: [i64] = [0, SNAPSHOT_VERSION, 0]
val decoded = decode_wire(bad)
expect(decoded.status == REPLAY_BAD_MAGIC).to_be_true()
```

</details>

#### bad version is reported

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad: [i64] = [SNAPSHOT_MAGIC, 99, 0]
val decoded = decode_wire(bad)
expect(decoded.status == REPLAY_BAD_VERSION).to_be_true()
```

</details>

#### short frame payload is reported as truncated

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Claims one frame but provides zero payload words.
val bad: [i64] = [SNAPSHOT_MAGIC, SNAPSHOT_VERSION, 1]
val decoded = decode_wire(bad)
expect(decoded.status == REPLAY_TRUNCATED).to_be_true()
```

</details>

### Chromium M11 replay_session
_Frame-for-frame byte-identical comparison._

#### golden vs golden replays cleanly

1. var live = SnapshotRecorder new
2. live record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val golden = build_golden_session()
# Build a fresh live recorder from the same deterministic source.
var live = SnapshotRecorder.new(RecordFlag.enabled_at("live.bin"))
var seq = 0
while seq < golden.frame_count():
    val pixels: [i64] = [seq, seq + 17, (seq * 3) + 5, (seq * 7) + 11]
    live.record_pixels(2, 2, pixels)
    seq = seq + 1
val report = replay_session(golden, live)
expect(report.is_ok()).to_be_true()
expect(report.frames_checked == golden.frame_count()).to_be_true()
```

</details>

#### mismatched frame count is reported

1. var live = SnapshotRecorder new
2. live record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val golden = build_golden_session()
var live = SnapshotRecorder.new(RecordFlag.enabled_at("live.bin"))
live.record_pixels(2, 2, [0, 17, 5, 11])
val report = replay_session(golden, live)
expect(report.status == REPLAY_LENGTH_MISMATCH).to_be_true()
```

</details>

#### divergent pixels are reported as frame mismatch

1. var live = SnapshotRecorder new
2. var pixels: [i64] = [seq, seq + 17,
3. pixels = [999, seq + 17,
4. live record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val golden = build_golden_session()
var live = SnapshotRecorder.new(RecordFlag.enabled_at("live.bin"))
var seq = 0
while seq < golden.frame_count():
    # One flipped byte on the first frame.
    var pixels: [i64] = [seq, seq + 17, (seq * 3) + 5, (seq * 7) + 11]
    if seq == 0:
        pixels = [999, seq + 17, (seq * 3) + 5, (seq * 7) + 11]
    live.record_pixels(2, 2, pixels)
    seq = seq + 1
val report = replay_session(golden, live)
expect(report.status == REPLAY_FRAME_MISMATCH).to_be_true()
expect(report.mismatch_at == 0).to_be_true()
```

</details>

#### replay_wire round-trips through the wire buffer

1. var live = SnapshotRecorder new
2. live record pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val golden = build_golden_session()
val wire = golden.to_wire()
var live = SnapshotRecorder.new(RecordFlag.enabled_at("live.bin"))
var seq = 0
while seq < golden.frame_count():
    val pixels: [i64] = [seq, seq + 17, (seq * 3) + 5, (seq * 7) + 11]
    live.record_pixels(2, 2, pixels)
    seq = seq + 1
val report = replay_wire(wire, live)
expect(report.is_ok()).to_be_true()
```

</details>

### Chromium M11 replay_wm_compare_regression

#### wm_compare regression replay is green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = replay_wm_compare_regression()
expect(report.is_ok()).to_be_true()
```

</details>

#### wm_compare regression checks at least three frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = replay_wm_compare_regression()
expect(report.frames_checked >= 3).to_be_true()
```

</details>

#### wm_compare regression reports no mismatch sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = replay_wm_compare_regression()
expect(report.mismatch_at == -1).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chromium M11 parse_record_flag
- Chromium M11 snapshot_hash_bytes
- Chromium M11 SnapshotRecorder
- Chromium M11 SnapshotSession wire format
- Chromium M11 decode_wire error handling
- Chromium M11 replay_session
- Chromium M11 replay_wm_compare_regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

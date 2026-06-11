# Actor Snapshot Specification

> <details>

<!-- sdn-diagram:id=actor_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=actor_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

actor_snapshot_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=actor_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Actor Snapshot Specification

## Scenarios

### ActorSnapshot

### creation

#### creates with ActorSnapshot__new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("hello", 1, 100, "src-1")
expect(snap.state()).to_equal("hello")
```

</details>

#### state() returns the correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new(42, 0, 0, "worker")
expect(snap.state()).to_equal(42)
```

</details>

#### version() returns version number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("data", 5, 10, "node-a")
expect(snap.version()).to_equal(5)
```

</details>

#### timestamp() returns timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("data", 3, 77, "node-b")
expect(snap.timestamp()).to_equal(77)
```

</details>

#### source() returns source identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("val", 0, 0, "worker-7")
expect(snap.source()).to_equal("worker-7")
```

</details>

### is_from

#### returns true for matching source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new(nil, 0, 0, "origin-1")
expect(snap.is_from("origin-1")).to_equal(true)
```

</details>

#### returns false for non-matching source

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new(nil, 0, 0, "origin-1")
expect(snap.is_from("origin-2")).to_equal(false)
```

</details>

### metadata

#### with_metadata returns new snapshot with metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("st", 0, 0, "s1")
val snap2 = snap.with_metadata("key", "value")
expect(snap2.metadata("key")).to_equal("value")
```

</details>

#### original snapshot unchanged after with_metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("st", 0, 0, "s1")
val snap2 = snap.with_metadata("key", "value")
expect(snap.has_metadata("key")).to_equal(false)
```

</details>

#### has_metadata returns true for existing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("st", 0, 0, "s1")
val snap2 = snap.with_metadata("color", "red")
expect(snap2.has_metadata("color")).to_equal(true)
```

</details>

#### has_metadata returns false for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("st", 0, 0, "s1")
expect(snap.has_metadata("missing")).to_equal(false)
```

</details>

#### metadata returns nil for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("data", 0, 0, "s1")
expect(snap.metadata("nope")).to_be_nil()
```

</details>

#### with_metadata preserves other fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("payload", 3, 99, "src-x")
val snap2 = snap.with_metadata("tag", "v1")
expect(snap2.state()).to_equal("payload")
expect(snap2.version()).to_equal(3)
expect(snap2.timestamp()).to_equal(99)
expect(snap2.source()).to_equal("src-x")
```

</details>

#### multiple metadata entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new("d", 0, 0, "s")
val s2 = snap.with_metadata("a", 1)
val s3 = s2.with_metadata("b", 2)
expect(s3.metadata("a")).to_equal(1)
expect(s3.metadata("b")).to_equal(2)
```

</details>

### snapshot with nil state

#### handles nil state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new(nil, 0, 0, "s1")
expect(snap.state()).to_be_nil()
```

</details>

#### handles array state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = ActorSnapshot.new([1, 2, 3], 1, 5, "arr-src")
expect(snap.state()).to_equal([1, 2, 3])
```

</details>

### ActorState

### creation

#### creates with initial state

1. var st = ActorState new
   - Expected: st.current() equals `initial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("initial", "worker-1")
expect(st.current()).to_equal("initial")
```

</details>

#### version starts at 0

1. var st = ActorState new
   - Expected: st.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(100, "w1")
expect(st.version()).to_equal(0)
```

</details>

#### source returns identifier

1. var st = ActorState new
   - Expected: st.source() equals `my-actor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(nil, "my-actor")
expect(st.source()).to_equal("my-actor")
```

</details>

#### ActorState__named creates with nil initial

1. var st = ActorState named
   - Expected: st.source() equals `lazy-actor`
   - Expected: st.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.named("lazy-actor")
expect(st.current()).to_be_nil()
expect(st.source()).to_equal("lazy-actor")
expect(st.version()).to_equal(0)
```

</details>

### update

#### update replaces state

1. var st = ActorState new
2. st update
   - Expected: st.current() equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("old", "w")
st.update("new")
expect(st.current()).to_equal("new")
```

</details>

#### update increments version

1. var st = ActorState new
2. st update
   - Expected: st.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(0, "w")
st.update(1)
expect(st.version()).to_equal(1)
```

</details>

#### multiple updates increment version correctly

1. var st = ActorState new
2. st update
3. st update
4. st update
   - Expected: st.version() equals `3`
   - Expected: st.current() equals `d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("a", "w")
st.update("b")
st.update("c")
st.update("d")
expect(st.version()).to_equal(3)
expect(st.current()).to_equal("d")
```

</details>

### update_with

#### applies function to current state

1. var st = ActorState new
2. st update with
   - Expected: st.current() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(10, "calc")
st.update_with(_1 * 2)
expect(st.current()).to_equal(20)
```

</details>

#### increments version

1. var st = ActorState new
2. st update with
   - Expected: st.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(5, "calc")
st.update_with(_1 + 1)
expect(st.version()).to_equal(1)
```

</details>

### snapshot

#### creates snapshot of current state

1. var st = ActorState new
   - Expected: snap.state() equals `data`
   - Expected: snap.version() equals `0`
   - Expected: snap.source() equals `w-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("data", "w-1")
val snap = st.snapshot()
expect(snap.state()).to_equal("data")
expect(snap.version()).to_equal(0)
expect(snap.source()).to_equal("w-1")
```

</details>

#### snapshot isolated from subsequent updates

1. var st = ActorState new
2. st update
   - Expected: snap.state() equals `before`
   - Expected: snap.version() equals `0`
   - Expected: st.current() equals `after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("before", "w")
val snap = st.snapshot()
st.update("after")
expect(snap.state()).to_equal("before")
expect(snap.version()).to_equal(0)
expect(st.current()).to_equal("after")
```

</details>

#### snapshot_with uses custom state

1. var st = ActorState new
   - Expected: snap.state() equals `custom-view`
   - Expected: snap.version() equals `0`
   - Expected: snap.source() equals `w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new([1, 2, 3], "w")
val snap = st.snapshot_with("custom-view")
expect(snap.state()).to_equal("custom-view")
expect(snap.version()).to_equal(0)
expect(snap.source()).to_equal("w")
```

</details>

### metadata

#### set_metadata propagates to snapshots

1. var st = ActorState new
2. st set metadata
   - Expected: snap.has_metadata("env") is true
   - Expected: snap.metadata("env") equals `production`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("data", "w")
st.set_metadata("env", "production")
val snap = st.snapshot()
expect(snap.has_metadata("env")).to_equal(true)
expect(snap.metadata("env")).to_equal("production")
```

</details>

#### set_metadata overwrites existing key

1. var st = ActorState new
2. st set metadata
3. st set metadata
   - Expected: snap.metadata("key") equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new("d", "w")
st.set_metadata("key", "v1")
st.set_metadata("key", "v2")
val snap = st.snapshot()
expect(snap.metadata("key")).to_equal("v2")
```

</details>

### multiple updates and snapshots

#### snapshots at different versions

1. var st = ActorState new
2. st update
3. st update
   - Expected: snap0.state() equals `0`
   - Expected: snap0.version() equals `0`
   - Expected: snap1.state() equals `10`
   - Expected: snap1.version() equals `1`
   - Expected: snap2.state() equals `20`
   - Expected: snap2.version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var st = ActorState.new(0, "counter")
val snap0 = st.snapshot()
st.update(10)
val snap1 = st.snapshot()
st.update(20)
val snap2 = st.snapshot()
expect(snap0.state()).to_equal(0)
expect(snap0.version()).to_equal(0)
expect(snap1.state()).to_equal(10)
expect(snap1.version()).to_equal(1)
expect(snap2.state()).to_equal(20)
expect(snap2.version()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/actor_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ActorSnapshot
- creation
- is_from
- metadata
- snapshot with nil state
- ActorState
- creation
- update
- update_with
- snapshot
- metadata
- multiple updates and snapshots

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

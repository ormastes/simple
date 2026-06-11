# Versioned Snapshot Specification

> <details>

<!-- sdn-diagram:id=versioned_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=versioned_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

versioned_snapshot_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=versioned_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Versioned Snapshot Specification

## Scenarios

### VersionedSnapshot

### creation

#### creates with initial value at version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(100)
expect(vs.current()).to_equal(100)
expect(vs.version()).to_equal(0)
```

</details>

#### creates with string initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new("hello")
expect(vs.current()).to_equal("hello")
```

</details>

#### creates with nil initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(nil)
expect(vs.current()).to_be_nil()
```

</details>

#### creates with custom max_history

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.with_history("start", 3)
expect(vs.current()).to_equal("start")
expect(vs.version()).to_equal(0)
```

</details>

### current

#### returns initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
expect(vs.current()).to_equal(42)
```

</details>

#### returns latest value after updates

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: vs.current() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(1)
vs.update(2)
vs.update(3)
expect(vs.current()).to_equal(3)
```

</details>

### version

#### starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(0)
expect(vs.version()).to_equal(0)
```

</details>

#### increments on each update

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: vs.version() equals `1`
3. vs update
   - Expected: vs.version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(0)
vs.update(10)
expect(vs.version()).to_equal(1)
vs.update(20)
expect(vs.version()).to_equal(2)
```

</details>

### at_version

#### returns value at version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(100)
expect(vs.at_version(0)).to_equal(100)
```

</details>

#### returns value at specific version

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: vs.at_version(0) equals `a`
   - Expected: vs.at_version(1) equals `b`
   - Expected: vs.at_version(2) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new("a")
vs.update("b")
vs.update("c")
expect(vs.at_version(0)).to_equal("a")
expect(vs.at_version(1)).to_equal("b")
expect(vs.at_version(2)).to_equal("c")
```

</details>

#### returns nil for missing version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(10)
expect(vs.at_version(99)).to_be_nil()
```

</details>

#### returns nil for negative version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(10)
expect(vs.at_version(-1)).to_be_nil()
```

</details>

### has_version

#### returns true for existing version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(10)
expect(vs.has_version(0)).to_equal(true)
```

</details>

#### returns false for missing version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(10)
expect(vs.has_version(5)).to_equal(false)
```

</details>

#### tracks updated versions

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: vs.has_version(0) is true
   - Expected: vs.has_version(1) is true
   - Expected: vs.has_version(2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(0)
vs.update(1)
expect(vs.has_version(0)).to_equal(true)
expect(vs.has_version(1)).to_equal(true)
expect(vs.has_version(2)).to_equal(false)
```

</details>

### version_count

#### starts at 1 with initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(10)
expect(vs.version_count()).to_equal(1)
```

</details>

#### grows with updates

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: vs.version_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(0)
vs.update(1)
vs.update(2)
expect(vs.version_count()).to_equal(3)
```

</details>

### snapshot

#### creates frozen snapshot of current state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
val snap = vs.snapshot()
expect(snap.get()).to_equal(42)
expect(snap.get_version()).to_equal(0)
```

</details>

#### snapshot reflects latest update

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: snap.get() equals `3`
   - Expected: snap.get_version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(1)
vs.update(2)
vs.update(3)
val snap = vs.snapshot()
expect(snap.get()).to_equal(3)
expect(snap.get_version()).to_equal(2)
```

</details>

#### snapshot is immutable after creation

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: snap.get() equals `10`
   - Expected: snap.get_version() equals `0`
   - Expected: vs.current() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(10)
val snap = vs.snapshot()
vs.update(20)
vs.update(30)
expect(snap.get()).to_equal(10)
expect(snap.get_version()).to_equal(0)
expect(vs.current()).to_equal(30)
```

</details>

### Snapshot__new

#### creates snapshot directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = Snapshot.new(5, "data")
expect(snap.get()).to_equal("data")
expect(snap.get_version()).to_equal(5)
```

</details>

#### creates snapshot with nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = Snapshot.new(0, nil)
expect(snap.get()).to_be_nil()
expect(snap.get_version()).to_equal(0)
```

</details>

### history

#### returns all version entries

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: h.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new("a")
vs.update("b")
vs.update("c")
val h = vs.history()
expect(h.len()).to_equal(3)
```

</details>

#### entries contain version and value

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: h[0][0] equals `0`
   - Expected: h[0][1] equals `10`
   - Expected: h[1][0] equals `1`
   - Expected: h[1][1] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(10)
vs.update(20)
val h = vs.history()
expect(h[0][0]).to_equal(0)
expect(h[0][1]).to_equal(10)
expect(h[1][0]).to_equal(1)
expect(h[1][1]).to_equal(20)
```

</details>

#### initial state has one entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vs = VersionedSnapshot.new(42)
val h = vs.history()
expect(h.len()).to_equal(1)
expect(h[0][0]).to_equal(0)
expect(h[0][1]).to_equal(42)
```

</details>

### history_since

#### returns entries from given version onwards

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
   - Expected: h.len() equals `2`
   - Expected: h[0][1] equals `b`
   - Expected: h[1][1] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new("a")
vs.update("b")
vs.update("c")
val h = vs.history_since(1)
expect(h.len()).to_equal(2)
expect(h[0][1]).to_equal("b")
expect(h[1][1]).to_equal("c")
```

</details>

#### returns all entries when version is 0

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: h.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(10)
vs.update(20)
val h = vs.history_since(0)
expect(h.len()).to_equal(2)
```

</details>

#### returns empty when version is beyond current

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: h.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(10)
vs.update(20)
val h = vs.history_since(99)
expect(h.len()).to_equal(0)
```

</details>

### update

#### adds new version

1. var vs = VersionedSnapshot new
2. vs update
   - Expected: vs.current() equals `2`
   - Expected: vs.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(1)
vs.update(2)
expect(vs.current()).to_equal(2)
expect(vs.version()).to_equal(1)
```

</details>

#### multiple updates track all values

1. var vs = VersionedSnapshot new
2. vs update
3. vs update
4. vs update
   - Expected: vs.current() equals `30`
   - Expected: vs.version() equals `3`
   - Expected: vs.at_version(1) equals `10`
   - Expected: vs.at_version(2) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(0)
vs.update(10)
vs.update(20)
vs.update(30)
expect(vs.current()).to_equal(30)
expect(vs.version()).to_equal(3)
expect(vs.at_version(1)).to_equal(10)
expect(vs.at_version(2)).to_equal(20)
```

</details>

### update_with

#### applies function to current value

1. var vs = VersionedSnapshot new
2. vs update with
   - Expected: vs.current() equals `20`
   - Expected: vs.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(10)
vs.update_with(_1 * 2)
expect(vs.current()).to_equal(20)
expect(vs.version()).to_equal(1)
```

</details>

#### chains function applications

1. var vs = VersionedSnapshot new
2. vs update with
3. vs update with
   - Expected: vs.current() equals `20`
   - Expected: vs.at_version(1) equals `2`
   - Expected: vs.at_version(2) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.new(1)
vs.update_with(_1 + 1)
vs.update_with(_1 * 10)
expect(vs.current()).to_equal(20)
expect(vs.at_version(1)).to_equal(2)
expect(vs.at_version(2)).to_equal(20)
```

</details>

### max_history trimming

#### trims oldest entries when exceeding max_history

1. var vs = VersionedSnapshot with history
2. vs update
3. vs update
4. vs update
   - Expected: vs.version_count() equals `3`
   - Expected: vs.has_version(0) is false
   - Expected: vs.has_version(1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.with_history(0, 3)
vs.update(1)
vs.update(2)
vs.update(3)
# 4 entries total, max is 3 -- version 0 should be trimmed
expect(vs.version_count()).to_equal(3)
expect(vs.has_version(0)).to_equal(false)
expect(vs.has_version(1)).to_equal(true)
```

</details>

#### retains latest entries

1. var vs = VersionedSnapshot with history
2. vs update
3. vs update
4. vs update
   - Expected: vs.current() equals `3`
   - Expected: vs.version_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.with_history(0, 2)
vs.update(1)
vs.update(2)
vs.update(3)
# max 2: should keep versions 2 and 3
expect(vs.current()).to_equal(3)
expect(vs.version_count()).to_equal(2)
```

</details>

#### at_version returns nil for trimmed versions

1. var vs = VersionedSnapshot with history
2. vs update
3. vs update
4. vs update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vs = VersionedSnapshot.with_history(0, 2)
vs.update(10)
vs.update(20)
vs.update(30)
expect(vs.at_version(0)).to_be_nil()
expect(vs.at_version(1)).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/versioned_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VersionedSnapshot
- creation
- current
- version
- at_version
- has_version
- version_count
- snapshot
- Snapshot__new
- history
- history_since
- update
- update_with
- max_history trimming

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

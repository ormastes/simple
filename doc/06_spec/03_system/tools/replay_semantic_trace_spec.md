# Replay Semantic Trace Specification

> <details>

<!-- sdn-diagram:id=replay_semantic_trace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_semantic_trace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_semantic_trace_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_semantic_trace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Semantic Trace Specification

## Scenarios

### SemanticEventKind to_i32

#### returns expected ordinals for core kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SemanticEventKind.FunctionEnter.to_i32()).to_equal(0)
expect(SemanticEventKind.FunctionExit.to_i32()).to_equal(1)
expect(SemanticEventKind.VariableWrite.to_i32()).to_equal(2)
expect(SemanticEventKind.ObjectAlloc.to_i32()).to_equal(3)
```

</details>

#### returns expected ordinals for ownership kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SemanticEventKind.ObjectDrop.to_i32()).to_equal(4)
expect(SemanticEventKind.OwnershipTransfer.to_i32()).to_equal(5)
expect(SemanticEventKind.BorrowStart.to_i32()).to_equal(6)
expect(SemanticEventKind.BorrowEnd.to_i32()).to_equal(7)
```

</details>

### SemanticEventKind from_i32

#### round-trips ownership transfer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SemanticEventKind.from_i32(5)
expect(kind.to_i32()).to_equal(5)
expect(kind.to_text()).to_equal("OwnershipTransfer")
```

</details>

#### round-trips async spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spawn_kind = SemanticEventKind.from_i32(8)
expect(spawn_kind.to_text()).to_equal("AsyncSpawn")
```

</details>

#### round-trips async yield and resume

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val yield_kind = SemanticEventKind.from_i32(9)
expect(yield_kind.to_text()).to_equal("AsyncYield")
val resume_kind = SemanticEventKind.from_i32(10)
expect(resume_kind.to_text()).to_equal("AsyncResume")
```

</details>

#### defaults to FunctionEnter for unknown values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = SemanticEventKind.from_i32(999)
expect(kind.to_i32()).to_equal(0)
```

</details>

### SemanticEventKind to_text

#### returns readable names for borrow kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SemanticEventKind.BorrowStart.to_text()).to_equal("BorrowStart")
expect(SemanticEventKind.BorrowEnd.to_text()).to_equal("BorrowEnd")
```

</details>

#### returns readable names for object kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SemanticEventKind.ObjectAlloc.to_text()).to_equal("ObjectAlloc")
expect(SemanticEventKind.ObjectDrop.to_text()).to_equal("ObjectDrop")
```

</details>

### SemanticEvent construction

#### create sets kind and zeroes other fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.ObjectAlloc)
expect(ev.kind).to_equal(3)
expect(ev.seq).to_equal(0)
expect(ev.thread_id).to_equal(0)
expect(ev.object_id).to_equal(0)
```

</details>

#### event_kind returns the enum from kind field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.AsyncYield)
val kind = ev.event_kind()
expect(kind.to_text()).to_equal("AsyncYield")
```

</details>

#### SEMANTIC_EVENT_SIZE is 68

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SEMANTIC_EVENT_SIZE).to_equal(68)
```

</details>

#### create with FunctionEnter sets kind 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.FunctionEnter)
expect(ev.kind).to_equal(0)
expect(ev.payload_a).to_equal(0)
expect(ev.payload_b).to_equal(0)
```

</details>

### TraceWriter creation

#### create initializes empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val writer = TraceWriter.create("/tmp/test.sst", 1000000)
expect(writer.event_count).to_equal(0)
expect(writer.next_seq).to_equal(0)
expect(writer.buffer.len()).to_equal(0)
expect(writer.output_path).to_equal("/tmp/test.sst")
```

</details>

#### create stores buffer capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val writer = TraceWriter.create("/tmp/test2.sst", 500000)
expect(writer.buffer_capacity).to_equal(500000)
expect(writer.write_pos).to_equal(0)
```

</details>

### TraceWriter emit

#### emit increments event_count and next_seq

1. var writer = TraceWriter create
2. writer emit
   - Expected: writer.event_count equals `1`
   - Expected: writer.next_seq equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var writer = TraceWriter.create("/tmp/test3.sst", 1000000)
val ev = SemanticEvent.create(SemanticEventKind.FunctionEnter)
writer.emit(ev)
expect(writer.event_count).to_equal(1)
expect(writer.next_seq).to_equal(1)
```

</details>

#### emit appends bytes to buffer

1. var writer = TraceWriter create
2. writer emit
   - Expected: writer.buffer.len() equals `68`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var writer = TraceWriter.create("/tmp/test4.sst", 1000000)
val ev = SemanticEvent.create(SemanticEventKind.ObjectAlloc)
writer.emit(ev)
expect(writer.buffer.len()).to_equal(68)
```

</details>

### ObjectId

#### stores type and alloc site

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = ObjectId(id: 1, type_name_id: 10, alloc_site_file: 5, alloc_site_line: 42, dropped: false)
expect(obj.id).to_equal(1)
expect(obj.type_name_id).to_equal(10)
expect(obj.alloc_site_file).to_equal(5)
expect(obj.alloc_site_line).to_equal(42)
expect(obj.dropped).to_equal(false)
```

</details>

#### to_text includes id and type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = ObjectId(id: 7, type_name_id: 3, alloc_site_file: 1, alloc_site_line: 99, dropped: false)
val s = obj.to_text()
expect(s).to_contain("7")
expect(s).to_contain("type=3")
```

</details>

### ObjectRegistry creation

#### create starts with next_id 1 and empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ObjectRegistry.create()
expect(reg.next_id).to_equal(1)
expect(reg.entries.len()).to_equal(0)
```

</details>

### ObjectRegistry register and lookup

#### register returns incrementing IDs

1. var reg = ObjectRegistry create
   - Expected: id1 equals `1`
   - Expected: id2 equals `2`
   - Expected: reg.entries.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ObjectRegistry.create()
val id1 = reg.register(10, 1, 42)
val id2 = reg.register(20, 2, 99)
expect(id1).to_equal(1)
expect(id2).to_equal(2)
expect(reg.entries.len()).to_equal(2)
```

</details>

#### mark_dropped sets dropped flag

1. var reg = ObjectRegistry create
2. reg mark dropped
   - Expected: obj.dropped is true
   - Expected: "should find object" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ObjectRegistry.create()
val id1 = reg.register(10, 1, 42)
reg.mark_dropped(id1)
match reg.lookup(id1):
    case Some(obj):
        expect(obj.dropped).to_equal(true)
    case None:
        expect("should find object").to_equal("")
```

</details>

#### active_count excludes dropped objects

1. var reg = ObjectRegistry create
2. reg mark dropped
   - Expected: reg.active_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ObjectRegistry.create()
val id1 = reg.register(10, 1, 1)
val id2 = reg.register(20, 1, 2)
val id3 = reg.register(30, 1, 3)
reg.mark_dropped(id2)
expect(reg.active_count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_semantic_trace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SemanticEventKind to_i32
- SemanticEventKind from_i32
- SemanticEventKind to_text
- SemanticEvent construction
- TraceWriter creation
- TraceWriter emit
- ObjectId
- ObjectRegistry creation
- ObjectRegistry register and lookup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Replay Semantic Event Specification

> <details>

<!-- sdn-diagram:id=replay_semantic_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_semantic_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_semantic_event_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_semantic_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Semantic Event Specification

## Scenarios

### SemanticEventKind to_i32

#### FunctionEnter to_i32 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.FunctionEnter
expect(k.to_i32()).to_equal(0)
```

</details>

#### FunctionExit to_i32 returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.FunctionExit
expect(k.to_i32()).to_equal(1)
```

</details>

#### ObjectAlloc to_i32 returns 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.ObjectAlloc
expect(k.to_i32()).to_equal(3)
```

</details>

#### AsyncSpawn to_i32 returns 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.AsyncSpawn
expect(k.to_i32()).to_equal(8)
```

</details>

### SemanticEventKind from_i32 roundtrip

#### from_i32(0) gives FunctionEnter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.from_i32(0)
expect(k.to_i32()).to_equal(0)
```

</details>

#### from_i32(11) gives AsyncComplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = SemanticEventKind.from_i32(11)
expect(k.to_i32()).to_equal(11)
```

</details>

### SemanticEvent create

#### create sets kind field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.VariableWrite)
expect(ev.kind).to_equal(SemanticEventKind.VariableWrite.to_i32())
```

</details>

#### create initialises seq to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.ObjectDrop)
expect(ev.seq).to_equal(0)
```

</details>

#### event_kind() roundtrips back to BorrowStart

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = SemanticEvent.create(SemanticEventKind.BorrowStart)
val k = ev.event_kind()
expect(k.to_i32()).to_equal(6)
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_semantic_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SemanticEventKind to_i32
- SemanticEventKind from_i32 roundtrip
- SemanticEvent create

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

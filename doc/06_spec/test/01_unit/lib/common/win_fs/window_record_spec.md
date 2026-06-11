# WindowRecord Specification

> Record lifecycle: create / update / destroy semantics and generation counter.

<!-- sdn-diagram:id=window_record_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_record_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_record_spec -> std
window_record_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_record_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WindowRecord Specification

Record lifecycle: create / update / destroy semantics and generation counter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/win_fs/window_record_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Record lifecycle: create / update / destroy semantics and generation counter.

## Scenarios

### WindowRecord

### lifecycle

#### AC-2: creation yields Normal state and generation 1

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 100, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
expect rec.generation to_equal 1
```

</details>

#### AC-2: update_title bumps generation

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 100, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val next = window_update_title(rec, "Transfer")
expect next.title to_equal "Transfer"
expect next.generation to_be_greater_than 1
```

</details>

#### AC-2: mark_destroyed sets state to Destroyed

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 100, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val gone = window_mark_destroyed(rec)
expect gone.state to_equal WindowState.Destroyed
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

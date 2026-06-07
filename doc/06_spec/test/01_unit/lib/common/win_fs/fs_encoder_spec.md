# FsEncoder Specification

> Exercises round-trip `WindowRecord` → `FsTree` → `WindowRecord` and schema

<!-- sdn-diagram:id=fs_encoder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_encoder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_encoder_spec -> std
fs_encoder_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_encoder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FsEncoder Specification

Exercises round-trip `WindowRecord` → `FsTree` → `WindowRecord` and schema

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/win_fs/fs_encoder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises round-trip `WindowRecord` → `FsTree` → `WindowRecord` and schema
path layout `/<app>/<wid>/{title,state,geometry,buffer,meta,actions/*}`.

## Scenarios

### FsEncoder

### round-trip

#### AC-2: encode then decode reproduces record identity

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 42,
    generation: 1,
    app: "banking",
    title: "Account",
    state: WindowState.Normal,
    geometry: Rect(x: 10, y: 20, w: 800, h: 600),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val tree = encode_record(rec)
val decoded = decode_tree(tree)
expect decoded.ok to_equal true
expect decoded.value.wid to_equal 42
expect decoded.value.app to_equal "banking"
expect decoded.value.title to_equal "Account"
```

</details>

### path schema

#### AC-2: encodes /<app>/<wid>/title

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. expect tree has path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 7, generation: 1, app: "mail", title: "Inbox",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 100, h: 100),
    buffer_ref: BufferRef(kind: "shm", handle: 1, bytes: 1),
    acl_id_path: id_path_intern("id.user.mail.view"))
val tree = encode_record(rec)
expect tree_has_path(tree, "/mail/7/title") to_equal true
```

</details>

#### AC-2: encodes state, geometry, buffer, meta, actions

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. expect tree has path
5. expect tree has path
6. expect tree has path
7. expect tree has path
8. expect tree has path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 7, generation: 1, app: "mail", title: "Inbox",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 100, h: 100),
    buffer_ref: BufferRef(kind: "shm", handle: 1, bytes: 1),
    acl_id_path: id_path_intern("id.user.mail.view"))
val tree = encode_record(rec)
expect tree_has_path(tree, "/mail/7/state") to_equal true
expect tree_has_path(tree, "/mail/7/geometry") to_equal true
expect tree_has_path(tree, "/mail/7/buffer") to_equal true
expect tree_has_path(tree, "/mail/7/meta") to_equal true
expect tree_has_path(tree, "/mail/7/actions") to_equal true
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

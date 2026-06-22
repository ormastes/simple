# Host Win-FS shim Specification

> Host shim publishes same tree under a temp runtime dir via the same encoder.

<!-- sdn-diagram:id=winfs_shim_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=winfs_shim_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

winfs_shim_host_spec -> std
winfs_shim_host_spec -> lib
winfs_shim_host_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=winfs_shim_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Win-FS shim Specification

Host shim publishes same tree under a temp runtime dir via the same encoder.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/simple_process_manager/winfs_shim_host_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Host shim publishes same tree under a temp runtime dir via the same encoder.
Verified by encoding the same record through the shared encoder and comparing
path layout + bytes.

## Scenarios

### winfs_shim_host

### publish via shared encoder

#### AC-4: publish writes /<app>/<wid>/title under runtime dir

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shim = WinFsShimHost.new_for_test(runtime_dir: "/tmp/spm_winfs_host")
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val result = shim.publish(rec)
expect result.ok to_equal true
val title = read_file("/tmp/spm_winfs_host/banking/42/title")
expect title to_equal "Acct"
```

</details>

#### AC-4: paths match the shared encoder schema (no drift)

1. geometry: Rect
2. buffer ref: BufferRef
3. acl id path: id path intern
4. expect tree has path
5. expect tree has path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val tree = encode_record(rec)
expect tree_has_path(tree, "/banking/42/title") to_equal true
expect tree_has_path(tree, "/banking/42/state") to_equal true
```

</details>

### grep sentinel

#### AC-4: winfs_shim_host.spl imports from common/win_fs/fs_encoder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/app/simple_process_manager/winfs_shim_host.spl")
expect source to_contain "use lib.common.win_fs.fs_encoder"
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

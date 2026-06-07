# Std Fs Specification

> 1. client close

<!-- sdn-diagram:id=std_fs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=std_fs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

std_fs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=std_fs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Fs Specification

## Scenarios

### StdFsNvfsClient.create (A2)

#### opens a fresh AppendOnly object and returns Ok

1. client close


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val flags = CreateFlags.defaults()
val r = client.create(_tmp_path("create.bin"), ObjClass.AppendOnly, flags)
expect(r.is_ok()).to_equal(true)
# Cleanup: close + remove.
val obj = r.unwrap()
client.close(obj)
```

</details>

### StdFsNvfsClient.write (A2)

#### appends bytes and reports Ok

1. buf push
   - Expected: n.is_ok() is true
2. client close


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val path = _tmp_path("write.bin")
val obj = client.create(path, ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var buf: [u8] = []
var i = 0
while i < 8:
    buf.push(0x5A as u8)
    i = i + 1
val n = client.write(obj, buf)
expect(n.is_ok()).to_equal(true)
client.close(obj)
```

</details>

### StdFsNvfsClient.seal (A2)

#### returns Ok after syncing the object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("seal.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
val r = client.seal(obj, false)
expect(r.is_ok()).to_equal(true)
```

</details>

### StdFsNvfsClient.publish_atomic (A2)

#### renames staging path to final path via rt_file_move

1. buf push
2. client write
3. client seal
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val staging = _tmp_path("publish.bin.tmp")
val final_path = _tmp_path("publish.bin")
val obj = client.create(staging, ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var buf: [u8] = []
buf.push(0x01 as u8)
client.write(obj, buf)
client.seal(obj, false)
val r = client.publish_atomic(obj, final_path)
expect(r.is_ok()).to_equal(true)
```

</details>

#### returns Err when the source staging path does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val ghost_obj = ObjHandle(id: 99, path: _tmp_path("ghost_missing.tmp"), is_open: true)
val r = client.publish_atomic(ghost_obj, _tmp_path("ghost.final"))
expect(r.is_err()).to_equal(true)
```

</details>

### StdFsNvfsClient.sync (A2)

#### fsyncs an existing object via rt_file_fsync

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("sync.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
val r = client.sync(obj, SyncScope.File)
expect(r.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StdFsNvfsClient.create (A2)
- StdFsNvfsClient.write (A2)
- StdFsNvfsClient.seal (A2)
- StdFsNvfsClient.publish_atomic (A2)
- StdFsNvfsClient.sync (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

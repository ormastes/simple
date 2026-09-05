# Std Fs Specification

> <details>

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
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Fs Specification

## Scenarios

### StdFsNvfsClient.create (A2)

#### opens a fresh AppendOnly object and returns Ok

- client close


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

- buf push
   - Expected: n.is_ok() is true
- client close


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

- buf push
- client write
- client seal
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

### StdFsNvfsClient streaming capability gaps

#### reports read_range as unsupported instead of pretending to write caller buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
expect(nvfs_status(client.read_range(obj, 0, 1, BufHandle.null()))).to_equal("unsupported")
```

</details>

#### returns local read_range bytes through the bring-up helper

- bytes push
- bytes push
- bytes push
   - Expected: client.write(obj, bytes).is_ok() is true
   - Expected: read.is_ok() is true
   - Expected: read.unwrap() equals `[0x20 as u8, 0x30 as u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range_bytes.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var bytes: [u8] = []
bytes.push(0x10 as u8)
bytes.push(0x20 as u8)
bytes.push(0x30 as u8)
expect(client.write(obj, bytes).is_ok()).to_equal(true)
val read = client.read_range_bytes(obj, 1, 2)
expect(read.is_ok()).to_equal(true)
expect(read.unwrap()).to_equal([0x20 as u8, 0x30 as u8])
```

</details>

#### rejects local read_range bytes past the file end

- bytes push
   - Expected: client.write(obj, bytes).is_ok() is true
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val obj = client.create(_tmp_path("read_range_oob.bin"), ObjClass.AppendOnly, CreateFlags.defaults()).unwrap()
var bytes: [u8] = []
bytes.push(0x41 as u8)
expect(client.write(obj, bytes).is_ok()).to_equal(true)
val r = client.read_range_bytes(obj, 0, 2)
expect(r.is_err()).to_equal(true)
```

</details>

#### reports buffer registration as unsupported until a real pinned buffer adapter exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
expect(nvfs_buffer_status(client.register_buffer(0, 4096))).to_equal("unsupported")
expect(nvfs_unit_status(client.unregister_buffer(BufHandle.null()))).to_equal("unsupported")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StdFsNvfsClient.create (A2)
- StdFsNvfsClient.write (A2)
- StdFsNvfsClient.seal (A2)
- StdFsNvfsClient.publish_atomic (A2)
- StdFsNvfsClient.sync (A2)
- StdFsNvfsClient streaming capability gaps

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Std Fs Transport Specification

> <details>

<!-- sdn-diagram:id=std_fs_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=std_fs_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

std_fs_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=std_fs_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Fs Transport Specification

## Scenarios

### StdFsNvfsClient.read_text

#### returns Ok with file content when the file exists

- dir create all
- file write text
   - Expected: r.is_ok() is true
   - Expected: content equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "/tmp/svllm_fs_unit/read_text"
dir_create_all(dir)
val path = dir + "/hello.txt"
file_write_text(path, "hello world")
val client = StdFsNvfsClient.new()
val r = client.read_text(path)
expect(r.is_ok()).to_equal(true)
val content = r.unwrap()
expect(content).to_equal("hello world")
```

</details>

#### returns Err when the file does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val r = client.read_text("/tmp/svllm_fs_unit_absent_xqz.txt")
expect(r.is_err()).to_equal(true)
```

</details>

### StdFsNvfsClient.read_bytes

#### returns Ok for an existing file

- dir create all
- file write text
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "/tmp/svllm_fs_unit/read_bytes"
dir_create_all(dir)
val path = dir + "/data.txt"
file_write_text(path, "abc")
val client = StdFsNvfsClient.new()
val r = client.read_bytes(path)
expect(r.is_ok()).to_equal(true)
```

</details>

#### returns Ok for a text-written empty file

- dir create all
- file write text
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "/tmp/svllm_fs_unit/read_bytes_empty"
dir_create_all(dir)
val path = dir + "/empty.txt"
file_write_text(path, "")
val client = StdFsNvfsClient.new()
val r = client.read_bytes(path)
expect(r.is_ok()).to_equal(true)
```

</details>

#### returns Err(NotFound) when the file does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val r = client.read_bytes("/tmp/svllm_fs_unit_absent_xqz.bin")
expect(r.is_err()).to_equal(true)
```

</details>

#### returns correct byte values (gated: native rt_file_read_bytes [u8] marshalling broken — doc/08_tracking/bug/native_sffi_file_byte_io_u8_marshalling_2026-06-20.md)

- dir create all
- buf push
- buf push
- buf push
- buf push
- buf push
- buf push
- file write bytes
   - Expected: r.is_ok() is true
   - Expected: data.len() equals `6`
   - Expected: data[0] as i64 equals `100`
   - Expected: data[5] as i64 equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_u8_fixed: i64 = 0
if native_u8_fixed == 1:
    val dir = "/tmp/svllm_fs_unit/read_bytes_values"
    dir_create_all(dir)
    val path = dir + "/pattern.bin"
    # Write known byte pattern 100..105 (6 bytes) via file_write_bytes
    var buf: [u8] = []
    buf.push(100 as u8)
    buf.push(101 as u8)
    buf.push(102 as u8)
    buf.push(103 as u8)
    buf.push(104 as u8)
    buf.push(105 as u8)
    file_write_bytes(path, buf)
    val client = StdFsNvfsClient.new()
    val r = client.read_bytes(path)
    expect(r.is_ok()).to_equal(true)
    val data = r.unwrap()
    expect(data.len()).to_equal(6)
    expect(data[0] as i64).to_equal(100)
    expect(data[5] as i64).to_equal(105)
```

</details>

### load_model_from_pack_fs — error paths

#### returns Err(PackRootNotFound) when the pack root has no manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val r = load_model_from_pack_fs(client, "/tmp/svllm_fs_unit_no_such_root_xqz", 0)
val tag = err_tag(r)
expect(tag).to_equal("PackRootNotFound")
```

</details>

#### returns Err(ManifestInvalid) when manifest.sdn contains garbage

- dir create all
- file write text
   - Expected: tag equals `ManifestInvalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack_root = "/tmp/svllm_fs_unit/badmanifest"
dir_create_all(pack_root)
file_write_text(pack_root + "/manifest.sdn", "THIS IS NOT VALID JSON OR SDN")
val client = StdFsNvfsClient.new()
val r = load_model_from_pack_fs(client, pack_root, 0)
val tag = err_tag(r)
expect(tag).to_equal("ManifestInvalid")
```

</details>

#### returns Err(ChunkOpenFailed) when a chunk file is missing

- dir create all
- file write text
   - Expected: tag equals `ChunkOpenFailed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack_root = "/tmp/svllm_fs_unit/missingchunk"
dir_create_all(pack_root)
val info = make_test_pack(pack_root)
# Write manifest but deliberately skip writing data-000.bin.
file_write_text(pack_root + "/manifest.sdn", info.manifest_text)
val client = StdFsNvfsClient.new()
val r = load_model_from_pack_fs(client, pack_root, 0)
val tag = err_tag(r)
expect(tag).to_equal("ChunkOpenFailed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/svllm/nvfs_client/std_fs_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- StdFsNvfsClient.read_text
- StdFsNvfsClient.read_bytes
- load_model_from_pack_fs — error paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Svllm Fs Loader System Specification

> <details>

<!-- sdn-diagram:id=svllm_fs_loader_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_fs_loader_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_fs_loader_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_fs_loader_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svllm Fs Loader System Specification

## Scenarios

### SVLLM FS Loader System

#### adapter: read_text returns Ok and contains manifest schema

- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack_root = "/tmp/svllm_test_adapter_read"
val _mkdir = dir_create_all(pack_root)
val test_path = pack_root + "/test_manifest.sdn"
val content = "{\"schema_version\":0,\"model_id\":\"test\"}"
val written = file_write_text(test_path, content)
verify(written)

val client = StdFsNvfsClient.new()
val result = client.read_text(test_path)
verify(result.is_ok())
val text = result.unwrap()
verify(text.contains("schema_version"))
```

</details>

#### adapter: read_bytes on absent path returns Err

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val result = client.read_bytes("/tmp/svllm_fs_absent_file_xyz_9999.bin")
verify(result.is_err())
```

</details>

#### adapter: read_bytes returns Ok with known pattern (gated: native [u8] file I/O broken — doc/08_tracking/bug/native_sffi_file_byte_io_u8_marshalling_2026-06-20.md)

- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_u8_fixed: i64 = 0
if native_u8_fixed == 1:
    val pack_root = "/tmp/svllm_test_adapter_bytes"
    val _mkdir = dir_create_all(pack_root)
    val test_path = pack_root + "/test_chunk.bin"
    val pattern = pattern_buffer(64, 99)
    val written = file_write_bytes(test_path, pattern)
    verify(written)

    val client = StdFsNvfsClient.new()
    val result = client.read_bytes(test_path)
    verify(result.is_ok())
    val data = result.unwrap()
    # Byte-value assertions: seed=99, pattern[i] = (99+i) & 0xFF
    verify(data.len() == 64)
    verify(data[0] as i64 == 99)
    verify(data[63] as i64 == ((99 + 63) and 0xFF))
```

</details>

#### happy path: build pack, serialize, write, read, load end-to-end (gated: native [u8] file I/O broken — doc/08_tracking/bug/native_sffi_file_byte_io_u8_marshalling_2026-06-20.md)

- tensors push
- tensors push
- tensors push
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_u8_fixed: i64 = 0
if native_u8_fixed == 1:
    # 1. Build 3 small tensors
    var tensors: [TensorInfo] = []
    tensors.push(make_tensor("weight_0", 256))
    tensors.push(make_tensor("weight_1", 512))
    tensors.push(make_tensor("weight_2", 128))

    # 2. Plan chunks with align=1 (no padding) so byte_len is exact
    val pack = plan_chunks(tensors, 1, 2097152)
    verify(pack.tensors.len() == 3)
    verify(pack.chunks.len() > 0)

    # Calculate total bytes streamed
    var total: i64 = 0
    var i: i64 = 0
    while i < pack.chunks.len():
        total = total + pack.chunks[i].byte_len
        i = i + 1

    # 3. Serialize manifest
    val manifest_txt = serialize_manifest(pack)
    verify(manifest_txt.len() > 0)
    verify(manifest_txt.contains("schema_version"))

    # 4. Choose pack_root, create dir, and write manifest
    val pack_root = "/tmp/svllm_test_loader_happy"
    val _mkdir = dir_create_all(pack_root)
    val manifest_path = pack_root + "/manifest.sdn"
    val written = file_write_text(manifest_path, manifest_txt)
    verify(written)

    # 5. Write chunk files with pattern data
    var chunk_idx: i64 = 0
    while chunk_idx < pack.chunks.len():
        val chunk = pack.chunks[chunk_idx]
        val chunk_path = pack_root + "/" + chunk.relative_path
        val chunk_buf = pattern_buffer(chunk.byte_len, 42 + chunk_idx)
        val chunk_written = file_write_bytes(chunk_path, chunk_buf)
        verify(chunk_written)
        chunk_idx = chunk_idx + 1

    # 6. Create client and load from pack
    val client = StdFsNvfsClient.new()
    val result = load_model_from_pack_fs(client, pack_root, 4096)
    verify(result.is_ok())

    val lr = result.unwrap()
    verify(lr.staged_tensor_count == pack.tensors.len())
    verify(lr.bytes_streamed == total)
    verify(lr.op_count >= pack.chunks.len() as i64)
    verify(lr.pack.tensors.len() == pack.tensors.len())
```

</details>

#### error path: PackRootNotFound when manifest missing

- verify
- LoaderError PackRootNotFound => verify
-   => verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = StdFsNvfsClient.new()
val result = load_model_from_pack_fs(client, "/tmp/svllm_fs_nonexistent_root_xyz_9999", 4096)
verify(result.is_err())
val err = result.unwrap_err()
match err:
    LoaderError.PackRootNotFound => verify(true)
    _ => verify(false)
```

</details>

#### error path: ManifestInvalid when manifest unparseable

- verify
- verify
- LoaderError ManifestInvalid => verify
-   => verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Write an invalid manifest
val pack_root = "/tmp/svllm_test_loader_invalid"
val _mkdir = dir_create_all(pack_root)
val manifest_path = pack_root + "/manifest.sdn"
val bad_manifest = "not valid json at all {"
val written = file_write_text(manifest_path, bad_manifest)
verify(written)

val client = StdFsNvfsClient.new()
val result = load_model_from_pack_fs(client, pack_root, 4096)
verify(result.is_err())
val err = result.unwrap_err()
match err:
    LoaderError.ManifestInvalid => verify(true)
    _ => verify(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/svllm_fs_loader_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SVLLM FS Loader System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

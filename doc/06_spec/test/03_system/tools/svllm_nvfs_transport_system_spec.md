# Svllm Nvfs Transport System Specification

> <details>

<!-- sdn-diagram:id=svllm_nvfs_transport_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_nvfs_transport_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_nvfs_transport_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_nvfs_transport_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svllm Nvfs Transport System Specification

## Scenarios

### svllm NvfsClient transport — end-to-end streaming

#### happy path: pack, serialize, image, load with granule=4

- ts push
- ts push
- verify
- verify
- chunk paths push
- chunk bytes push
- verify
- verify
- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build 2 tensors: t1 (8 bytes, F32), t2 (12 bytes, F32).
var ts: [TensorInfo] = []
ts.push(TensorInfo(name: "t1", shape: [2], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 8))
ts.push(TensorInfo(name: "t2", shape: [3], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 12))

# Plan chunks with align=1, large preferred size -> single chunk.
val pack = plan_chunks(ts, 1, 100000)
verify(pack.chunks.len() >= 1)

# Compute total bytes in all chunks.
var total: i64 = 0
var ci = 0
while ci < pack.chunks.len():
    total = total + pack.chunks[ci].byte_len
    ci = ci + 1

# Serialize manifest to SDN text.
val manifest_text = serialize_manifest(pack)
verify(manifest_text.len() > 10)

# Build chunk byte buffers: one per chunk, filled with pattern 0xAB.
var chunk_paths: [text] = []
var chunk_bytes: [[u8]] = []
var i = 0
while i < pack.chunks.len():
    chunk_paths.push(pack.chunks[i].relative_path)
    chunk_bytes.push(fill_pattern(pack.chunks[i].byte_len, 0xAB as u8))
    i = i + 1

# Build in-memory NvfsClient image.
val client = mem_nvfs_image("/models/test1", manifest_text, chunk_paths, chunk_bytes)

# Load with granule=4.
val result_r = load_model_from_pack_via(client, "/models/test1", 4)
verify(result_r.is_ok())

val lr = result_r.unwrap()
verify(lr.staged_tensor_count == pack.tensors.len())
verify(lr.bytes_streamed == total)
verify(lr.op_count >= pack.chunks.len())
verify(lr.pack.tensors.len() == pack.tensors.len())
```

</details>

#### happy path: granule=0 (one op per chunk)

- ts push
- chunk paths push
- chunk bytes push
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts: [TensorInfo] = []
ts.push(TensorInfo(name: "w", shape: [4], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 16))

val pack = plan_chunks(ts, 1, 100000)
val manifest_text = serialize_manifest(pack)

var chunk_paths: [text] = []
var chunk_bytes: [[u8]] = []
var i = 0
while i < pack.chunks.len():
    chunk_paths.push(pack.chunks[i].relative_path)
    chunk_bytes.push(fill_pattern(pack.chunks[i].byte_len, 0xCD as u8))
    i = i + 1

val client = mem_nvfs_image("/models/test2", manifest_text, chunk_paths, chunk_bytes)
val result_r = load_model_from_pack_via(client, "/models/test2", 0)
verify(result_r.is_ok())

val lr = result_r.unwrap()
# granule=0 -> one op per chunk (simplest case).
verify(lr.op_count == pack.chunks.len())
```

</details>

#### error: wrong pack root returns PackRootNotFound

- ts push
- chunk paths push
- chunk bytes push
- verify
- Ok
- Err
- LoaderError PackRootNotFound => verify
-   => verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts: [TensorInfo] = []
ts.push(TensorInfo(name: "x", shape: [2], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 8))

val pack = plan_chunks(ts, 1, 100000)
val manifest_text = serialize_manifest(pack)

var chunk_paths: [text] = []
var chunk_bytes: [[u8]] = []
var i = 0
while i < pack.chunks.len():
    chunk_paths.push(pack.chunks[i].relative_path)
    chunk_bytes.push(fill_pattern(pack.chunks[i].byte_len, 0xEE as u8))
    i = i + 1

# Image stored at /models/m1, but load from /wrong/root.
val client = mem_nvfs_image("/models/m1", manifest_text, chunk_paths, chunk_bytes)
val result_r = load_model_from_pack_via(client, "/wrong/root", 4)
verify(result_r.is_err())

match result_r:
    Ok(_) => verify(false)
    Err(e) =>
        match e:
            LoaderError.PackRootNotFound => verify(true)
            _ => verify(false)
```

</details>

#### error: missing chunks returns ChunkOpenFailed

- ts push
- verify
- Ok
- Err
- LoaderError ChunkOpenFailed => verify
-   => verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts: [TensorInfo] = []
ts.push(TensorInfo(name: "y", shape: [3], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 12))

val pack = plan_chunks(ts, 1, 100000)
val manifest_text = serialize_manifest(pack)

# Build manifest but NO chunk objects (empty chunk_paths / chunk_bytes).
val client = mem_nvfs_image("/models/m2", manifest_text, [], [])
val result_r = load_model_from_pack_via(client, "/models/m2", 4)
verify(result_r.is_err())

match result_r:
    Ok(_) => verify(false)
    Err(e) =>
        match e:
            LoaderError.ChunkOpenFailed => verify(true)
            _ => verify(false)
```

</details>

#### error: malformed manifest returns ManifestInvalid

- ts push
- chunk paths push
- chunk bytes push
- verify
- Ok
- Err
- LoaderError ManifestInvalid => verify
-   => verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ts: [TensorInfo] = []
ts.push(TensorInfo(name: "z", shape: [2], dtype: Dtype.F32, chunk_id: 0, offset_in_chunk: 0, byte_len: 8))

val pack = plan_chunks(ts, 1, 100000)

var chunk_paths: [text] = []
var chunk_bytes: [[u8]] = []
var i = 0
while i < pack.chunks.len():
    chunk_paths.push(pack.chunks[i].relative_path)
    chunk_bytes.push(fill_pattern(pack.chunks[i].byte_len, 0xFF as u8))
    i = i + 1

# Pass garbage as manifest instead of valid SDN.
val client = mem_nvfs_image("/models/m3", "garbage text not valid sdn", chunk_paths, chunk_bytes)
val result_r = load_model_from_pack_via(client, "/models/m3", 4)
verify(result_r.is_err())

match result_r:
    Ok(_) => verify(false)
    Err(e) =>
        match e:
            LoaderError.ManifestInvalid => verify(true)
            _ => verify(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/svllm_nvfs_transport_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svllm NvfsClient transport — end-to-end streaming

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

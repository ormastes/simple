# Svllm Streaming Loader System Specification

> <details>

<!-- sdn-diagram:id=svllm_streaming_loader_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_streaming_loader_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_streaming_loader_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_streaming_loader_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svllm Streaming Loader System Specification

## Scenarios

### svllm streaming loader — tensor packing

#### plan_chunks creates a TensorPack from TensorInfos

- verify pack tensors len
- verify pack chunks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val t1 = TensorInfo(
    name: "b0",
    shape: [4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 8,
    byte_len: 12
)
val tensors: [TensorInfo] = [t0, t1]
val pack = plan_chunks(tensors, 1, 2097152)

verify pack.tensors.len() == 2
verify pack.chunks.len() >= 1
verify pack.preferred_chunk_bytes == 2097152
```

</details>

#### plan_chunks assigns chunk_id and aligned offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val t1 = TensorInfo(
    name: "b0",
    shape: [4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 8,
    byte_len: 16
)
val tensors: [TensorInfo] = [t0, t1]
val pack = plan_chunks(tensors, 1, 2097152)

verify pack.tensors[0].chunk_id >= 0
verify pack.tensors[1].chunk_id >= 0
verify pack.tensors[0].offset_in_chunk >= 0
verify pack.tensors[1].offset_in_chunk >= pack.tensors[0].offset_in_chunk
```

</details>

### svllm streaming loader — streaming pack

#### stream_pack gathers tensor bytes from chunk buffers

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val t1 = TensorInfo(
    name: "b0",
    shape: [4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 8,
    byte_len: 12
)
val tensors: [TensorInfo] = [t0, t1]
val pack = plan_chunks(tensors, 1, 2097152)

val chunk_byte_len = sum_chunk_bytes(pack)
val buf = make_pattern_buffer(chunk_byte_len)
val chunk_data: [[u8]] = [buf]

val ok = match stream_pack(pack, chunk_data):
    Ok(r): r.stages.len() == pack.tensors.len() and r.bytes_streamed == chunk_byte_len
    Err(e): false
verify ok
```

</details>

#### stream_pack validates chunk_data length

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)

val chunk_data: [[u8]] = []

val has_error = match stream_pack(pack, chunk_data):
    Ok(r): false
    Err(e): true
verify has_error
```

</details>

#### stream_pack validates chunk buffer sizes

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)

val short_buf: [u8] = [1, 2, 3]
val chunk_data: [[u8]] = [short_buf]

val has_error = match stream_pack(pack, chunk_data):
    Ok(r): false
    Err(e): true
verify has_error
```

</details>

#### stream_pack extracts tensor bytes with correct pattern

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)

val buf = make_pattern_buffer(pack.chunks[0].byte_len)
val chunk_data: [[u8]] = [buf]

val ok = match stream_pack(pack, chunk_data):
    Ok(r): r.stages.len() == 1 and r.stages[0].bytes.len() == pack.tensors[0].byte_len and r.stages[0].bytes[0] == (0 as u8) and r.stages[0].bytes[1] == (1 as u8)
    Err(e): false
verify ok
```

</details>

### svllm streaming loader — read planning

#### plan_stream builds read schedule with granule=0

- verify plan op count == pack chunks len
- verify plan total bytes == sum chunk bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val t1 = TensorInfo(
    name: "b0",
    shape: [4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 8,
    byte_len: 12
)
val tensors: [TensorInfo] = [t0, t1]
val pack = plan_chunks(tensors, 1, 2097152)

val plan = plan_stream(pack, 0)
verify plan.op_count == pack.chunks.len()
verify plan.total_bytes == sum_chunk_bytes(pack)
```

</details>

#### plan_stream splits large chunks by granule

- verify plan op count >= pack chunks len
- verify plan total bytes == sum chunk bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 100
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)

val granule: i64 = 4
val plan = plan_stream(pack, granule)
verify plan.granule == granule
verify plan.op_count >= pack.chunks.len()
verify plan.total_bytes == sum_chunk_bytes(pack)
```

</details>

### svllm streaming loader — manifest serialization

#### serialize_manifest produces text

- verify txt len
- verify txt contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)

val txt = serialize_manifest(pack)
verify txt.len() > 0
verify txt.contains("schema_version") == true
```

</details>

### svllm streaming loader — full integration

#### load_model_from_pack_streamed returns LoadResult on success

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val t1 = TensorInfo(
    name: "b0",
    shape: [4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 8,
    byte_len: 12
)
val tensors: [TensorInfo] = [t0, t1]
val pack = plan_chunks(tensors, 1, 2097152)

val manifest_text = serialize_manifest(pack)
val chunk_byte_len = sum_chunk_bytes(pack)
val buf = make_pattern_buffer(chunk_byte_len)
val chunk_data: [[u8]] = [buf]

val granule: i64 = 4
val plan = plan_stream(pack, granule)

val ok = match load_model_from_pack_streamed("/tmp/p", manifest_text, granule, chunk_data):
    Ok(lr): lr.staged_tensor_count == pack.tensors.len() and lr.bytes_streamed == chunk_byte_len and lr.op_count == plan.op_count and lr.pack.tensors.len() == pack.tensors.len()
    Err(e): false
verify ok
```

</details>

#### load_model_from_pack_streamed fails on invalid manifest

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_manifest_error = match load_model_from_pack_streamed("/tmp/p", "invalid sdn", 4, []):
    Ok(lr): false
    Err(e): is_manifest_invalid(e)
verify has_manifest_error
```

</details>

#### load_model_from_pack_streamed fails on empty chunk_data

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t0 = TensorInfo(
    name: "w0",
    shape: [2, 4],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 8
)
val tensors: [TensorInfo] = [t0]
val pack = plan_chunks(tensors, 1, 2097152)
val manifest_text = serialize_manifest(pack)

val has_chunk_error = match load_model_from_pack_streamed("/tmp/p", manifest_text, 4, []):
    Ok(lr): false
    Err(e): is_chunk_open_failed(e)
verify has_chunk_error
```

</details>

#### load_model_from_pack returns NvfsUnavailable

- Ok
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_nvfs_error = match load_model_from_pack("/tmp/p"):
    Ok(lr): false
    Err(e): is_nvfs_unavailable(e)
verify has_nvfs_error
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/svllm_streaming_loader_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svllm streaming loader — tensor packing
- svllm streaming loader — streaming pack
- svllm streaming loader — read planning
- svllm streaming loader — manifest serialization
- svllm streaming loader — full integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

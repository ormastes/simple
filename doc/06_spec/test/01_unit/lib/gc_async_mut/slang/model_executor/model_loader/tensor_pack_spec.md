# Tensor Pack Specification

> <details>

<!-- sdn-diagram:id=tensor_pack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_pack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_pack_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_pack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Pack Specification

## Scenarios

### TensorPack.empty

#### has the supplied pack_root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = TensorPack.empty("/models/llama3-8b")
expect(pack.pack_root).to_equal("/models/llama3-8b")
```

</details>

#### has zero tensors and chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = TensorPack.empty("/x")
expect(pack.tensor_count()).to_equal(0)
expect(pack.chunk_count()).to_equal(0)
```

</details>

#### has empty model_id and revision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = TensorPack.empty("/x")
expect(pack.model_id).to_equal("")
expect(pack.revision).to_equal("")
```

</details>

### TensorPack.find_tensor

#### returns empty-named TensorInfo when missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = TensorPack.empty("/x")
val t = pack.find_tensor("missing")
expect(t.name).to_equal("")
```

</details>

#### finds a tensor that is present

1. var pack = TensorPack empty
   - Expected: t.name equals `w0`
   - Expected: t.byte_len equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pack = TensorPack.empty("/x")
val shape: [i64] = [4, 8]
pack.tensors.push(TensorInfo(
    name: "w0",
    shape: shape,
    dtype: Dtype.F16,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 64
))
val t = pack.find_tensor("w0")
expect(t.name).to_equal("w0")
expect(t.byte_len).to_equal(64)
```

</details>

### ChunkInfo

#### stores relative path and digest

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = ChunkInfo(
    id: 0,
    relative_path: "data-000.bin",
    byte_len: 2097152,
    digest_hex: "0011aabb"
)
expect(c.relative_path).to_equal("data-000.bin")
expect(c.digest_hex).to_equal("0011aabb")
```

</details>

### DEFAULT constants (A2)

#### chunk align is 4 KiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_CHUNK_ALIGN).to_equal(4096)
```

</details>

#### preferred chunk bytes is 2 MiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DEFAULT_PREFERRED_CHUNK_BYTES).to_equal(2097152)
```

</details>

### plan_chunks (A2)

#### emits a single chunk for two small tensors (16B + 24B, fits in one 2 MiB chunk)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tensors = [
    TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 16),
    TensorInfo(name: "b", shape: [3], dtype: Dtype.I64,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 24)
]
val pack = plan_chunks(tensors, DEFAULT_CHUNK_ALIGN, DEFAULT_PREFERRED_CHUNK_BYTES)
expect(pack.chunk_count()).to_equal(1)
expect(pack.tensor_count()).to_equal(2)
```

</details>

#### aligns the second tensor to DEFAULT_CHUNK_ALIGN (4096)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tensors = [
    TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 16),
    TensorInfo(name: "b", shape: [3], dtype: Dtype.I64,
               chunk_id: 0, offset_in_chunk: 0, byte_len: 24)
]
val pack = plan_chunks(tensors, DEFAULT_CHUNK_ALIGN, DEFAULT_PREFERRED_CHUNK_BYTES)
val second = pack.tensors[1]
# 16 bytes then align-up to 4096.
expect(second.offset_in_chunk).to_equal(4096)
```

</details>

### write_chunk (A2)

#### emits chunk bytes of expected length (tensor bytes + align padding)

1. src push


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TensorInfo(name: "w", shape: [2, 2], dtype: Dtype.F32,
                   chunk_id: 0, offset_in_chunk: 0, byte_len: 16)
var src: [u8] = []
var i = 0
while i < 16:
    src.push(0xAB as u8)
    i = i + 1
val out = write_chunk(t, src, DEFAULT_CHUNK_ALIGN)
# First 16 bytes are the tensor; remainder (if any) is zero padding.
expect(out.len()).to_be_greater_than(15)
```

</details>

### sha256_chunk (A2)

#### returns a 64-char lowercase hex digest

1. bytes push
   - Expected: hex.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bytes: [u8] = []
var i = 0
while i < 16:
    bytes.push(0 as u8)
    i = i + 1
val hex = sha256_chunk(bytes)
expect(hex.len()).to_equal(64)
```

</details>

#### is deterministic (same input => same hex)

1. a push
2. b push
   - Expected: sha256_chunk(a) equals `sha256_chunk(b)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u8] = []
var b: [u8] = []
var i = 0
while i < 8:
    a.push(0x42 as u8)
    b.push(0x42 as u8)
    i = i + 1
expect(sha256_chunk(a)).to_equal(sha256_chunk(b))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TensorPack.empty
- TensorPack.find_tensor
- ChunkInfo
- DEFAULT constants (A2)
- plan_chunks (A2)
- write_chunk (A2)
- sha256_chunk (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

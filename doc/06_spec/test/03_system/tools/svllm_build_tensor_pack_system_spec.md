# Svllm Build Tensor Pack System Specification

> <details>

<!-- sdn-diagram:id=svllm_build_tensor_pack_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_build_tensor_pack_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_build_tensor_pack_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_build_tensor_pack_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svllm Build Tensor Pack System Specification

## Scenarios

### svllm build_tensor_pack round-trip

#### plan_chunks produces multi-chunk TensorPack

- var orig = plan chunks
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

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build 3 tensors, each ~1.5 MB.
val t1 = TensorInfo(
    name: "weights_layer1",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t2 = TensorInfo(
    name: "weights_layer2",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t3 = TensorInfo(
    name: "bias_layer3",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val tensors = [t1, t2, t3]

# Plan with 4 KiB alignment and 2 MiB preferred chunk size.
# Each 1.5 MB tensor fits in its own chunk; two tensors exceed 2 MiB.
var orig = plan_chunks(tensors, 4096, 2097152)

# Verify we got 3 chunks (one per tensor).
verify(orig.chunks.len() == 3)
verify(orig.tensors.len() == 3)

# Set model metadata so round-trip is non-trivial.
orig.model_id = "demo-model-v1"
orig.revision = "20260620"

# Verify tensors are assigned to chunks in order.
val t0 = orig.tensors[0]
verify(t0.name == "weights_layer1")
verify(t0.chunk_id == 0)

val t1_check = orig.tensors[1]
verify(t1_check.name == "weights_layer2")
verify(t1_check.chunk_id == 1)

val t2_check = orig.tensors[2]
verify(t2_check.name == "bias_layer3")
verify(t2_check.chunk_id == 2)
```

</details>

#### serialize_manifest produces well-formed text

- var pack = plan chunks
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

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = TensorInfo(
    name: "weights",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t2 = TensorInfo(
    name: "bias",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 1,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t3 = TensorInfo(
    name: "scale",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 2,
    offset_in_chunk: 0,
    byte_len: 1500000
)

var pack = plan_chunks([t1, t2, t3], 4096, 2097152)
pack.model_id = "demo-model"
pack.revision = "v1"

val txt = serialize_manifest(pack)

# Verify presence of key markers (order fixed by serialize_manifest).
verify(txt.contains("\"schema_version\":0"))
verify(txt.contains("\"model_id\":\"demo-model\""))
verify(txt.contains("\"revision\":\"v1\""))
verify(txt.contains("\"preferred_chunk_bytes\":2097152"))
verify(txt.contains("\"chunks\":["))
verify(txt.contains("\"tensors\":["))
verify(txt.char_at(0) == "{")
verify(txt.char_at(txt.len() - 1) == "}")
```

</details>

#### parse_manifest → serialize → parse round-trip

- var orig = plan chunks
- Ok
- verify
- verify
- verify
- verify
- verify
- verify
- Err
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = TensorInfo(
    name: "w1",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t2 = TensorInfo(
    name: "w2",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 1,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t3 = TensorInfo(
    name: "w3",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 2,
    offset_in_chunk: 0,
    byte_len: 1500000
)

var orig = plan_chunks([t1, t2, t3], 4096, 2097152)
orig.model_id = "test-model"
orig.revision = "r1"

# Serialize to text.
val txt = serialize_manifest(orig)

# Parse back.
val parse_result = parse_manifest(txt)
match parse_result:
    Ok(m) =>
        verify(m.schema_version == 0)
        verify(m.model_id == "test-model")
        verify(m.revision == "r1")
        verify(m.preferred_chunk_bytes == 2097152)
        # Verify the parsed manifest carries full tensor and chunk arrays.
        verify(m.tensors.len() == orig.tensors.len())
        verify(m.chunks.len() == orig.chunks.len())
    Err(e) =>
        verify(false)
```

</details>

#### build_tensor_pack reconstructs TensorPack from manifest

- var orig = plan chunks
- Ok
- Ok
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
- verify
- verify
- verify
- verify
- Err
- verify
- Err
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 92 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t1 = TensorInfo(
    name: "layer1_w",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t2 = TensorInfo(
    name: "layer2_w",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 1,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t3 = TensorInfo(
    name: "layer3_w",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 2,
    offset_in_chunk: 0,
    byte_len: 1500000
)

var orig = plan_chunks([t1, t2, t3], 4096, 2097152)
orig.model_id = "build-test"
orig.revision = "v2"

val txt = serialize_manifest(orig)

val parse_result = parse_manifest(txt)
match parse_result:
    Ok(m) =>
        # build_tensor_pack should reconstruct the full TensorPack.
        val build_result = build_tensor_pack("/tmp/pack", m)
        match build_result:
            Ok(rebuilt) =>
                # Verify array lengths.
                verify(rebuilt.tensors.len() == orig.tensors.len())
                verify(rebuilt.chunks.len() == orig.chunks.len())

                # Verify pack metadata.
                verify(rebuilt.model_id == orig.model_id)
                verify(rebuilt.preferred_chunk_bytes == orig.preferred_chunk_bytes)
                verify(rebuilt.pack_root == "/tmp/pack")

                # Verify tensor[0] field-level.
                val rebuilt_t0 = rebuilt.tensors[0]
                val orig_t0 = orig.tensors[0]
                verify(rebuilt_t0.name == orig_t0.name)
                verify(rebuilt_t0.chunk_id == orig_t0.chunk_id)
                verify(rebuilt_t0.byte_len == orig_t0.byte_len)
                verify(rebuilt_t0.offset_in_chunk == orig_t0.offset_in_chunk)
                verify(rebuilt_t0.shape.len() == orig_t0.shape.len())

                # Verify tensor[1] field-level — proves parser preserves all elements.
                val rebuilt_t1 = rebuilt.tensors[1]
                val orig_t1 = orig.tensors[1]
                verify(rebuilt_t1.name == orig_t1.name)
                verify(rebuilt_t1.chunk_id == orig_t1.chunk_id)
                verify(rebuilt_t1.offset_in_chunk == orig_t1.offset_in_chunk)
                verify(rebuilt_t1.byte_len == orig_t1.byte_len)
                verify(rebuilt_t1.shape.len() == orig_t1.shape.len())

                # Verify tensor[2] field-level.
                val rebuilt_t2 = rebuilt.tensors[2]
                val orig_t2 = orig.tensors[2]
                verify(rebuilt_t2.name == orig_t2.name)
                verify(rebuilt_t2.chunk_id == orig_t2.chunk_id)
                verify(rebuilt_t2.offset_in_chunk == orig_t2.offset_in_chunk)
                verify(rebuilt_t2.byte_len == orig_t2.byte_len)
                verify(rebuilt_t2.shape.len() == orig_t2.shape.len())

                # Verify chunk[0] field-level.
                val rebuilt_c0 = rebuilt.chunks[0]
                val orig_c0 = orig.chunks[0]
                verify(rebuilt_c0.id == orig_c0.id)
                verify(rebuilt_c0.byte_len == orig_c0.byte_len)
                verify(rebuilt_c0.relative_path == orig_c0.relative_path)

                # Verify chunk[last] (index 2) field-level — proves all chunks preserved.
                val last_idx = rebuilt.chunks.len() - 1
                val rebuilt_clast = rebuilt.chunks[last_idx]
                val orig_clast = orig.chunks[last_idx]
                verify(rebuilt_clast.id == orig_clast.id)
                verify(rebuilt_clast.byte_len == orig_clast.byte_len)
                verify(rebuilt_clast.relative_path == orig_clast.relative_path)
            Err(e) =>
                verify(false)
    Err(e) =>
        verify(false)
```

</details>

#### build_tensor_pack catches invariant violations

- var orig = plan chunks
- Ok
- Ok
- verify
- Err
- verify
- verify
- Err
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create a valid manifest, parse it, then mutate to violate invariants.
# Test that build_tensor_pack returns TensorChunkMismatch when tensors
# reference out-of-range chunk_ids or when tensors exist but chunks is empty.
val t1 = TensorInfo(
    name: "w1",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 0,
    offset_in_chunk: 0,
    byte_len: 1500000
)
val t2 = TensorInfo(
    name: "w2",
    shape: [1500000],
    dtype: Dtype.F32,
    chunk_id: 1,
    offset_in_chunk: 0,
    byte_len: 1500000
)

var orig = plan_chunks([t1, t2], 4096, 2097152)
orig.model_id = "bad-model"
orig.revision = "v1"

val txt = serialize_manifest(orig)

val parse_result = parse_manifest(txt)
match parse_result:
    Ok(m) =>
        # Mutate the parsed manifest to violate the invariant:
        # tensors without matching chunks (chunks array is empty).
        var bad = m
        bad.chunks = []

        # build_tensor_pack must detect this and return TensorChunkMismatch.
        val build_result = build_tensor_pack("/tmp/pack", bad)
        match build_result:
            Ok(p) =>
                # Should not succeed; invariant was violated.
                verify(false)
            Err(err) =>
                match err:
                    ManifestError.TensorChunkMismatch =>
                        # Correct: invariant was caught.
                        verify(true)
                    _ =>
                        # Wrong error variant.
                        verify(false)
    Err(e) =>
        verify(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/svllm_build_tensor_pack_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svllm build_tensor_pack round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

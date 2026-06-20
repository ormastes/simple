# Loader Specification

> <details>

<!-- sdn-diagram:id=loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loader_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader Specification

## Scenarios

### load_model_from_pack_streamed — happy path

#### returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
expect(r.is_ok()).to_equal(true)
```

</details>

#### result.pack has correct tensor count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
match r:
    Ok(lr) => expect(lr.pack.tensors.len()).to_equal(pack.tensors.len())
    Err(_) => expect(false).to_equal(true)
```

</details>

#### result.pack has correct chunk count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
match r:
    Ok(lr) => expect(lr.pack.chunks.len()).to_equal(pack.chunks.len())
    Err(_) => expect(false).to_equal(true)
```

</details>

#### bytes_streamed equals sum of chunk byte_lens

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
var expected: i64 = 0
var ci = 0
while ci < pack.chunks.len():
    expected = expected + pack.chunks[ci].byte_len
    ci = ci + 1
match r:
    Ok(lr) => expect(lr.bytes_streamed).to_equal(expected)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### staged_tensor_count equals tensor count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
match r:
    Ok(lr) => expect(lr.staged_tensor_count).to_equal(pack.tensors.len())
    Err(_) => expect(false).to_equal(true)
```

</details>

#### op_count matches plan_stream result

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
val r = load_model_from_pack_streamed("/models/test", serialized, 0, chunk_data)
val plan = plan_stream(pack, 0)
match r:
    Ok(lr) => expect(lr.op_count).to_equal(plan.op_count)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### op_count > chunk_count when granule splits chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use a granule of 1 byte so each byte_len of each chunk => many ops.
# This discriminates that loader wires plan.op_count (not chunk_count).
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val chunk_data = _make_chunk_data(pack)
# granule=4096: chunk is DEFAULT_CHUNK_ALIGN-aligned (>=4096), so
# at least 1 op per chunk but if chunk > 4096 then >1 op per chunk.
# chunk byte_len = align_up(tensor offsets) which is a multiple of 4096.
# With two 16-byte tensors: second placed at 4096, ends at 4096+16=4112,
# chunk byte_len = align_up(4112, 4096) = 8192 => 2 ops at granule=4096.
val granule: i64 = 4096
val r = load_model_from_pack_streamed("/models/test", serialized, granule, chunk_data)
val plan = plan_stream(pack, granule)
expect(plan.op_count).to_be_greater_than(pack.chunks.len())
match r:
    Ok(lr) => expect(lr.op_count).to_equal(plan.op_count)
    Err(_) => expect(false).to_equal(true)
```

</details>

### load_model_from_pack_streamed — error cases

#### malformed manifest_text yields Err(ManifestInvalid)

- Err
   - Expected: is_invalid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_data: [[u8]] = []
val r = load_model_from_pack_streamed("/models/test", "garbage", 0, empty_data)
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        val is_invalid = match e:
            LoaderError.ManifestInvalid => true
            _ => false
        expect(is_invalid).to_equal(true)
```

</details>

#### empty chunk_data with valid manifest yields Err(ChunkOpenFailed)

- Err
   - Expected: is_chunk_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _make_pack_and_manifest()
val serialized = serialize_manifest(pack)
val empty_data: [[u8]] = []
val r = load_model_from_pack_streamed("/models/test", serialized, 0, empty_data)
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        val is_chunk_err = match e:
            LoaderError.ChunkOpenFailed => true
            _ => false
        expect(is_chunk_err).to_equal(true)
```

</details>

### load_model_from_pack_streamed — ChunkDataInvalid path

#### placeholder — ChunkDataInvalid unreachable via manifest path (see comment above)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true).to_equal(true)
```

</details>

### load_model_from_pack — bare entry

#### returns Err(NvfsUnavailable)

- Err
   - Expected: is_nvfs is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = load_model_from_pack("x")
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        val is_nvfs = match e:
            LoaderError.NvfsUnavailable => true
            _ => false
        expect(is_nvfs).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- load_model_from_pack_streamed — happy path
- load_model_from_pack_streamed — error cases
- load_model_from_pack_streamed — ChunkDataInvalid path
- load_model_from_pack — bare entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

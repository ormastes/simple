# Manifest Specification

> <details>

<!-- sdn-diagram:id=manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

manifest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Specification

## Scenarios

### TensorPackManifest.empty

#### is_empty on fresh value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TensorPackManifest.empty()
expect(m.is_empty()).to_equal(true)
```

</details>

#### has schema_version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TensorPackManifest.empty()
expect(m.schema_version).to_equal(0)
```

</details>

### parse_manifest — malformed inputs

#### rejects empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("")
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects whitespace-only input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("   ")
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects garbage input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("garbage")
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects input missing schema_version key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("\"model_id\":\"x\"")
expect(r.is_err()).to_equal(true)
```

</details>

#### rejects input missing model_id key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("\"schema_version\":0")
expect(r.is_err()).to_equal(true)
```

</details>

#### empty input returns Malformed not some other error

- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("")
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        match e:
            ManifestError.Malformed => expect(true).to_equal(true)
            _ => expect(false).to_equal(true)
```

</details>

#### garbage input returns Malformed

- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = parse_manifest("garbage")
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        match e:
            ManifestError.Malformed => expect(true).to_equal(true)
            _ => expect(false).to_equal(true)
```

</details>

### parse_manifest — unsupported version

#### returns UnsupportedVersion when schema_version is 1

- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build input without brace interpolation — keys inline
val bad = "\"schema_version\":1,\"model_id\":\"x\""
val r = parse_manifest(bad)
expect(r.is_err()).to_equal(true)
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        match e:
            ManifestError.UnsupportedVersion => expect(true).to_equal(true)
            _ => expect(false).to_equal(true)
```

</details>

#### returns UnsupportedVersion when schema_version is 99

- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = "\"schema_version\":99,\"model_id\":\"m\""
val r = parse_manifest(bad)
match r:
    Ok(_) => expect(false).to_equal(true)
    Err(e) =>
        match e:
            ManifestError.UnsupportedVersion => expect(true).to_equal(true)
            _ => expect(false).to_equal(true)
```

</details>

### parse_manifest — round-trip via serialize_manifest

#### parse_manifest(serialize_manifest(pack)) returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
expect(r.is_ok()).to_equal(true)
```

</details>

#### round-trip preserves model_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.model_id).to_equal(pack.model_id)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### round-trip preserves revision

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.revision).to_equal(pack.revision)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### round-trip preserves preferred_chunk_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.preferred_chunk_bytes).to_equal(pack.preferred_chunk_bytes)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### round-trip reports schema_version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.schema_version).to_equal(0)
    Err(_) => expect(false).to_equal(true)
```

</details>

#### round-trip tensor_count matches pack.tensors.len()

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.tensor_count).to_equal(pack.tensors.len())
    Err(_) => expect(false).to_equal(true)
```

</details>

#### round-trip chunk_count matches pack.chunks.len()

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val serialized = serialize_manifest(pack)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.chunk_count).to_equal(pack.chunks.len())
    Err(_) => expect(false).to_equal(true)
```

</details>

### parse_manifest — escape round-trip

#### round-trip preserves model_id with embedded quote and backslash

- var p = TensorPack empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a pack whose model_id contains a literal " and \
# _esc in serialize + _find_str_after in parse must be symmetric.
var p = TensorPack.empty("/tmp/pack")
p.model_id = "a\"b\\c"
p.revision = "v0"
p.chunks.push(ChunkInfo(
    id: 0,
    relative_path: "data-000.bin",
    byte_len: 4096,
    digest_hex: "0011aabb00000000000000000000000000000000000000000000000000000000"
))
p.tensors.push(TensorInfo(
    name: "w", shape: [2, 2], dtype: Dtype.F32,
    chunk_id: 0, offset_in_chunk: 0, byte_len: 16
))
val serialized = serialize_manifest(p)
val r = parse_manifest(serialized)
match r:
    Ok(m) => expect(m.model_id).to_equal("a\"b\\c")
    Err(_) => expect(false).to_equal(true)
```

</details>

### build_tensor_pack (stub — deferred)

#### returns Err until build is implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TensorPackManifest.empty()
val r = build_tensor_pack("/tmp/pack", m)
expect(r.is_err()).to_equal(true)
```

</details>

### serialize_manifest (A2)

#### produces non-empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = _demo_pack()
val out = serialize_manifest(pack)
expect(out.len()).to_be_greater_than(10)
```

</details>

#### includes the schema_version field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("schema_version")
```

</details>

#### includes the tensor name 'w' and dtype F32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("w")
expect(out).to_contain("F32")
```

</details>

#### includes digest_hex and relative_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = serialize_manifest(_demo_pack())
expect(out).to_contain("0011aabb")
expect(out).to_contain("data-000.bin")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_executor/model_loader/manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TensorPackManifest.empty
- parse_manifest — malformed inputs
- parse_manifest — unsupported version
- parse_manifest — round-trip via serialize_manifest
- parse_manifest — escape round-trip
- build_tensor_pack (stub — deferred)
- serialize_manifest (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

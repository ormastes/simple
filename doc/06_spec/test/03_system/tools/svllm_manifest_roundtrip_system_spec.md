# System Test - svllm Manifest Round-Trip

> End-to-end system test for manifest serialization and parsing round-trip. Tests TensorPack → serialize_manifest → parse_manifest → TensorPackManifest conversion integrity and error handling.

<!-- sdn-diagram:id=svllm_manifest_roundtrip_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svllm_manifest_roundtrip_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svllm_manifest_roundtrip_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svllm_manifest_roundtrip_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# System Test - svllm Manifest Round-Trip

End-to-end system test for manifest serialization and parsing round-trip. Tests TensorPack → serialize_manifest → parse_manifest → TensorPackManifest conversion integrity and error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SVLLM |
| Category | Model Loading |
| Difficulty | 3/5 |
| Status | In Progress (round-trip tests blocked on parse_manifest implementation) |
| Source | `test/03_system/tools/svllm_manifest_roundtrip_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end system test for manifest serialization and parsing round-trip.
Tests TensorPack → serialize_manifest → parse_manifest → TensorPackManifest
conversion integrity and error handling.

Serialization tests (serialize_manifest) pass. Round-trip tests fail until the
parallel agent implements parse_manifest (currently a stub returning Err).

## Coverage

- Basic round-trip: serialize then parse preserves pack metadata
- Chunk and tensor cardinality preservation
- Error cases: empty input, malformed JSON, unsupported schema version
- Manifest field validation

## Scenarios

### svllm Manifest Serialization + Parsing

#### serialize_manifest produces non-empty output

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.len() > 0)
```

</details>

#### serialized manifest contains schema_version

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.contains("schema_version"))
```

</details>

#### serialized manifest contains model_id

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.contains("test_model"))
```

</details>

#### serialized manifest contains tensor names

- verify
- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.contains("weight1"))
verify(serialized.contains("weight2"))
verify(serialized.contains("bias"))
```

</details>

#### serialized manifest contains dtype labels

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.contains("F32"))
verify(serialized.contains("F16"))
```

</details>

#### serialized manifest contains chunk info

- verify
- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
verify(serialized.contains("data-000.bin"))
verify(serialized.contains("data-001.bin"))
```

</details>

### svllm Manifest Round-Trip

#### parse_manifest rejects empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_manifest("")
expect(result.is_err()).to_equal(true)
```

</details>

#### parse_manifest rejects garbage input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_manifest("this is not valid manifest data at all")
expect(result.is_err()).to_equal(true)
```

</details>

#### parse_manifest round-trip succeeds on well-formed manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)
```

</details>

#### parse_manifest round-trip preserves tensor count

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.tensor_count == pack.tensors.len())
```

</details>

#### parse_manifest round-trip preserves chunk count

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.chunk_count == pack.chunks.len())
```

</details>

#### parse_manifest round-trip preserves model_id

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.model_id == pack.model_id)
```

</details>

#### parse_manifest round-trip preserves revision

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.revision == pack.revision)
```

</details>

#### parse_manifest round-trip preserves preferred_chunk_bytes

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.preferred_chunk_bytes == pack.preferred_chunk_bytes)
```

</details>

#### parse_manifest round-trip sets schema_version to 0

- verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pack = demo_pack()
val serialized = serialize_manifest(pack)
val parse_result = parse_manifest(serialized)
expect(parse_result.is_ok()).to_equal(true)

val manifest = parse_result.unwrap()
verify(manifest.schema_version == 0)
```

</details>

### svllm Manifest Error Handling

#### parse_manifest rejects valid header with garbage tail (structural guard)

- Ok
- Err
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Has schema_version and model_id keys but no chunks/tensors/closing brace
val truncated = "{\"schema_version\":0,\"model_id\":\"m\",\"revision\":\"r\",\"preferred_chunk_bytes\":4096 GARBAGE"
val result = parse_manifest(truncated)
match result:
    Ok(_) => verify(false)
    Err(ManifestError.Malformed) => verify(true)
    Err(_) => verify(false)
```

</details>

#### parse_manifest returns Malformed for garbage

- Ok
- Err
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse_manifest("garbage")
match result:
    Ok(_) => verify(false)
    Err(ManifestError.Malformed) => verify(true)
    Err(_) => verify(false)  # Any other error variant is wrong
```

</details>

#### parse_manifest rejects unsupported schema_version

- Ok
- Err
- Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Manifest with schema_version 1 (unsupported)
val bad_version = "{\"schema_version\":1,\"model_id\":\"test\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"chunks\":[],\"tensors\":[]}"
val result = parse_manifest(bad_version)
# Should fail with UnsupportedVersion because schema_version != 0
match result:
    Ok(_) => verify(false)
    Err(ManifestError.UnsupportedVersion) => verify(true)
    Err(_) => verify(false)  # Any other error variant is wrong
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

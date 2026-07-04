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
| 11 | 11 | 0 | 0 |

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

### parse_manifest

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

#### returns Ok on a well-formed canonical v0 manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val r = parse_manifest(sdn)
expect(r.is_ok()).to_equal(true)
```

</details>

#### keeps parsed model metadata and counts

- Ok
   - Expected: m.model_id equals `demo`
   - Expected: m.revision equals `v0`
   - Expected: m.preferred_chunk_bytes equals `2097152`
   - Expected: m.chunk_count equals `0`
   - Expected: m.tensor_count equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val r = parse_manifest(sdn)
match r:
    Ok(m) =>
        expect(m.model_id).to_equal("demo")
        expect(m.revision).to_equal("v0")
        expect(m.preferred_chunk_bytes).to_equal(2097152)
        expect(m.chunk_count).to_equal(0)
        expect(m.tensor_count).to_equal(0)
    Err(_) =>
        fail("canonical manifest should parse")
```

</details>

### build_tensor_pack

#### materialises a pack from a parsed manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val m = parse_manifest(sdn).unwrap()
val r = build_tensor_pack("/tmp/pack", m)
expect(r.is_ok()).to_equal(true)
```

</details>

#### copies parsed manifest fields into the pack

- Ok
   - Expected: pack.pack_root equals `/tmp/pack`
   - Expected: pack.model_id equals `demo`
   - Expected: pack.revision equals `v0`
   - Expected: pack.preferred_chunk_bytes equals `2097152`
   - Expected: pack.chunk_count() equals `0`
   - Expected: pack.tensor_count() equals `0`
- Err
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "{\"schema_version\":0,\"model_id\":\"demo\",\"revision\":\"v0\",\"preferred_chunk_bytes\":2097152,\"digest_algo\":\"sha256\",\"chunks\":[],\"tensors\":[]}"
val m = parse_manifest(sdn).unwrap()
val r = build_tensor_pack("/tmp/pack", m)
match r:
    Ok(pack) =>
        expect(pack.pack_root).to_equal("/tmp/pack")
        expect(pack.model_id).to_equal("demo")
        expect(pack.revision).to_equal("v0")
        expect(pack.preferred_chunk_bytes).to_equal(2097152)
        expect(pack.chunk_count()).to_equal(0)
        expect(pack.tensor_count()).to_equal(0)
    Err(_) =>
        fail("canonical manifest should materialise")
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
- parse_manifest
- build_tensor_pack
- serialize_manifest (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

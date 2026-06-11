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
| 9 | 9 | 0 | 0 |

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

### parse_manifest (A1 stub)

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

#### TODO: returns Ok on a well-formed v0 manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "schema_version: 0\nmodel_id: \"demo\"\nrevision: \"v0\"\npreferred_chunk_bytes: 2097152\nchunks: []\ntensors: []\n"
val r = parse_manifest(sdn)
# Intentionally failing until the parser is implemented.
expect(r.is_ok()).to_equal(true)
```

</details>

### build_tensor_pack (A1 stub)

#### TODO: materialises a pack from a parsed manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = TensorPackManifest.empty()
val r = build_tensor_pack("/tmp/pack", m)
# Intentionally failing until build is implemented.
expect(r.is_ok()).to_equal(true)
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
- parse_manifest (A1 stub)
- build_tensor_pack (A1 stub)
- serialize_manifest (A2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

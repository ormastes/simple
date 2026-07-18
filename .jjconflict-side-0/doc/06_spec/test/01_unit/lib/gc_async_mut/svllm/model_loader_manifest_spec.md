# Model Loader Manifest Specification

> <details>

<!-- sdn-diagram:id=model_loader_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model_loader_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model_loader_manifest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model_loader_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Manifest Specification

## Scenarios

### svLLM tensor-pack manifest loader

#### parses canonical empty v0 manifest text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(manifest_status(empty_manifest())).to_equal("ok")
expect(manifest_model_id(empty_manifest())).to_equal("tiny")
expect(manifest_counts(empty_manifest())).to_equal("0:0")
```

</details>

#### rejects malformed and unsupported manifests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(manifest_status("not a manifest")).to_equal("error")
expect(manifest_status("{\"schema_version\":1,\"model_id\":\"tiny\",\"revision\":\"r1\",\"preferred_chunk_bytes\":4096,\"chunks\":[],\"tensors\":[]}")).to_equal("error")
```

</details>

#### loads an already-read empty manifest without throwing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(load_status("/tmp/pack", empty_manifest())).to_equal("ok")
expect(load_status("", empty_manifest())).to_equal("error")
expect(pack_load_status("/tmp/pack")).to_equal("error")
```

</details>

#### materializes canonical non-empty tensor and chunk metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(manifest_status(one_tensor_manifest())).to_equal("ok")
expect(manifest_counts(one_tensor_manifest())).to_equal("1:1")
expect(pack_summary("/tmp/pack", one_tensor_manifest())).to_equal("tiny:1:1:16")
expect(manifest_status(bad_chunk_manifest())).to_equal("error")
expect(manifest_status(bad_digest_manifest())).to_equal("error")
```

</details>

#### loads manifest.sdn from a pack root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pack_load_status("test/fixtures/svllm/valid_pack")).to_equal("ok")
```

</details>

#### rejects missing chunk files from a pack root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pack_load_detail("test/fixtures/svllm/missing_chunk_pack")).to_equal("chunk_error")
```

</details>

#### rejects mismatched chunk files from a pack root

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pack_load_detail("test/fixtures/svllm/wrong_chunk_pack")).to_equal("chunk_error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_loader_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svLLM tensor-pack manifest loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

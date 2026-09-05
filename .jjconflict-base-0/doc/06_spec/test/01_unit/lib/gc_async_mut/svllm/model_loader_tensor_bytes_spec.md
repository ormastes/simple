# Model Loader Tensor Bytes Specification

> <details>

<!-- sdn-diagram:id=model_loader_tensor_bytes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model_loader_tensor_bytes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model_loader_tensor_bytes_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model_loader_tensor_bytes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Tensor Bytes Specification

## Scenarios

### svLLM tensor byte range loader

#### loads the declared tensor byte range from a validated pack

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "test/fixtures/svllm/valid_pack"
val name = "tok_embeddings.weight"
expect(tensor_byte_status(root, name)).to_equal("ok")
expect(tensor_byte_len(root, name)).to_equal(16)
expect(tensor_byte_at(root, name, 0)).to_equal(48)
expect(tensor_byte_at(root, name, 15)).to_equal(102)
```

</details>

#### loads a declared tensor byte range spanning sequential chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "test/fixtures/svllm/cross_chunk_pack"
val name = "split.weight"
expect(tensor_byte_status(root, name)).to_equal("ok")
expect(tensor_byte_len(root, name)).to_equal(7)
expect(tensor_byte_at(root, name, 0)).to_equal(98)
expect(tensor_byte_at(root, name, 3)).to_equal(10)
expect(tensor_byte_at(root, name, 4)).to_equal(69)
expect(tensor_byte_at(root, name, 6)).to_equal(71)
```

</details>

#### reports missing tensor names explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tensor_byte_status("test/fixtures/svllm/valid_pack", "missing.weight")).to_equal("tensor_not_found")
```

</details>

#### does not read bytes from invalid packs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tensor_byte_status("test/fixtures/svllm/missing_chunk_pack", "tok_embeddings.weight")).to_equal("chunk_error")
expect(tensor_byte_status("test/fixtures/svllm/wrong_chunk_pack", "tok_embeddings.weight")).to_equal("chunk_error")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_loader_tensor_bytes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svLLM tensor byte range loader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

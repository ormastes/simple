# Model Loader Transport Specification

> <details>

<!-- sdn-diagram:id=model_loader_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model_loader_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model_loader_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model_loader_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Model Loader Transport Specification

## Scenarios

### svLLM memory NVFS streaming transport

#### streams a manifest and chunk bytes through the restored loader entry

- chunks push
   - Expected: streamed_status(manifest_one_chunk(), chunks) equals `tiny:1:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(streamed_status(manifest_one_chunk(), chunks)).to_equal("tiny:1:1")
```

</details>

#### streams a pack image through the memory NVFS transport

- paths push
- chunks push
   - Expected: via_status(manifest_one_chunk(), paths, chunks) equals `tiny:1:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var paths: [text] = []
paths.push("data-000.bin")
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(via_status(manifest_one_chunk(), paths, chunks)).to_equal("tiny:1:1")
```

</details>

#### maps missing transport chunks to chunk_error

- paths push
- chunks push
   - Expected: via_status(manifest_one_chunk(), paths, chunks) equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var paths: [text] = []
paths.push("other.bin")
var chunks: [[u8]] = []
chunks.push(bytes4())
expect(via_status(manifest_one_chunk(), paths, chunks)).to_equal("chunk_error")
```

</details>

#### maps short streamed chunk data to chunk_error

- chunks push
   - Expected: streamed_status(manifest_one_chunk(), chunks) equals `chunk_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chunks: [[u8]] = []
chunks.push(bytes2(0x10 as u8, 0x20 as u8))
expect(streamed_status(manifest_one_chunk(), chunks)).to_equal("chunk_error")
```

</details>

#### validates split tensor chunks through the streamed path

- chunks push
- chunks push
   - Expected: streamed_status(manifest_two_chunks(), chunks) equals `tiny:2:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var chunks: [[u8]] = []
chunks.push(bytes2(0x10 as u8, 0x20 as u8))
chunks.push(bytes2(0x30 as u8, 0x40 as u8))
expect(streamed_status(manifest_two_chunks(), chunks)).to_equal("tiny:2:1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/svllm/model_loader_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svLLM memory NVFS streaming transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

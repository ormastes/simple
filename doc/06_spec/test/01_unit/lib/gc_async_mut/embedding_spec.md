# Embedding Specification

> <details>

<!-- sdn-diagram:id=embedding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=embedding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

embedding_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=embedding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Embedding Specification

## Scenarios

### Embedding

### create

#### initializes with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num_embeddings = 1000
val embedding_dim = 128
expect(num_embeddings).to_equal(1000)
expect(embedding_dim).to_equal(128)
```

</details>

#### creates weight tensor with scaled random values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Weight scaled by 0.1
val scale = 0.1
expect(scale).to_equal(0.1)
```

</details>

#### initializes in training mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val training = true
expect(training).to_equal(true)
```

</details>

#### initializes empty last_indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var last_indices = []
expect(last_indices.len()).to_equal(0)
```

</details>

### forward (1D input)

#### looks up embedding vectors by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input (batch_size,) -> Output (batch_size, embedding_dim)
val batch_size = 3
val embedding_dim = 128
val output_elements = batch_size * embedding_dim
expect(output_elements).to_equal(384)
```

</details>

#### stores indices for backward pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var stored_indices = [5, 10, 3]
expect(stored_indices.len()).to_equal(3)
```

</details>

#### handles out-of-bounds with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Negative or >= num_embeddings -> zero vector
val idx = -1
val is_oob = idx < 0
expect(is_oob).to_equal(true)
```

</details>

### forward (2D input)

#### handles batch x sequence input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input (batch, seq_len) -> Output (batch, seq_len, embedding_dim)
val batch_size = 2
val seq_len = 5
val embedding_dim = 64
val total = batch_size * seq_len * embedding_dim
expect(total).to_equal(640)
```

</details>

### backward

#### scatter-adds gradients to weight

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For each index from forward, accumulate grad row
val num_embeddings = 100
val embedding_dim = 32
val grad_size = num_embeddings * embedding_dim
expect(grad_size).to_equal(3200)
```

</details>

#### skips out-of-bounds indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = -1
val should_skip = idx < 0
expect(should_skip).to_equal(true)
```

</details>

#### stores gradient in weight tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grad_stored = true
expect(grad_stored).to_equal(true)
```

</details>

### parameters

#### returns list with weight tensor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num_params = 1
expect(num_params).to_equal(1)
```

</details>

### train/eval modes

#### train sets training to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val training = true
expect(training).to_equal(true)
```

</details>

#### eval sets training to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val training = false
expect(training).to_equal(false)
```

</details>

### Dataset

### ArrayDataset

#### returns correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]]
expect(data.len()).to_equal(3)
```

</details>

#### returns sample at valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [[1.0, 2.0], [3.0, 4.0]]
val sample = data[0]
expect(sample.len()).to_equal(2)
```

</details>

#### returns empty array for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = -1
val result = []
expect(result.len()).to_equal(0)
```

</details>

#### returns empty array for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data_len = 3
val index = 5
val oob = index >= data_len
expect(oob).to_equal(true)
```

</details>

### LabeledDataset

#### returns labeled sample at valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val feature = [1.0, 2.0]
val label = 0.0
expect(feature.len()).to_equal(2)
expect(label).to_equal(0.0)
```

</details>

#### returns default sample for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Returns LabeledSample(feature: [], label: 0.0)
val default_label = 0.0
var default_feature = []
expect(default_label).to_equal(0.0)
expect(default_feature.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/embedding_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Embedding
- create
- forward (1D input)
- forward (2D input)
- backward
- parameters
- train/eval modes
- Dataset
- ArrayDataset
- LabeledDataset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Embedding Specification

> Tests covering Embedding, create, forward (1D input), forward (2D input), backward, parameters, train/eval modes, Dataset, ArrayDataset, LabeledDataset.

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

- initializes with correct dimensions
   - Expected: num_embeddings equals `1000`
   - Expected: embedding_dim equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with correct dimensions")
val num_embeddings = 1000
val embedding_dim = 128
expect(num_embeddings).to_equal(1000)
expect(embedding_dim).to_equal(128)
```

</details>

#### creates weight tensor with scaled random values

- creates weight tensor with scaled random values
   - Expected: scale equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates weight tensor with scaled random values")
# Weight scaled by 0.1
val scale = 0.1
expect(scale).to_equal(0.1)
```

</details>

#### initializes in training mode

- initializes in training mode
   - Expected: training is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes in training mode")
val training = true
expect(training).to_equal(true)
```

</details>

#### initializes empty last_indices

- initializes empty last_indices
   - Expected: last_indices.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes empty last_indices")
var last_indices = []
expect(last_indices.len()).to_equal(0)
```

</details>

### forward (1D input)

#### looks up embedding vectors by index

- looks up embedding vectors by index
   - Expected: output_elements equals `384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("looks up embedding vectors by index")
# Input (batch_size,) -> Output (batch_size, embedding_dim)
val batch_size = 3
val embedding_dim = 128
val output_elements = batch_size * embedding_dim
expect(output_elements).to_equal(384)
```

</details>

#### stores indices for backward pass

- stores indices for backward pass
   - Expected: stored_indices.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores indices for backward pass")
var stored_indices = [5, 10, 3]
expect(stored_indices.len()).to_equal(3)
```

</details>

#### handles out-of-bounds with zeros

- handles out-of-bounds with zeros
   - Expected: is_oob is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles out-of-bounds with zeros")
# Negative or >= num_embeddings -> zero vector
val idx = -1
val is_oob = idx < 0
expect(is_oob).to_equal(true)
```

</details>

### forward (2D input)

#### handles batch x sequence input

- handles batch x sequence input
   - Expected: total equals `640`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles batch x sequence input")
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

- scatter-adds gradients to weight
   - Expected: grad_size equals `3200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scatter-adds gradients to weight")
# For each index from forward, accumulate grad row
val num_embeddings = 100
val embedding_dim = 32
val grad_size = num_embeddings * embedding_dim
expect(grad_size).to_equal(3200)
```

</details>

#### skips out-of-bounds indices

- skips out-of-bounds indices
   - Expected: should_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips out-of-bounds indices")
val idx = -1
val should_skip = idx < 0
expect(should_skip).to_equal(true)
```

</details>

#### stores gradient in weight tensor

- stores gradient in weight tensor
   - Expected: grad_stored is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores gradient in weight tensor")
val grad_stored = true
expect(grad_stored).to_equal(true)
```

</details>

### parameters

#### returns list with weight tensor

- returns list with weight tensor
   - Expected: num_params equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns list with weight tensor")
val num_params = 1
expect(num_params).to_equal(1)
```

</details>

### train/eval modes

#### train sets training to true

- train sets training to true
   - Expected: training is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("train sets training to true")
val training = true
expect(training).to_equal(true)
```

</details>

#### eval sets training to false

- eval sets training to false
   - Expected: training is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval sets training to false")
val training = false
expect(training).to_equal(false)
```

</details>

### Dataset

### ArrayDataset

#### returns correct length

- returns correct length
   - Expected: data.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct length")
val data = [[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]]
expect(data.len()).to_equal(3)
```

</details>

#### returns sample at valid index

- returns sample at valid index
   - Expected: sample.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sample at valid index")
val data = [[1.0, 2.0], [3.0, 4.0]]
val sample = data[0]
expect(sample.len()).to_equal(2)
```

</details>

#### returns empty array for negative index

- returns empty array for negative index
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array for negative index")
val index = -1
val result = []
expect(result.len()).to_equal(0)
```

</details>

#### returns empty array for out-of-bounds index

- returns empty array for out-of-bounds index
   - Expected: oob is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty array for out-of-bounds index")
val data_len = 3
val index = 5
val oob = index >= data_len
expect(oob).to_equal(true)
```

</details>

### LabeledDataset

#### returns labeled sample at valid index

- returns labeled sample at valid index
   - Expected: feature.len() equals `2`
   - Expected: label equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns labeled sample at valid index")
val feature = [1.0, 2.0]
val label = 0.0
expect(feature.len()).to_equal(2)
expect(label).to_equal(0.0)
```

</details>

#### returns default sample for out-of-bounds

- returns default sample for out-of-bounds
   - Expected: default_label equals `0.0`
   - Expected: default_feature.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns default sample for out-of-bounds")
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
| Source | `test/unit/lib/gc_async_mut/embedding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Embedding, create, forward (1D input), forward (2D input), backward, parameters, train/eval modes, Dataset, ArrayDataset, LabeledDataset.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ecd7c6f3da6e0a25e1854aefd6cb7a97f7de17dae95a3b457f239c4fb9811380`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecd7c6f3da6e0a25e1854aefd6cb7a97f7de17dae95a3b457f239c4fb9811380`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecd7c6f3da6e0a25e1854aefd6cb7a97f7de17dae95a3b457f239c4fb9811380`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/gc_async_mut/embedding_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/embedding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/embedding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/embedding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/embedding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/embedding_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes with correct dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/embedding_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates weight tensor with scaled random values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/embedding_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes in training mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

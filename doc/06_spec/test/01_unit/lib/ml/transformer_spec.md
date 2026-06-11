# Transformer Specification

> <details>

<!-- sdn-diagram:id=transformer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transformer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transformer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transformer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transformer Specification

## Scenarios

### Transformer

#### attention

#### creates multi-head attention

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mha = MockMultiheadAttention(embed_dim: 256, num_heads: 8)
expect mha.embed_dim == 256
expect mha.num_heads == 8
```

</details>

#### encoder/decoder

#### creates transformer encoder layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoder = MockTransformerEncoderLayer(d_model: 512, nhead: 8)
expect encoder.d_model == 512
expect encoder.nhead == 8
```

</details>

#### creates transformer decoder layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decoder = MockTransformerDecoderLayer(d_model: 512, nhead: 8)
expect decoder.d_model == 512
expect decoder.nhead == 8
```

</details>

#### sequence modeling

#### processes sequences with positional encoding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pe = MockPositionalEncoding(d_model: 256, max_len: 1024)
expect pe.d_model == 256
expect pe.max_len == 1024
```

</details>

#### advanced

#### handles masking

1. expect mask is valid
2. expect mask apply to attention weights


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mask = MockMask.new([8, 10, 10], mask_type="causal")
expect mask.is_valid()
expect mask.apply_to_attention_weights()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/transformer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Transformer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

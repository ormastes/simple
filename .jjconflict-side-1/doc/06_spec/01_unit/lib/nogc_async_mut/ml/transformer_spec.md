# Transformer Specification

> Tests covering Transformer.

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

- creates multi-head attention


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-head attention")
val mha = MockMultiheadAttention(embed_dim: 256, num_heads: 8)
expect mha.embed_dim == 256
expect mha.num_heads == 8
```

</details>

#### encoder/decoder

#### creates transformer encoder layer

- creates transformer encoder layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates transformer encoder layer")
val encoder = MockTransformerEncoderLayer(d_model: 512, nhead: 8)
expect encoder.d_model == 512
expect encoder.nhead == 8
```

</details>

#### creates transformer decoder layer

- creates transformer decoder layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates transformer decoder layer")
val decoder = MockTransformerDecoderLayer(d_model: 512, nhead: 8)
expect decoder.d_model == 512
expect decoder.nhead == 8
```

</details>

#### sequence modeling

#### processes sequences with positional encoding

- processes sequences with positional encoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes sequences with positional encoding")
val pe = MockPositionalEncoding(d_model: 256, max_len: 1024)
expect pe.d_model == 256
expect pe.max_len == 1024
```

</details>

#### advanced

#### handles masking

- handles masking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles masking")
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
| Source | `test/01_unit/lib/nogc_async_mut/ml/transformer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Transformer.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67cec264971ad9fbe9d5bd0dfe646ffe28a2a6c56170ea85bbe587b122486a8c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67cec264971ad9fbe9d5bd0dfe646ffe28a2a6c56170ea85bbe587b122486a8c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67cec264971ad9fbe9d5bd0dfe646ffe28a2a6c56170ea85bbe587b122486a8c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/ml/transformer_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/ml/transformer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/ml/transformer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/ml/transformer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/ml/transformer_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates multi-head attention' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ml/transformer_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates transformer encoder layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/ml/transformer_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates transformer decoder layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

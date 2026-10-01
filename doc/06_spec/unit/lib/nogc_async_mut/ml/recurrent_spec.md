# Recurrent Specification

> Tests covering RNN Layers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Recurrent Specification

## Scenarios

### RNN Layers

#### RNN

#### creates RNN layer

- creates RNN layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates RNN layer")
val rnn_layer = MockRNN(input_size: 10, hidden_size: 20, num_layers: 1)
expect rnn_layer.input_size == 10
expect rnn_layer.hidden_size == 20
```

</details>

#### LSTM

#### creates LSTM layer

- creates LSTM layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates LSTM layer")
val lstm_layer = MockLSTM(input_size: 10, hidden_size: 20, num_layers: 1)
expect lstm_layer.input_size == 10
expect lstm_layer.hidden_size == 20
```

</details>

#### GRU

#### creates GRU layer

- creates GRU layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates GRU layer")
val gru_layer = MockGRU(input_size: 10, hidden_size: 20, num_layers: 1)
expect gru_layer.input_size == 10
expect gru_layer.hidden_size == 20
```

</details>

#### sequence processing

#### processes sequences with LSTM

- processes sequences with LSTM


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes sequences with LSTM")
val lstm = MockLSTM(input_size: 5, hidden_size: 10, num_layers: 1)
expect lstm.hidden_size == 10
```

</details>

#### advanced

#### handles packed sequences

- handles packed sequences


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles packed sequences")
val packed = MockPackedSequence.new(100, 5)
expect packed.is_packed()
expect packed.num_sequences == 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/ml/recurrent_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RNN Layers.
- RNN Layers

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

- Canonical SPipe generation for source `e086232a0e2cf49437fd5174f469b927ac08adcc6e9790f527b7155782c993fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e086232a0e2cf49437fd5174f469b927ac08adcc6e9790f527b7155782c993fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e086232a0e2cf49437fd5174f469b927ac08adcc6e9790f527b7155782c993fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_async_mut/ml/recurrent_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/ml/recurrent_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/ml/recurrent_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/ml/recurrent_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/ml/recurrent_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates RNN layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/ml/recurrent_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates LSTM layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/ml/recurrent_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates GRU layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

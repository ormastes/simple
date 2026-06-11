# Recurrent Specification

> <details>

<!-- sdn-diagram:id=recurrent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=recurrent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

recurrent_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=recurrent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rnn_layer = MockRNN(input_size: 10, hidden_size: 20, num_layers: 1)
expect rnn_layer.input_size == 10
expect rnn_layer.hidden_size == 20
```

</details>

#### LSTM

#### creates LSTM layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lstm_layer = MockLSTM(input_size: 10, hidden_size: 20, num_layers: 1)
expect lstm_layer.input_size == 10
expect lstm_layer.hidden_size == 20
```

</details>

#### GRU

#### creates GRU layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gru_layer = MockGRU(input_size: 10, hidden_size: 20, num_layers: 1)
expect gru_layer.input_size == 10
expect gru_layer.hidden_size == 20
```

</details>

#### sequence processing

#### processes sequences with LSTM

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lstm = MockLSTM(input_size: 5, hidden_size: 10, num_layers: 1)
expect lstm.hidden_size == 10
```

</details>

#### advanced

#### handles packed sequences

1. expect packed is packed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/nogc_async_mut/ml/recurrent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

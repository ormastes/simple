# Bson Specification

> <details>

<!-- sdn-diagram:id=bson_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bson_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bson_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bson_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bson Specification

## Scenarios

### BSON encoder — reference vectors

#### empty document

#### encodes empty doc correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_empty_doc_ok()).to_equal(true)
```

</details>

#### Int32

#### encodes int32 field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_int32_a1_ok()).to_equal(true)
```

</details>

#### String

#### encodes string field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_str_ab_ok()).to_equal(true)
```

</details>

#### Null

#### encodes null field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_null_a_ok()).to_equal(true)
```

</details>

#### Bool

#### encodes bool true field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_bool_true_ok()).to_equal(true)
```

</details>

#### encodes bool false field correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_bool_false_ok()).to_equal(true)
```

</details>

#### encode error

#### returns NotADocument when top-level value is not Doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_not_doc_err()).to_equal(true)
```

</details>

### BSON decoder — reference vectors

#### empty document

#### decodes empty doc bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_empty_doc()).to_equal(true)
```

</details>

#### Int32

#### decodes int32 field bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_int32_a1()).to_equal(true)
```

</details>

#### String

#### decodes string field bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_str_ab()).to_equal(true)
```

</details>

#### Null

#### decodes null field bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_null_a()).to_equal(true)
```

</details>

#### Bool

#### decodes bool true bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_bool_true()).to_equal(true)
```

</details>

#### decodes bool false bytes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_bool_false()).to_equal(true)
```

</details>

### BSON decoder — error cases

#### too short

#### returns UnexpectedEnd when buffer is under 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_too_short()).to_equal(true)
```

</details>

#### length mismatch

#### returns LengthMismatch when declared length differs from buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_length_mismatch()).to_equal(true)
```

</details>

#### declared length below minimum

#### returns UnexpectedEnd when declared length is under 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_dec_length_too_small()).to_equal(true)
```

</details>

### BSON round-trip

#### empty document round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_empty()).to_equal(true)
```

</details>

#### Int32 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int32()).to_equal(true)
```

</details>

#### Int64 round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_int64()).to_equal(true)
```

</details>

#### String round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_string()).to_equal(true)
```

</details>

#### Null round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_null()).to_equal(true)
```

</details>

#### Bool true round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_bool_true()).to_equal(true)
```

</details>

#### Bool false round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_bool_false()).to_equal(true)
```

</details>

#### nested document round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_nested()).to_equal(true)
```

</details>

#### array round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_array()).to_equal(true)
```

</details>

#### binary round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_binary()).to_equal(true)
```

</details>

#### datetime round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_datetime()).to_equal(true)
```

</details>

#### regex round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_regex()).to_equal(true)
```

</details>

#### multi-field document round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_rt_multi_field()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/bson_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BSON encoder — reference vectors
- BSON decoder — reference vectors
- BSON decoder — error cases
- BSON round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

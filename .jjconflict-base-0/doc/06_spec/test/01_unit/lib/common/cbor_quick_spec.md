# Cbor Quick Specification

> <details>

<!-- sdn-diagram:id=cbor_quick_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cbor_quick_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cbor_quick_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cbor_quick_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Quick Specification

## Scenarios

### quick test

#### text_to_bytes single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_to_bytes("a")
expect(result.len()).to_equal(1)
```

</details>

#### text_to_bytes multi char

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = text_to_bytes("ab")
expect(result.len()).to_equal(2)
```

</details>

#### var name test my_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val my_bytes: [i64] = []
expect(cbor_validate(my_bytes)).to_equal(false)
```

</details>

#### var name test bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = []
expect(cbor_validate(bytes)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_quick_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- quick test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

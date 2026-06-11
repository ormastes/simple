# Test Sha512 Debug Specification

> <details>

<!-- sdn-diagram:id=test_sha512_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_sha512_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_sha512_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_sha512_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Sha512 Debug Specification

## Scenarios

### sha512_256 debug

#### empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sha512_256_bytes([])
expect(result.len()).to_equal(32)
```

</details>

#### small 4-byte input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sha512_256_bytes([1, 2, 3, 4])
expect(result.len()).to_equal(32)
```

</details>

#### 68-byte input

1. data push
   - Expected: result.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [i64] = []
var i = 0
while i < 68:
    data.push(i & 255)
    i = i + 1
val result = sha512_256_bytes(data)
expect(result.len()).to_equal(32)
```

</details>

#### 128-byte input

1. data push
   - Expected: result.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [i64] = []
var i = 0
while i < 128:
    data.push(i & 255)
    i = i + 1
val result = sha512_256_bytes(data)
expect(result.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/test_sha512_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sha512_256 debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

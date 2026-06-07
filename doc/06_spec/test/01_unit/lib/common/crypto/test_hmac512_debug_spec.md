# Test Hmac512 Debug Specification

> 1. key push

<!-- sdn-diagram:id=test_hmac512_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_hmac512_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_hmac512_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_hmac512_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Hmac512 Debug Specification

## Scenarios

### hmac_sha512_256 debug

#### basic call doesn't crash

1. key push
2. data push
   - Expected: result.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var key: [i64] = []
var data: [i64] = []
var i = 0
while i < 7:
    key.push(7)
    i = i + 1
i = 0
while i < 11:
    data.push(11)
    i = i + 1
val result = hmac_sha512_256_bytes(key, data)
expect(result.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/test_hmac512_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hmac_sha512_256 debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

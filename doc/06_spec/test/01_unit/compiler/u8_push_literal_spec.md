# U8 Push Literal Specification

> <details>

<!-- sdn-diagram:id=u8_push_literal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=u8_push_literal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

u8_push_literal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=u8_push_literal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U8 Push Literal Specification

## Scenarios

### u8 push literal

#### direct push matches workaround push byte-for-byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = build_key_direct()
val workaround = build_key_workaround()
expect(direct.len()).to_equal(8)
expect(workaround.len()).to_equal(8)
expect(direct[0]).to_equal(workaround[0])
expect(direct[1]).to_equal(workaround[1])
expect(direct[2]).to_equal(workaround[2])
expect(direct[3]).to_equal(workaround[3])
expect(direct[4]).to_equal(workaround[4])
expect(direct[5]).to_equal(workaround[5])
expect(direct[6]).to_equal(workaround[6])
expect(direct[7]).to_equal(workaround[7])
```

</details>

#### direct push preserves exact values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val direct = build_key_direct()
expect(direct[0]).to_equal(0x01u8)
expect(direct[1]).to_equal(0x23u8)
expect(direct[2]).to_equal(0x45u8)
expect(direct[3]).to_equal(0x67u8)
expect(direct[4]).to_equal(0x89u8)
expect(direct[5]).to_equal(0xABu8)
expect(direct[6]).to_equal(0xCDu8)
expect(direct[7]).to_equal(0xEFu8)
```

</details>

#### in-block direct push preserves value

1. arr push
   - Expected: arr[0] equals `0x42u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [u8] = []
arr.push(0x42u8)
expect(arr[0]).to_equal(0x42u8)
```

</details>

#### push decimal u8 literal

1. arr push
   - Expected: arr[0] equals `65u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [u8] = []
arr.push(65u8)
expect(arr[0]).to_equal(65u8)
```

</details>

#### push zero literal

1. arr push
   - Expected: arr[0] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [u8] = []
arr.push(0u8)
expect(arr[0]).to_equal(0u8)
```

</details>

#### push max u8 literal

1. arr push
   - Expected: arr[0] equals `255u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [u8] = []
arr.push(255u8)
expect(arr[0]).to_equal(255u8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/u8_push_literal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- u8 push literal

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

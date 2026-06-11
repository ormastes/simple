# Lshr2 Debug Specification

> <details>

<!-- sdn-diagram:id=lshr2_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lshr2_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lshr2_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lshr2_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lshr2 Debug Specification

## Scenarios

### lshr64 v2

#### -1 >> 1 = max_i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_lshr64(-1, 1)).to_equal(9223372036854775807)
```

</details>

#### -1 >> 8 = 0x00FFFFFFFFFFFFFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_lshr64(-1, 8)).to_equal(72057594037927935)
```

</details>

#### -1 >> 63 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_lshr64(-1, 63)).to_equal(1)
```

</details>

#### positive unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_lshr64(100, 2)).to_equal(25)
```

</details>

#### 0xcf83 >> 56 = 0xcf

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cf83e135... first byte of sha512('')
# h0 after sha512 compression
val test = -3502672086076662267  # 0xcf83e13... as signed i64
expect(_lshr64(test, 56) & 255).to_equal(0xcf)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/lshr2_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lshr64 v2

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

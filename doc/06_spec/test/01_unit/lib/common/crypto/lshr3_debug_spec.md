# Lshr3 Debug Specification

> <details>

<!-- sdn-diagram:id=lshr3_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lshr3_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lshr3_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lshr3_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lshr3 Debug Specification

## Scenarios

### lshr64 v3 correct value

#### correct test value >> 56 = 0xcf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = -3493701266030217027  # correct h0 for sha512('')
val r = _lshr64(test, 56)
expect(r & 255).to_equal(207)  # 0xcf
```

</details>

#### correct test value >> 48 = 0x83

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test = -3493701266030217027
expect(_lshr64(test, 48) & 255).to_equal(0x83)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/lshr3_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lshr64 v3 correct value

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Lshr64 Debug Specification

> <details>

<!-- sdn-diagram:id=lshr64_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lshr64_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lshr64_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lshr64_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lshr64 Debug Specification

## Scenarios

### lshr64 debug

#### sha512 bytes([0x61]) gets some output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sha512_bytes([0x61])
expect(r.len()).to_equal(64)
```

</details>

#### sha512 empty output length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sha512_bytes([])
expect(r.len()).to_equal(64)
```

</details>

#### empty first byte should be 0xcf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = sha512_bytes([])
expect(r[0]).to_equal(0xcf)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/lshr64_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lshr64 debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

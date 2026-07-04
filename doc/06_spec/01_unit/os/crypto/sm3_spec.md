# Sm3 Specification

> <details>

<!-- sdn-diagram:id=sm3_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sm3_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sm3_spec -> std
sm3_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sm3_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sm3 Specification

## Scenarios

### SM3 hash (GB/T 32905-2012)

#### SM3('abc') matches GM/T 0004-2012 Appendix A.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sm3_hash(_abc_bytes())
val hex = _bytes_to_hex(result)
expect(hex).to_equal("66c7f0f462eeedd9d1f2d46bdc10e4e24167c4875cf2f7a2297da02b8f4ba8e0")
```

</details>

#### SM3('') matches empty-message standard vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sm3_hash(_empty_bytes())
val hex = _bytes_to_hex(result)
expect(hex).to_equal("1ab21d8355cfa17f8e61194831e81a8f22bec8c728fefb747ed035eb5082aa2b")
```

</details>

#### SM3 digest length is 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sm3_hash(_abc_bytes())
expect(result.len()).to_equal(32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/sm3_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SM3 hash (GB/T 32905-2012)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

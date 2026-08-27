# Tiger Kat Specification

> <details>

<!-- sdn-diagram:id=tiger_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tiger_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tiger_kat_spec -> std
tiger_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tiger_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiger Kat Specification

## Scenarios

### Tiger/192 -- Anderson+Biham 1996 known-answer vectors

#### Tiger(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(tiger192(_empty_bytes()))).to_equal(
    "3293ac630c13f0245f92bbb1766e16167a4e58492dde73f3"
)
```

</details>

#### Tiger(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(tiger192(_a_bytes()))).to_equal(
    "77befbef2e7ef8ab2ec8f93bf587a7fc613e247f5f247809"
)
```

</details>

#### Tiger(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(tiger192(_abc_bytes()))).to_equal(
    "2aab1484e8c158f2bfb8c5ff41b57a525129131c957b5f93"
)
```

</details>

#### Tiger(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bytes_hex(tiger192(_tiger_bytes()))).to_equal(
    "dd00230799f5009fec6debc838bb6a27df2b9d6f110c7937"
)
```

</details>

#### Tiger/192 output length is 24 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tiger192(_abc_bytes()).len()).to_equal(24)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/tiger_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tiger/192 -- Anderson+Biham 1996 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Whirlpool Specification

> <details>

<!-- sdn-diagram:id=whirlpool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=whirlpool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

whirlpool_spec -> std
whirlpool_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=whirlpool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Whirlpool Specification

## Scenarios

### Whirlpool ISO/IEC 10118-3 known-answer vectors

#### whirlpool(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_whirlpool_empty_first8()).to_equal("19fa61d75522a466")
```

</details>

#### whirlpool(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_whirlpool_a_first8()).to_equal("8aca2602792aec6f")
```

</details>

#### whirlpool output length is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_whirlpool_empty_len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/whirlpool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Whirlpool ISO/IEC 10118-3 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Symbol Hash Specification

> <details>

<!-- sdn-diagram:id=symbol_hash_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbol_hash_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbol_hash_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbol_hash_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Hash Specification

## Scenarios

### Symbol Hash

#### computes zero collision probability for empty or single symbol sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(collision_probability(0.0, 1024.0)).to_equal(0.0)
expect(collision_probability(1.0, 1024.0)).to_equal(0.0)
```

</details>

#### computes birthday-bound collision probability for multiple symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probability = collision_probability(4.0, 100.0)
expect(probability).to_equal(0.06)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/symbol_hash_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Symbol Hash

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

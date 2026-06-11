# Bdd Text Eq Runtime Specification

> <details>

<!-- sdn-diagram:id=bdd_text_eq_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bdd_text_eq_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bdd_text_eq_runtime_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bdd_text_eq_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Text Eq Runtime Specification

## Scenarios

### rt_bdd_expect_eq_rv uses semantic compare for text

#### equal text operands compare equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "ok" == "ok"
```

</details>

#### equal int operands compare equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 == 1
```

</details>

#### unequal text operands deliberate-fail RED

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "ok" == "ko"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_text_eq_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rt_bdd_expect_eq_rv uses semantic compare for text

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

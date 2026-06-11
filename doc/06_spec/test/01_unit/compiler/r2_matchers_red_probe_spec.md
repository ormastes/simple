# R2 Matchers Red Probe Specification

> <details>

<!-- sdn-diagram:id=r2_matchers_red_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=r2_matchers_red_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

r2_matchers_red_probe_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=r2_matchers_red_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# R2 Matchers Red Probe Specification

## Scenarios

### R2 matcher deliberate-fail probes

#### to_equal must report RED for 1 == 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1).to_equal(2)
```

</details>

#### to_be_nil must report RED for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/r2_matchers_red_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- R2 matcher deliberate-fail probes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

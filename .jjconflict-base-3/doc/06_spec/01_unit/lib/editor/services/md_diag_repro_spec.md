# Md Diag Repro Specification

> <details>

<!-- sdn-diagram:id=md_diag_repro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_diag_repro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_diag_repro_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_diag_repro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Diag Repro Specification

## Scenarios

### md_diagnostics repro

#### unclosed fence produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = md_check_unclosed_code_fences("```python\nno close", "a.md")
expect(diags.len()).to_equal(1)
```

</details>

#### empty heading produces a diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diags = md_check_empty_headings("#\ntext", "a.md")
expect(diags.len() >= 1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_diag_repro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md_diagnostics repro

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

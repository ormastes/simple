# Lint Simple Specification

> <details>

<!-- sdn-diagram:id=lint_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lint_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lint_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lint_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Simple Specification

## Scenarios

### Lint class

#### creates new lint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint = Lint.new("S001", LintLevel.Deny, LintCategory.Safety, "Test message")
expect lint.code == "S001"
expect lint.message == "Test message"
```

</details>

### Linter class

#### creates new linter

1. expect linter lints len
2. expect linter results len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linter = Linter.new()
expect linter.lints.len() > 0
expect linter.results.len() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lint_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lint class
- Linter class

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

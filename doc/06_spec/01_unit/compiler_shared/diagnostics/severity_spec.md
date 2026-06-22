# Severity Specification

> <details>

<!-- sdn-diagram:id=severity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=severity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

severity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=severity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Severity Specification

## Scenarios

### Severity

#### keeps severity variants available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("severity")

expect(source).to_contain("enum Severity")
expect(source).to_contain("Error")
expect(source).to_contain("Warning")
expect(source).to_contain("Note")
expect(source).to_contain("Help")
expect(source).to_contain("Info")
```

</details>

#### keeps severity display and predicate helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = diagnostics_source("severity")

expect(source).to_contain("fn name() -> text")
expect(source).to_contain("fn color() -> text")
expect(source).to_contain("fn priority() -> i32")
expect(source).to_contain("fn is_error() -> bool")
expect(source).to_contain("fn is_warning() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler_shared/diagnostics/severity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Severity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

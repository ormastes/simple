# Query Lint Print To Log Specification

> <details>

<!-- sdn-diagram:id=query_lint_print_to_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_lint_print_to_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_lint_print_to_log_spec -> std
query_lint_print_to_log_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_lint_print_to_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Lint Print To Log Specification

## Scenarios

### print-to-log lint

#### warns for print in production app source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["fn main():", "    print \"debug\"", "    0"]
val count = _check_print_to_log_text(lines, "src/app/demo/main.spl", "json")
expect count == 1
```

</details>

#### allows print in scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["fn main():", "    print \"debug\"", "    0"]
val count = _check_print_to_log_text(lines, "scripts/demo.spl", "json")
expect count == 0
```

</details>

#### allows print in tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["fn main():", "    print \"debug\"", "    0"]
val count = _check_print_to_log_text(lines, "test/demo_spec.spl", "json")
expect count == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_lint_print_to_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- print-to-log lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

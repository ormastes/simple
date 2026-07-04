# Cli Observer Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=cli_observer_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_observer_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_observer_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_observer_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Observer Numeric Guard Specification

## Scenarios

### ui cli observer numeric guard

#### defaults malformed changes counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.cli/__init__.spl") ?? ""

expect(source).to_contain("fn parse_cli_observer_count_or_default(value: text, default_value: i64) -> i64")
expect(source).to_contain("parse_cli_observer_count_or_default(args[1], 10)")
expect(source.contains("args[1].to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/cli_observer_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui cli observer numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

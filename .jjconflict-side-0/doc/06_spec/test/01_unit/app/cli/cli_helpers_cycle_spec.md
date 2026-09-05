# Cli Helpers Cycle Specification

> <details>

<!-- sdn-diagram:id=cli_helpers_cycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_helpers_cycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_helpers_cycle_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_helpers_cycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Helpers Cycle Specification

## Scenarios

### CLI helpers dependency shape

#### stays on leaf imports instead of reaching back through app.cli.main

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/cli/cli_helpers.spl") ?? ""

expect(source).to_contain("use std.db_atomic.{atomic_write, DbConfig}")
expect(source).to_contain("path_basename(current_dir)")
expect(source.contains("use app.cli.main.")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/cli_helpers_cycle_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLI helpers dependency shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

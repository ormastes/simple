# Scv Cli Dispatch Specification

> <details>

<!-- sdn-diagram:id=scv_cli_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_cli_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_cli_dispatch_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_cli_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Cli Dispatch Specification

## Scenarios

### scv CLI dispatch registration

#### registers scv in the table-driven command registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var found = false
var app_path = ""
var env_override = "unset"
for entry in get_command_table():
    if entry.name == "scv":
        found = true
        app_path = entry.app_path
        env_override = entry.env_override
expect(found).to_equal(true)
expect(app_path).to_equal("src/app/scv/main.spl")
expect(env_override).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_cli_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv CLI dispatch registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Traceability Command Specification

> <details>

<!-- sdn-diagram:id=traceability_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traceability_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traceability_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traceability_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traceability Command Specification

## Scenarios

### CLI traceability-check command

#### is registered in the dispatch table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = get_command_table()
var found = false
for entry in table:
    if entry.name == "traceability-check":
        found = true
expect(found).to_equal(true)
```

</details>

#### routes to the traceability app

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_command("traceability-check")
var app_path = ""
if val entry = result:
    app_path = entry.app_path
expect(app_path).to_equal("src/app/traceability/main.spl")
```

</details>

#### has a Simple implementation instead of a placeholder

1. has simple impl = entry has simple impl
   - Expected: has_simple_impl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_command("traceability-check")
var has_simple_impl = false
if val entry = result:
    has_simple_impl = entry.has_simple_impl()
expect(has_simple_impl).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/traceability_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLI traceability-check command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

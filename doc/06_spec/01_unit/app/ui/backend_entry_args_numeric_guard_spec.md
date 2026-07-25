# Backend Entry Args Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=backend_entry_args_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_entry_args_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_entry_args_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_entry_args_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Entry Args Numeric Guard Specification

## Scenarios

### ui backend entry args numeric guard

#### defaults malformed port values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui/backend_entry_args.spl") ?? ""

expect(source).to_contain("pub fn parse_ui_port_or_default(value: text, default: i32) -> i32")
expect(source).to_contain("trimmed.to_int() ?? default")
expect(source.contains("trimmed.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/backend_entry_args_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui backend entry args numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

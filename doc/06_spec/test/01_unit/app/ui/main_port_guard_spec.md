# Main Port Guard Specification

> <details>

<!-- sdn-diagram:id=main_port_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=main_port_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

main_port_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=main_port_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Main Port Guard Specification

## Scenarios

### ui main port guard

#### guards malformed port arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui/main.spl") ?? ""

expect(source).to_contain("return parse_ui_port_or_default(port_args[i + 1], 3000)")
expect(source).to_contain("return parse_ui_port_or_default(port_str, 3000)")
expect(source.contains("return port_args[i + 1].to_int()")).to_equal(false)
expect(source.contains("return port_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/main_port_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ui main port guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

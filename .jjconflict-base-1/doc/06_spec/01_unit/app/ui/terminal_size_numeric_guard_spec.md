# Terminal Size Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=terminal_size_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=terminal_size_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

terminal_size_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=terminal_size_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Terminal Size Numeric Guard Specification

## Scenarios

### terminal size numeric guards

#### guards environment and probe numeric parsing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/ui.tui/screen.spl") ?? ""

expect(source).to_contain("terminal_size_int_or_zero(cols)")
expect(source).to_contain("terminal_size_int_or_zero(rows)")
expect(source).to_contain("terminal_size_int_or_zero(parts[0])")
expect(source).to_contain("terminal_size_int_or_zero(num_str)")
expect(source).to_contain("trimmed.to_int() ?? 0")
expect(source.contains("cols.to_int()")).to_equal(false)
expect(source.contains("rows.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/terminal_size_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- terminal size numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

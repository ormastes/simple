# Lazy Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=lazy_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Numeric Guard Specification

## Scenarios

### nogc_async_mut mcp lazy numeric guards

#### guards debug log query numeric filters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_debug_log_tools.spl") ?? ""

expect(source).to_contain("_debug_log_int_or_zero(since_str)")
expect(source).to_contain("_debug_log_int_or_zero(extract_field(e, \"id\"))")
expect(source.contains("int(since_str)")).to_equal(false)
```

</details>

#### guards terminal numeric params

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_terminal_tools.spl") ?? ""

expect(source).to_contain("val trimmed = s.trim()")
expect(source).to_contain("int(trimmed)")
expect(source.contains("int(s)")).to_equal(false)
```

</details>

#### guards outline line selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/outline_renderer.spl") ?? ""

expect(source).to_contain("outline_line_selector_or_zero(selector)")
expect(source.contains("val target_line = int(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/mcp/lazy_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut mcp lazy numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

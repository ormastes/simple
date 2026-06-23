# Lsp Diagnostics Timeout Specification

> <details>

<!-- sdn-diagram:id=lsp_diagnostics_timeout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_diagnostics_timeout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_diagnostics_timeout_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_diagnostics_timeout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Diagnostics Timeout Specification

## Scenarios

### simple_lsp_mcp diagnostics timeout guard

#### uses a bounded process run for opt-in diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/simple_lsp_mcp/tools.spl") ?? ""

expect(source).to_contain("process_run_timeout")
expect(source).to_contain("find_simple_binary()")
expect(source).to_contain("10000")
expect(source).to_contain("diagnostics unavailable in source mode")
```

</details>

#### keeps client position parsing on the safe digit parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val main_source = rt_file_read_text("src/app/simple_lsp_mcp/main.spl") ?? ""
val tools_source = rt_file_read_text("src/app/simple_lsp_mcp/tools.spl") ?? ""

expect(main_source).to_contain("arg_int_field(a, \"line\")")
expect(main_source).to_contain("arg_int_field(a, \"character\")")
expect(main_source.contains("line_raw.to_int()")).to_equal(false)
expect(main_source.contains("char_raw.to_int()")).to_equal(false)
expect(tools_source).to_contain("parse_nonnegative_int_or_minus_one(line_str)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple_lsp_mcp diagnostics timeout guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

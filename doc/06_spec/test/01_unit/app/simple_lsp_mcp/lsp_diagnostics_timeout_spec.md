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
| 1 | 1 | 0 | 0 |

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
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

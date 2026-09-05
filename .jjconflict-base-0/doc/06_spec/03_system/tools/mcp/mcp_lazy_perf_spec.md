# MCP Lazy Loading Performance Specification

> Performance verification for MCP server startup with lazy imports. The MCP full server uses `use lazy` for 5 heavy tool modules (34 tools), deferring their loading until first tool invocation.

<!-- sdn-diagram:id=mcp_lazy_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_lazy_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_lazy_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_lazy_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Lazy Loading Performance Specification

Performance verification for MCP server startup with lazy imports. The MCP full server uses `use lazy` for 5 heavy tool modules (34 tools), deferring their loading until first tool invocation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LAZY-002 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/03_system/tools/mcp/mcp_lazy_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Performance verification for MCP server startup with lazy imports.
The MCP full server uses `use lazy` for 5 heavy tool modules (34 tools),
deferring their loading until first tool invocation.

## Expected Behavior

- MCP server starts without loading debug/diagnostic tool modules
- Tool schema functions are loaded on first tools/list request
- Handler functions are loaded on first tool invocation
- All 34 tools remain functional after lazy loading

## Scenarios

### MCP lazy loading structure

#### MCP main.spl exists and uses lazy imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = rt_file_exists("src/app/mcp/main.spl")
expect(exists).to_equal(true)
```

</details>

#### MCP helper modules are kept eager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Helpers and protocol are needed at startup
val exists = mcp_module_exists("helpers")
expect(exists).to_equal(true)
```

</details>

#### debug tools module exists for lazy loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = mcp_module_exists("main_lazy_debug_tools") or mcp_module_exists("debug_tools")
expect(exists).to_equal(true)
```

</details>

#### debug log tools module exists for lazy loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = mcp_module_exists("main_lazy_debug_log_tools") or mcp_module_exists("debug_log_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic read tools module exists for lazy loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = mcp_module_exists("main_lazy_diag_tools") or mcp_module_exists("diag_read_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic edit tools module exists for lazy loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = mcp_module_exists("main_lazy_diag_tools") or mcp_module_exists("diag_edit_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic vcs tools module exists for lazy loading

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = mcp_module_exists("main_lazy_vcs_tools") or mcp_module_exists("diag_vcs_tools")
expect(exists).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

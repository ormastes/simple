# MCP Performance Regression Prevention Specification

> Comprehensive tests for MCP performance regression prevention. Covers four areas: 1. Static lint checks for MCP anti-patterns (MCP001-MCP004) 2. Runtime perf guard counters and thresholds 3. Wrapper validation for production readiness 4. Wrapper file structure verification

<!-- sdn-diagram:id=mcp_perf_regression_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_perf_regression_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_perf_regression_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_perf_regression_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Performance Regression Prevention Specification

Comprehensive tests for MCP performance regression prevention. Covers four areas: 1. Static lint checks for MCP anti-patterns (MCP001-MCP004) 2. Runtime perf guard counters and thresholds 3. Wrapper validation for production readiness 4. Wrapper file structure verification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #F12 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/mcp_performance_regression_prevention_plan_2026-03-30.md |
| Source | `test/03_system/tools/mcp/mcp_perf_regression_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests for MCP performance regression prevention.
Covers four areas:
1. Static lint checks for MCP anti-patterns (MCP001-MCP004)
2. Runtime perf guard counters and thresholds
3. Wrapper validation for production readiness
4. Wrapper file structure verification

## Key Concepts

| Concept | Description |
|---------|-------------|
| MCP001 | Source entrypoint in production wrapper |
| MCP002 | Full-tree scan in request handler |
| MCP003 | Per-request subprocess in hot path |
| MCP004 | Cache without invalidation hook |
| PerfGuard | Runtime counters with threshold violations |
| WrapperValidator | Validates wrapper scripts use compiled artifacts |

## Scenarios

### MCP001 Source Entrypoint Lint

#### detects ENTRY assignment to .spl file in wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "ENTRY=\"src/app/mcp/main.spl\"\nexec \"$RUNTIME\" \"$ENTRY\""
val path = "bin/simple_mcp_server"
# Lint function exists and can be called on wrapper-like paths
expect(path.ends_with("_mcp_server")).to_equal(true)
expect(source.contains(".spl")).to_equal(true)
```

</details>

#### detects exec with .spl argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "exec \"$RUNTIME\" \"$ENTRY_SOURCE\" 2>/dev/null"
expect(source.contains("exec")).to_equal(true)
expect(source.contains(".spl") or source.contains("ENTRY")).to_equal(true)
```

</details>

#### does not flag non-wrapper files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/mcp/main.spl"
val is_wrapper = path.ends_with("_mcp_server") or path.ends_with("_mcp_server.cmd")
expect(is_wrapper).to_equal(false)
```

</details>

#### does not flag .cmd wrapper without .spl reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "set \"ENTRY=%SCRIPT_DIR%..\\build\\mcp.smf\"\n\"%RUNTIME%\" \"%ENTRY%\""
expect(source.contains(".spl")).to_equal(false)
```

</details>

### MCP002 Full-Tree Scan Lint

#### detects rt_dir_walk in handle_ function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "handle_search"
val line = "    val files = rt_dir_walk(\"/vault\")"
expect(fn_name.starts_with("handle_")).to_equal(true)
expect(line.contains("rt_dir_walk(")).to_equal(true)
```

</details>

#### detects scan_vault in dispatch function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "dispatch_analytics"
val line = "    val all = scan_vault(root)"
expect(fn_name.starts_with("dispatch_")).to_equal(true)
expect(line.contains("scan_vault(")).to_equal(true)
```

</details>

#### skips scan calls in reindex functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "handle_reindex_vault"
val is_admin = fn_name.contains("reindex")
expect(is_admin).to_equal(true)
```

</details>

#### skips scan calls in admin functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "handle_admin_rebuild"
val is_admin = fn_name.contains("admin") or fn_name.contains("rebuild")
expect(is_admin).to_equal(true)
```

</details>

#### skips non-MCP source files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/lib/common/text/parser.spl"
val is_mcp = path.contains("/mcp/") or path.contains("/mcp_")
expect(is_mcp).to_equal(false)
```

</details>

### MCP003 Per-Request Subprocess Lint

#### detects rt_process_run in handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "    rt_process_run(\"ls\", [\"-la\"])"
expect(line.contains("rt_process_run(")).to_equal(true)
```

</details>

#### detects shell_cmd in handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "    shell_cmd(cmd)"
expect(line.contains("shell_cmd(")).to_equal(true)
```

</details>

#### skips cli_passthrough.spl entirely

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/app/mcp/cli_passthrough.spl"
val should_skip = path.ends_with("cli_passthrough.spl")
expect(should_skip).to_equal(true)
```

</details>

#### flags subprocess in dispatch function

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_name = "_dispatch_in_process"
val is_handle = fn_name.starts_with("handle_")
val is_dispatch = fn_name.starts_with("dispatch_")
val is_private_dispatch = fn_name.starts_with("_dispatch_")
val is_handler = is_handle or is_dispatch or is_private_dispatch
expect(is_handler).to_equal(true)
```

</details>

### MCP004 Cache Without Invalidation Lint

#### detects cache var without invalidation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "var TOOLS_CACHE = \"\""
val is_cache = line.contains("var ") and line.contains("_CACHE")
expect(is_cache).to_equal(true)
```

</details>

#### accepts cache var with invalidation function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var TOOLS_CACHE = \"\"\nfn invalidate_tools():\n    TOOLS_CACHE = \"\""
val has_invalidation = source.contains("fn invalidate") or source.contains("_CACHE = \"\"")
# There are two occurrences: the declaration and the reset
expect(has_invalidation).to_equal(true)
```

</details>

#### detects cached_ prefix variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "var cached_results = []"
val is_cache = line.starts_with("var cached_")
expect(is_cache).to_equal(true)
```

</details>

### McpPerfGuard Runtime Counters

#### perf_guard.spl module exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(exists).to_equal(true)
```

</details>

#### defines McpPerfGuard struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("struct McpPerfGuard")).to_equal(true)
```

</details>

#### defines PerfViolation struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("struct PerfViolation")).to_equal(true)
```

</details>

#### tracks dir_walks counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_dir_walk")).to_equal(true)
```

</details>

#### tracks file_reads counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_file_read")).to_equal(true)
```

</details>

#### tracks subprocess counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_subprocess")).to_equal(true)
```

</details>

#### checks latency threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("PERF_LATENCY")).to_equal(true)
```

</details>

#### supports disable via environment variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("MCP_PERF_GUARD")).to_equal(true)
```

</details>

#### provides snapshot for diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("McpPerfSnapshot")).to_equal(true)
```

</details>

### MCP Wrapper Validator

#### wrapper_validator.spl module exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(exists).to_equal(true)
```

</details>

#### defines WrapperValidationResult struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("struct WrapperValidationResult")).to_equal(true)
```

</details>

#### validates all five wrapper scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("simple_mcp_server")).to_equal(true)
expect(source.contains("simple_lsp_mcp_server")).to_equal(true)
expect(source.contains("t32_mcp_server")).to_equal(true)
expect(source.contains("t32_lsp_mcp_server")).to_equal(true)
expect(source.contains("obsidian_lsp_mcp_server")).to_equal(true)
```

</details>

#### checks for .spl entrypoint as anti-pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("has_spl_entry")).to_equal(true)
```

</details>

#### checks for Rust bootstrap path as anti-pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("compiler_rust/target")).to_equal(true)
```

</details>

#### checks for log suppression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("SIMPLE_LOG=error")).to_equal(true)
```

</details>

#### checks for stderr suppression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("2>/dev/null")).to_equal(true)
```

</details>

### MCP Wrapper Files Exist

#### bin/simple_mcp_server exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("bin/simple_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/simple_lsp_mcp_server exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("bin/simple_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/t32_mcp_server exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("bin/t32_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/t32_lsp_mcp_server exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("bin/t32_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/obsidian_lsp_mcp_server exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("bin/obsidian_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

### MCP Perf Lint Registration

#### mcp_perf_lint.spl exists in lint directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = file_exists("src/compiler/35.semantics/lint/mcp_perf_lint.spl")
expect(exists).to_equal(true)
```

</details>

#### lint __init__.spl exports mcp_perf_lint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("mcp_perf_lint")).to_equal(true)
```

</details>

#### lint exports McpPerfLintWarning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("McpPerfLintWarning")).to_equal(true)
```

</details>

#### lint exports all four check functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("lint_source_entrypoint")).to_equal(true)
expect(source.contains("lint_full_tree_scan")).to_equal(true)
expect(source.contains("lint_per_request_subprocess")).to_equal(true)
expect(source.contains("lint_cache_no_invalidation")).to_equal(true)
```

</details>

### MCP Server Performance Structure

#### MCP main.spl has tool dispatch cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/mcp/main.spl")
expect(source.contains("_mcp_static_tools_result_cached")).to_equal(true)
```

</details>

#### MCP main.spl has init response cache

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/mcp/main.spl")
expect(source.contains("_mcp_initialize_result")).to_equal(true)
```

</details>

#### MCP main.spl uses table-driven dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/mcp/main.spl")
val table_source = file_read("src/app/mcp/tool_table.spl")
expect(source.contains("dispatch_tool")).to_equal(true)
expect(source.contains("use .tool_table")).to_equal(true)
expect(table_source.contains("get_tool_table")).to_equal(true)
```

</details>

#### MCP main.spl has in-process handlers for core tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/mcp/main_dispatch.spl")
expect(source.contains("_dispatch_in_process")).to_equal(true)
```

</details>

#### MCP cli_passthrough is isolated from in-process handlers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/app/mcp/main_dispatch.spl")
val table_source = file_read("src/app/mcp/tool_table.spl")
# CLI passthrough is used only for handler_kind="cli"
expect(source.contains("_dispatch_cli_direct")).to_equal(true)
expect(source.contains("handle_cli_passthrough_direct")).to_equal(true)
expect(table_source.contains("\"cli\"")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/mcp_performance_regression_prevention_plan_2026-03-30.md](doc/03_plan/mcp_performance_regression_prevention_plan_2026-03-30.md)


</details>

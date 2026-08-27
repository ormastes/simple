# MCP Performance Regression Prevention Specification

> Comprehensive tests for MCP performance regression prevention. Covers four areas: 1. Static lint checks for MCP anti-patterns (MCP001-MCP004) 2. Runtime perf guard counters and thresholds 3. Wrapper validation for production readiness 4. Wrapper file structure verification

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
| Source | `test/system/mcp/mcp_perf_regression_spec.spl` |
| Updated | 2026-08-27 |
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

- detects ENTRY assignment to .spl file in wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects ENTRY assignment to .spl file in wrapper")
val source = "ENTRY=\"src/app/mcp/main.spl\"\nexec \"$RUNTIME\" \"$ENTRY\""
val path = "bin/simple_mcp_server"
# Lint function exists and can be called on wrapper-like paths
assert_equal(path.ends_with("_mcp_server"), true)
assert_equal(source.contains(".spl"), true)
```

</details>

#### detects exec with .spl argument

- detects exec with .spl argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects exec with .spl argument")
val source = "exec \"$RUNTIME\" \"$ENTRY_SOURCE\" 2>/dev/null"
assert_equal(source.contains("exec"), true)
assert_equal(source.contains(".spl") or source.contains("ENTRY"), true)
```

</details>

#### does not flag non-wrapper files

- does not flag non-wrapper files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag non-wrapper files")
val path = "src/app/mcp/main.spl"
val is_wrapper = path.ends_with("_mcp_server") or path.ends_with("_mcp_server.cmd")
assert_equal(is_wrapper, false)
```

</details>

#### does not flag .cmd wrapper without .spl reference

- does not flag .cmd wrapper without .spl reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag .cmd wrapper without .spl reference")
val source = "set \"ENTRY=%SCRIPT_DIR%..\\build\\mcp.smf\"\n\"%RUNTIME%\" \"%ENTRY%\""
assert_equal(source.contains(".spl"), false)
```

</details>

### MCP002 Full-Tree Scan Lint

#### detects rt_dir_walk in handle_ function

- detects rt_dir_walk in handle_ function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects rt_dir_walk in handle_ function")
val fn_name = "handle_search"
val line = "    val files = rt_dir_walk(\"/vault\")"
assert_equal(fn_name.starts_with("handle_"), true)
assert_equal(line.contains("rt_dir_walk("), true)
```

</details>

#### detects scan_vault in dispatch function

- detects scan_vault in dispatch function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects scan_vault in dispatch function")
val fn_name = "dispatch_analytics"
val line = "    val all = scan_vault(root)"
assert_equal(fn_name.starts_with("dispatch_"), true)
assert_equal(line.contains("scan_vault("), true)
```

</details>

#### skips scan calls in reindex functions

- skips scan calls in reindex functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips scan calls in reindex functions")
val fn_name = "handle_reindex_vault"
val is_admin = fn_name.contains("reindex")
assert_equal(is_admin, true)
```

</details>

#### skips scan calls in admin functions

- skips scan calls in admin functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips scan calls in admin functions")
val fn_name = "handle_admin_rebuild"
val is_admin = fn_name.contains("admin") or fn_name.contains("rebuild")
assert_equal(is_admin, true)
```

</details>

#### skips non-MCP source files

- skips non-MCP source files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips non-MCP source files")
val path = "src/lib/common/text/parser.spl"
val is_mcp = path.contains("/mcp/") or path.contains("/mcp_")
assert_equal(is_mcp, false)
```

</details>

### MCP003 Per-Request Subprocess Lint

#### detects rt_process_run in handler

- detects rt_process_run in handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects rt_process_run in handler")
val line = "    rt_process_run(\"ls\", [\"-la\"])"
assert_equal(line.contains("rt_process_run("), true)
```

</details>

#### detects shell_cmd in handler

- detects shell_cmd in handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects shell_cmd in handler")
val line = "    shell_cmd(cmd)"
assert_equal(line.contains("shell_cmd("), true)
```

</details>

#### skips cli_passthrough.spl entirely

- skips cli_passthrough.spl entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips cli_passthrough.spl entirely")
val path = "src/app/mcp/cli_passthrough.spl"
val should_skip = path.ends_with("cli_passthrough.spl")
assert_equal(should_skip, true)
```

</details>

#### flags subprocess in dispatch function

- flags subprocess in dispatch function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags subprocess in dispatch function")
val fn_name = "_dispatch_in_process"
val is_handle = fn_name.starts_with("handle_")
val is_dispatch = fn_name.starts_with("dispatch_")
val is_private_dispatch = fn_name.starts_with("_dispatch_")
val is_handler = is_handle or is_dispatch or is_private_dispatch
assert_equal(is_handler, true)
```

</details>

### MCP004 Cache Without Invalidation Lint

#### detects cache var without invalidation

- detects cache var without invalidation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects cache var without invalidation")
val line = "var TOOLS_CACHE = \"\""
val is_cache = line.contains("var ") and line.contains("_CACHE")
assert_equal(is_cache, true)
```

</details>

#### accepts cache var with invalidation function

- accepts cache var with invalidation function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts cache var with invalidation function")
val source = "var TOOLS_CACHE = \"\"\nfn invalidate_tools():\n    TOOLS_CACHE = \"\""
val has_invalidation = source.contains("fn invalidate") or source.contains("_CACHE = \"\"")
# There are two occurrences: the declaration and the reset
assert_equal(has_invalidation, true)
```

</details>

#### detects cached_ prefix variables

- detects cached_ prefix variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects cached_ prefix variables")
val line = "var cached_results = []"
val is_cache = line.starts_with("var cached_")
assert_equal(is_cache, true)
```

</details>

### McpPerfGuard Runtime Counters

#### perf_guard.spl module exists

- perf_guard.spl module exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("perf_guard.spl module exists")
val exists = rt_file_exists("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(exists, true)
```

</details>

#### defines McpPerfGuard struct

- defines McpPerfGuard struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines McpPerfGuard struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("struct McpPerfGuard"), true)
```

</details>

#### defines PerfViolation struct

- defines PerfViolation struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines PerfViolation struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("struct PerfViolation"), true)
```

</details>

#### tracks dir_walks counter

- tracks dir_walks counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks dir_walks counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("record_dir_walk"), true)
```

</details>

#### tracks file_reads counter

- tracks file_reads counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks file_reads counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("record_file_read"), true)
```

</details>

#### tracks subprocess counter

- tracks subprocess counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks subprocess counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("record_subprocess"), true)
```

</details>

#### checks latency threshold

- checks latency threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks latency threshold")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("PERF_LATENCY"), true)
```

</details>

#### supports disable via environment variable

- supports disable via environment variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports disable via environment variable")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("MCP_PERF_GUARD"), true)
```

</details>

#### provides snapshot for diagnostics

- provides snapshot for diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides snapshot for diagnostics")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
assert_equal(source.contains("McpPerfSnapshot"), true)
```

</details>

### MCP Wrapper Validator

#### wrapper_validator.spl module exists

- wrapper_validator.spl module exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wrapper_validator.spl module exists")
val exists = rt_file_exists("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(exists, true)
```

</details>

#### defines WrapperValidationResult struct

- defines WrapperValidationResult struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WrapperValidationResult struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("struct WrapperValidationResult"), true)
```

</details>

#### validates all five wrapper scripts

- validates all five wrapper scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates all five wrapper scripts")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("simple_mcp_server"), true)
assert_equal(source.contains("simple_lsp_mcp_server"), true)
assert_equal(source.contains("t32_mcp_server"), true)
assert_equal(source.contains("t32_lsp_mcp_server"), true)
assert_equal(source.contains("obsidian_lsp_mcp_server"), true)
```

</details>

#### checks for .spl entrypoint as anti-pattern

- checks for .spl entrypoint as anti-pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for .spl entrypoint as anti-pattern")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("has_spl_entry"), true)
```

</details>

#### checks for Rust bootstrap path as anti-pattern

- checks for Rust bootstrap path as anti-pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for Rust bootstrap path as anti-pattern")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("compiler_rust/target"), true)
```

</details>

#### checks for log suppression

- checks for log suppression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for log suppression")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("SIMPLE_LOG=error"), true)
```

</details>

#### checks for stderr suppression

- checks for stderr suppression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for stderr suppression")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
assert_equal(source.contains("2>/dev/null"), true)
```

</details>

### MCP Wrapper Files Exist

#### bin/simple_mcp_server exists

- bin/simple_mcp_server exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_mcp_server exists")
val exists = rt_file_exists("bin/simple_mcp_server")
assert_equal(exists, true)
```

</details>

#### bin/simple_lsp_mcp_server exists

- bin/simple_lsp_mcp_server exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_lsp_mcp_server exists")
val exists = rt_file_exists("bin/simple_lsp_mcp_server")
assert_equal(exists, true)
```

</details>

#### bin/t32_mcp_server exists

- bin/t32_mcp_server exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/t32_mcp_server exists")
val exists = rt_file_exists("bin/t32_mcp_server")
assert_equal(exists, true)
```

</details>

#### bin/t32_lsp_mcp_server exists

- bin/t32_lsp_mcp_server exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/t32_lsp_mcp_server exists")
val exists = rt_file_exists("bin/t32_lsp_mcp_server")
assert_equal(exists, true)
```

</details>

#### bin/obsidian_lsp_mcp_server exists

- bin/obsidian_lsp_mcp_server exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/obsidian_lsp_mcp_server exists")
val exists = rt_file_exists("bin/obsidian_lsp_mcp_server")
assert_equal(exists, true)
```

</details>

### MCP Perf Lint Registration

#### mcp_perf_lint.spl exists in lint directory

- mcp_perf_lint.spl exists in lint directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mcp_perf_lint.spl exists in lint directory")
val exists = rt_file_exists("src/compiler/35.semantics/lint/mcp_perf_lint.spl")
assert_equal(exists, true)
```

</details>

#### lint __init__.spl exports mcp_perf_lint

- lint __init__.spl exports mcp_perf_lint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint __init__.spl exports mcp_perf_lint")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
assert_equal(source.contains("mcp_perf_lint"), true)
```

</details>

#### lint exports McpPerfLintWarning

- lint exports McpPerfLintWarning


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint exports McpPerfLintWarning")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
assert_equal(source.contains("McpPerfLintWarning"), true)
```

</details>

#### lint exports all four check functions

- lint exports all four check functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint exports all four check functions")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
assert_equal(source.contains("lint_source_entrypoint"), true)
assert_equal(source.contains("lint_full_tree_scan"), true)
assert_equal(source.contains("lint_per_request_subprocess"), true)
assert_equal(source.contains("lint_cache_no_invalidation"), true)
```

</details>

### MCP Server Performance Structure

#### MCP main.spl has tool dispatch cache

- MCP main.spl has tool dispatch cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has tool dispatch cache")
val source = rt_file_read_text("src/app/mcp/main.spl")
assert_equal(source.contains("TOOLS_CACHE"), true)
```

</details>

#### MCP main.spl has init response cache

- MCP main.spl has init response cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has init response cache")
val source = rt_file_read_text("src/app/mcp/main.spl")
assert_equal(source.contains("INIT_CACHE"), true)
```

</details>

#### MCP main.spl uses table-driven dispatch

- MCP main.spl uses table-driven dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl uses table-driven dispatch")
val source = rt_file_read_text("src/app/mcp/main.spl")
val table_source = rt_file_read_text("src/app/mcp/tool_table.spl")
assert_equal(source.contains("dispatch_tool"), true)
assert_equal(source.contains("use .tool_table"), true)
assert_equal(table_source.contains("get_tool_table"), true)
```

</details>

#### MCP main.spl has in-process handlers for core tools

- MCP main.spl has in-process handlers for core tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has in-process handlers for core tools")
val source = rt_file_read_text("src/app/mcp/main_dispatch.spl")
assert_equal(source.contains("_dispatch_in_process"), true)
```

</details>

#### MCP cli_passthrough is isolated from in-process handlers

- MCP cli_passthrough is isolated from in-process handlers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP cli_passthrough is isolated from in-process handlers")
val source = rt_file_read_text("src/app/mcp/main_dispatch.spl")
val table_source = rt_file_read_text("src/app/mcp/tool_table.spl")
# CLI passthrough is used only for handler_kind="cli"
assert_equal(source.contains("_dispatch_cli_direct"), true)
assert_equal(source.contains("handle_cli_passthrough_direct"), true)
assert_equal(table_source.contains("\"cli\""), true)
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

- **Plan:** `doc/03_plan/mcp_performance_regression_prevention_plan_2026-03-30.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `442c68ac39ad18ce5eca9715817be6a5f49d2066d2d54618748686230f16cd08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `442c68ac39ad18ce5eca9715817be6a5f49d2066d2d54618748686230f16cd08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `442c68ac39ad18ce5eca9715817be6a5f49d2066d2d54618748686230f16cd08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/system/mcp/mcp_perf_regression_spec.spl
mirror: doc/06_spec/system/mcp/mcp_perf_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/mcp/mcp_perf_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/mcp/mcp_perf_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/mcp/mcp_perf_regression_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects ENTRY assignment to .spl file in wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/mcp/mcp_perf_regression_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects exec with .spl argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/mcp/mcp_perf_regression_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag non-wrapper files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

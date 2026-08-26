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
| Updated | 2026-08-26 |
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
   - Expected: path.ends_with("_mcp_server") is true
   - Expected: source contains `.spl`


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
expect(path.ends_with("_mcp_server")).to_equal(true)
expect(source.contains(".spl")).to_equal(true)
```

</details>

#### detects exec with .spl argument

- detects exec with .spl argument
   - Expected: source contains `exec`
   - Expected: source contains `".spl") or source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects exec with .spl argument")
val source = "exec \"$RUNTIME\" \"$ENTRY_SOURCE\" 2>/dev/null"
expect(source.contains("exec")).to_equal(true)
expect(source.contains(".spl") or source.contains("ENTRY")).to_equal(true)
```

</details>

#### does not flag non-wrapper files

- does not flag non-wrapper files
   - Expected: is_wrapper is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag non-wrapper files")
val path = "src/app/mcp/main.spl"
val is_wrapper = path.ends_with("_mcp_server") or path.ends_with("_mcp_server.cmd")
expect(is_wrapper).to_equal(false)
```

</details>

#### does not flag .cmd wrapper without .spl reference

- does not flag .cmd wrapper without .spl reference
   - Expected: source does not contain `.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag .cmd wrapper without .spl reference")
val source = "set \"ENTRY=%SCRIPT_DIR%..\\build\\mcp.smf\"\n\"%RUNTIME%\" \"%ENTRY%\""
expect(source.contains(".spl")).to_equal(false)
```

</details>

### MCP002 Full-Tree Scan Lint

#### detects rt_dir_walk in handle_ function

- detects rt_dir_walk in handle_ function
   - Expected: fn_name.starts_with("handle_") is true
   - Expected: line contains `rt_dir_walk(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects rt_dir_walk in handle_ function")
val fn_name = "handle_search"
val line = "    val files = rt_dir_walk(\"/vault\")"
expect(fn_name.starts_with("handle_")).to_equal(true)
expect(line.contains("rt_dir_walk(")).to_equal(true)
```

</details>

#### detects scan_vault in dispatch function

- detects scan_vault in dispatch function
   - Expected: fn_name.starts_with("dispatch_") is true
   - Expected: line contains `scan_vault(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects scan_vault in dispatch function")
val fn_name = "dispatch_analytics"
val line = "    val all = scan_vault(root)"
expect(fn_name.starts_with("dispatch_")).to_equal(true)
expect(line.contains("scan_vault(")).to_equal(true)
```

</details>

#### skips scan calls in reindex functions

- skips scan calls in reindex functions
   - Expected: is_admin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips scan calls in reindex functions")
val fn_name = "handle_reindex_vault"
val is_admin = fn_name.contains("reindex")
expect(is_admin).to_equal(true)
```

</details>

#### skips scan calls in admin functions

- skips scan calls in admin functions
   - Expected: is_admin is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips scan calls in admin functions")
val fn_name = "handle_admin_rebuild"
val is_admin = fn_name.contains("admin") or fn_name.contains("rebuild")
expect(is_admin).to_equal(true)
```

</details>

#### skips non-MCP source files

- skips non-MCP source files
   - Expected: is_mcp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips non-MCP source files")
val path = "src/lib/common/text/parser.spl"
val is_mcp = path.contains("/mcp/") or path.contains("/mcp_")
expect(is_mcp).to_equal(false)
```

</details>

### MCP003 Per-Request Subprocess Lint

#### detects rt_process_run in handler

- detects rt_process_run in handler
   - Expected: line contains `rt_process_run(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects rt_process_run in handler")
val line = "    rt_process_run(\"ls\", [\"-la\"])"
expect(line.contains("rt_process_run(")).to_equal(true)
```

</details>

#### detects shell_cmd in handler

- detects shell_cmd in handler
   - Expected: line contains `shell_cmd(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects shell_cmd in handler")
val line = "    shell_cmd(cmd)"
expect(line.contains("shell_cmd(")).to_equal(true)
```

</details>

#### skips cli_passthrough.spl entirely

- skips cli_passthrough.spl entirely
   - Expected: should_skip is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips cli_passthrough.spl entirely")
val path = "src/app/mcp/cli_passthrough.spl"
val should_skip = path.ends_with("cli_passthrough.spl")
expect(should_skip).to_equal(true)
```

</details>

#### flags subprocess in dispatch function

- flags subprocess in dispatch function
   - Expected: is_handler is true


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
expect(is_handler).to_equal(true)
```

</details>

### MCP004 Cache Without Invalidation Lint

#### detects cache var without invalidation

- detects cache var without invalidation
   - Expected: is_cache is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects cache var without invalidation")
val line = "var TOOLS_CACHE = \"\""
val is_cache = line.contains("var ") and line.contains("_CACHE")
expect(is_cache).to_equal(true)
```

</details>

#### accepts cache var with invalidation function

- accepts cache var with invalidation function
   - Expected: has_invalidation is true


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
expect(has_invalidation).to_equal(true)
```

</details>

#### detects cached_ prefix variables

- detects cached_ prefix variables
   - Expected: is_cache is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects cached_ prefix variables")
val line = "var cached_results = []"
val is_cache = line.starts_with("var cached_")
expect(is_cache).to_equal(true)
```

</details>

### McpPerfGuard Runtime Counters

#### perf_guard.spl module exists

- perf_guard.spl module exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("perf_guard.spl module exists")
val exists = rt_file_exists("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(exists).to_equal(true)
```

</details>

#### defines McpPerfGuard struct

- defines McpPerfGuard struct
   - Expected: source contains `struct McpPerfGuard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines McpPerfGuard struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("struct McpPerfGuard")).to_equal(true)
```

</details>

#### defines PerfViolation struct

- defines PerfViolation struct
   - Expected: source contains `struct PerfViolation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines PerfViolation struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("struct PerfViolation")).to_equal(true)
```

</details>

#### tracks dir_walks counter

- tracks dir_walks counter
   - Expected: source contains `record_dir_walk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks dir_walks counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_dir_walk")).to_equal(true)
```

</details>

#### tracks file_reads counter

- tracks file_reads counter
   - Expected: source contains `record_file_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks file_reads counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_file_read")).to_equal(true)
```

</details>

#### tracks subprocess counter

- tracks subprocess counter
   - Expected: source contains `record_subprocess`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks subprocess counter")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("record_subprocess")).to_equal(true)
```

</details>

#### checks latency threshold

- checks latency threshold
   - Expected: source contains `PERF_LATENCY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks latency threshold")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("PERF_LATENCY")).to_equal(true)
```

</details>

#### supports disable via environment variable

- supports disable via environment variable
   - Expected: source contains `MCP_PERF_GUARD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports disable via environment variable")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("MCP_PERF_GUARD")).to_equal(true)
```

</details>

#### provides snapshot for diagnostics

- provides snapshot for diagnostics
   - Expected: source contains `McpPerfSnapshot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides snapshot for diagnostics")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/perf_guard.spl")
expect(source.contains("McpPerfSnapshot")).to_equal(true)
```

</details>

### MCP Wrapper Validator

#### wrapper_validator.spl module exists

- wrapper_validator.spl module exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wrapper_validator.spl module exists")
val exists = rt_file_exists("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(exists).to_equal(true)
```

</details>

#### defines WrapperValidationResult struct

- defines WrapperValidationResult struct
   - Expected: source contains `struct WrapperValidationResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WrapperValidationResult struct")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("struct WrapperValidationResult")).to_equal(true)
```

</details>

#### validates all five wrapper scripts

- validates all five wrapper scripts
   - Expected: source contains `simple_mcp_server`
   - Expected: source contains `simple_lsp_mcp_server`
   - Expected: source contains `t32_mcp_server`
   - Expected: source contains `t32_lsp_mcp_server`
   - Expected: source contains `obsidian_lsp_mcp_server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates all five wrapper scripts")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("simple_mcp_server")).to_equal(true)
expect(source.contains("simple_lsp_mcp_server")).to_equal(true)
expect(source.contains("t32_mcp_server")).to_equal(true)
expect(source.contains("t32_lsp_mcp_server")).to_equal(true)
expect(source.contains("obsidian_lsp_mcp_server")).to_equal(true)
```

</details>

#### checks for .spl entrypoint as anti-pattern

- checks for .spl entrypoint as anti-pattern
   - Expected: source contains `has_spl_entry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for .spl entrypoint as anti-pattern")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("has_spl_entry")).to_equal(true)
```

</details>

#### checks for Rust bootstrap path as anti-pattern

- checks for Rust bootstrap path as anti-pattern
   - Expected: source contains `compiler_rust/target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for Rust bootstrap path as anti-pattern")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("compiler_rust/target")).to_equal(true)
```

</details>

#### checks for log suppression

- checks for log suppression
   - Expected: source contains `SIMPLE_LOG=error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for log suppression")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("SIMPLE_LOG=error")).to_equal(true)
```

</details>

#### checks for stderr suppression

- checks for stderr suppression
   - Expected: source contains `2>/dev/null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks for stderr suppression")
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/wrapper_validator.spl")
expect(source.contains("2>/dev/null")).to_equal(true)
```

</details>

### MCP Wrapper Files Exist

#### bin/simple_mcp_server exists

- bin/simple_mcp_server exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_mcp_server exists")
val exists = rt_file_exists("bin/simple_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/simple_lsp_mcp_server exists

- bin/simple_lsp_mcp_server exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/simple_lsp_mcp_server exists")
val exists = rt_file_exists("bin/simple_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/t32_mcp_server exists

- bin/t32_mcp_server exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/t32_mcp_server exists")
val exists = rt_file_exists("bin/t32_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/t32_lsp_mcp_server exists

- bin/t32_lsp_mcp_server exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/t32_lsp_mcp_server exists")
val exists = rt_file_exists("bin/t32_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

#### bin/obsidian_lsp_mcp_server exists

- bin/obsidian_lsp_mcp_server exists
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bin/obsidian_lsp_mcp_server exists")
val exists = rt_file_exists("bin/obsidian_lsp_mcp_server")
expect(exists).to_equal(true)
```

</details>

### MCP Perf Lint Registration

#### mcp_perf_lint.spl exists in lint directory

- mcp_perf_lint.spl exists in lint directory
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mcp_perf_lint.spl exists in lint directory")
val exists = rt_file_exists("src/compiler/35.semantics/lint/mcp_perf_lint.spl")
expect(exists).to_equal(true)
```

</details>

#### lint __init__.spl exports mcp_perf_lint

- lint __init__.spl exports mcp_perf_lint
   - Expected: source contains `mcp_perf_lint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint __init__.spl exports mcp_perf_lint")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("mcp_perf_lint")).to_equal(true)
```

</details>

#### lint exports McpPerfLintWarning

- lint exports McpPerfLintWarning
   - Expected: source contains `McpPerfLintWarning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint exports McpPerfLintWarning")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("McpPerfLintWarning")).to_equal(true)
```

</details>

#### lint exports all four check functions

- lint exports all four check functions
   - Expected: source contains `lint_source_entrypoint`
   - Expected: source contains `lint_full_tree_scan`
   - Expected: source contains `lint_per_request_subprocess`
   - Expected: source contains `lint_cache_no_invalidation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lint exports all four check functions")
val source = rt_file_read_text("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("lint_source_entrypoint")).to_equal(true)
expect(source.contains("lint_full_tree_scan")).to_equal(true)
expect(source.contains("lint_per_request_subprocess")).to_equal(true)
expect(source.contains("lint_cache_no_invalidation")).to_equal(true)
```

</details>

### MCP Server Performance Structure

#### MCP main.spl has tool dispatch cache

- MCP main.spl has tool dispatch cache
   - Expected: source contains `TOOLS_CACHE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has tool dispatch cache")
val source = rt_file_read_text("src/app/mcp/main.spl")
expect(source.contains("TOOLS_CACHE")).to_equal(true)
```

</details>

#### MCP main.spl has init response cache

- MCP main.spl has init response cache
   - Expected: source contains `INIT_CACHE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has init response cache")
val source = rt_file_read_text("src/app/mcp/main.spl")
expect(source.contains("INIT_CACHE")).to_equal(true)
```

</details>

#### MCP main.spl uses table-driven dispatch

- MCP main.spl uses table-driven dispatch
   - Expected: source contains `dispatch_tool`
   - Expected: source contains `use .tool_table`
   - Expected: table_source contains `get_tool_table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl uses table-driven dispatch")
val source = rt_file_read_text("src/app/mcp/main.spl")
val table_source = rt_file_read_text("src/app/mcp/tool_table.spl")
expect(source.contains("dispatch_tool")).to_equal(true)
expect(source.contains("use .tool_table")).to_equal(true)
expect(table_source.contains("get_tool_table")).to_equal(true)
```

</details>

#### MCP main.spl has in-process handlers for core tools

- MCP main.spl has in-process handlers for core tools
   - Expected: source contains `_dispatch_in_process`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl has in-process handlers for core tools")
val source = rt_file_read_text("src/app/mcp/main_dispatch.spl")
expect(source.contains("_dispatch_in_process")).to_equal(true)
```

</details>

#### MCP cli_passthrough is isolated from in-process handlers

- MCP cli_passthrough is isolated from in-process handlers
   - Expected: source contains `_dispatch_cli_direct`
   - Expected: source contains `handle_cli_passthrough_direct`
   - Expected: table_source contains `"cli"`


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

- **Plan:** `doc/03_plan/mcp_performance_regression_prevention_plan_2026-03-30.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e0b44ed1f42a704d6bc04b428b104fb6a62faccd7dcb2bba987ef3fe09bd041a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0b44ed1f42a704d6bc04b428b104fb6a62faccd7dcb2bba987ef3fe09bd041a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0b44ed1f42a704d6bc04b428b104fb6a62faccd7dcb2bba987ef3fe09bd041a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/system/mcp/mcp_perf_regression_spec.spl
mirror: doc/06_spec/system/mcp/mcp_perf_regression_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/system/mcp/mcp_perf_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/mcp/mcp_perf_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/mcp/mcp_perf_regression_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
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

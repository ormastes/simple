# MCP Failure Prevention

> Release-blocking regression matrix for operators maintaining Simple MCP and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Failure Prevention

Release-blocking regression matrix for operators maintaining Simple MCP and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl` |
| Updated | 2026-08-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Release-blocking regression matrix for operators maintaining Simple MCP and
Simple LSP MCP. It joins the existing source-loader, wrapper-admission, live
protocol/tool, cache-invalidation, and warm performance gates without replacing
their detailed diagnostics.

## Preconditions

The normal `bin/simple` must be a freshly admitted pure-Simple compiler. The
production MCP and LSP wrappers must select executable, SHA-256-bound native
artifacts. Rust-seed or source fallback is failure evidence.

## Operator workflow

Run this spec after compiler source-loading, runtime-symbol, MCP/LSP, wrapper,
or packaging changes. Read the first failing step and then run the named
canonical checker directly for its retained diagnostics.

## Compatibility and limitations

The source contract is supporting evidence only. Endpoint acceptance comes from
the native smoke and NFR sessions, which launch both production wrappers and
make correlated tool calls.

## Scenarios

### MCP failure prevention matrix

### REQ-MCP-CMD-001: bounded pure-Simple startup ownership

#### should keep interpreted entries lazy and register the MCP file probe for JIT

- Verify interpreter source loading stays bounded
- Verify the JIT provider owns every MCP startup file probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify interpreter source loading stays bounded")
val loading = file_read(
    "src/compiler/80.driver/driver_source_pipeline_loading.spl")
val resolver = file_read(
    "src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl")
expect(loading).to_contain(
    "compile_mode != CompileMode.Interpret")
expect(loading).to_contain(
    "if has_project_source and needs_bulk_project_sources and not nb_entry_closure:")
expect(resolver).to_contain(
    "val simple_lib = rt_env_get(\"SIMPLE_LIB\")")

step("Verify the JIT provider owns every MCP startup file probe")
val symbols = file_read(
    "src/compiler_rust/common/src/runtime_symbols.rs")
val metadata = file_read(
    "src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs")
val exports = file_read(
    "src/compiler_rust/runtime/src/value/sffi/file_io/mod.rs")
expect(symbols).to_contain("\"rt_file_is_char_device\"")
expect(metadata).to_contain(
    "extern \"C\" fn rt_file_is_char_device")
expect(exports).to_contain("rt_file_is_char_device")
```

</details>

### REQ-MCP-CMD-002: admitted production wrappers

#### should reject source fallback and require native wrapper contracts

- Verify wrappers admit only hash-bound native artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify wrappers admit only hash-bound native artifacts")
val result = run_mcp_gate(
    "sh", ["scripts/check/check-mcp-wrapper-contract.shs"], 30000)
check_gate_pass(result)
check_marker(result, "mcp_wrapper_source_contract=pass")
check_marker(result, "mcp_wrapper_native_contract=pass")
```

</details>

<details>
<summary>Advanced: should exercise MCP and LSP protocol functions through production wrappers</summary>

#### should exercise MCP and LSP protocol functions through production wrappers _(slow)_

- Exercise MCP and LSP protocol functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise MCP and LSP protocol functions")
val result = run_mcp_gate(
    "sh", ["scripts/check/check-mcp-native-smoke.shs"], 180000)
check_gate_pass(result)
check_marker(result, "mcp_app_direct_rt_valid=true")
check_marker(result, "lsp_mcp_app_direct_rt_valid=true")
check_marker(result, "mcp_stdio_spec_direct_rt_valid=true")
check_marker(result, "mcp_core_request_ids_preserved=true")
check_marker(result, "mcp_startup_under_5000ms=true")
check_marker(result, "lsp_mcp_startup_under_5000ms=true")
check_marker(result, "mcp_second_start_ok=true")
check_marker(result, "mcp_stale_stamp_reprobe_ok=true")
check_marker(result, "mcp_tools_json_valid=true")
check_marker(result, "mcp_tools_schema_valid=true")
check_marker(result, "mcp_correlated_ids_valid=true")
check_marker(result, "mcp_main_feature_call_valid=true")
check_marker(result, "lsp_tools_json_valid=true")
check_marker(result, "lsp_tools_schema_valid=true")
check_marker(result, "lsp_correlated_ids_valid=true")
check_marker(result, "lsp_main_feature_call_valid=true")
```

</details>


</details>

### REQ-MCP-003 and REQ-MCP-005: bounded hot paths

<details>
<summary>Advanced: should keep warm MCP and LSP startup latency request p95 and RSS bounded</summary>

#### should keep warm MCP and LSP startup latency request p95 and RSS bounded _(slow)_

- Measure warm startup, request latency, and RSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure warm startup, request latency, and RSS")
val result = run_mcp_gate("env", [
    "MCP_LSP_NFR_SAMPLES=20",
    "sh", "scripts/check/check-mcp-lsp-nfr-evidence.shs"
], 180000)
check_gate_pass(result)
check_marker(result, "mcp_wrapper_sha256=")
check_marker(result, "mcp_native_sha256=")
check_marker(result, "mcp_startup_ms=")
check_marker(result, "mcp_request_p95_ms=")
check_marker(result, "mcp_max_rss_kib=")
check_marker(result, "lsp_wrapper_sha256=")
check_marker(result, "lsp_native_sha256=")
check_marker(result, "lsp_startup_ms=")
check_marker(result, "lsp_request_p95_ms=")
check_marker(result, "lsp_max_rss_kib=")
check_marker(result, "mcp_lsp_nfr_status=pass")
```

</details>


</details>

#### should fail closed when the NFR sample count is invalid

- Reject an invalid performance evidence configuration
   - Expected: result.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an invalid performance evidence configuration")
val result = run_mcp_gate("env", [
    "MCP_LSP_NFR_SAMPLES=0",
    "sh", "scripts/check/check-mcp-lsp-nfr-evidence.shs"
], 10000)
expect(result.exit_code).to_equal(2)
expect(result.stdout).to_contain("error=invalid_sample_count:0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

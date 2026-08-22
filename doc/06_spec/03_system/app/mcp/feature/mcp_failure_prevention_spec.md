# MCP Failure Prevention

> Verifies the mcp failure prevention behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Failure Prevention

Verifies the mcp failure prevention behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the mcp failure prevention behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### MCP failure prevention matrix

### REQ-MCP-CMD-001: bounded pure-Simple startup ownership

#### should keep interpreted entries lazy and register the MCP file probe for JIT

- Verify: should keep interpreted entries lazy and register the MCP file probe for JIT
- Verify interpreter source loading stays bounded
- Verify the JIT provider owns every MCP startup file probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001 REQ-MCP-CMD-002 REQ-MCP-001 REQ-MCP-003 REQ-MCP-005
step("Verify: should keep interpreted entries lazy and register the MCP file probe for JIT")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should reject source fallback and require native wrapper contracts
- Verify wrappers admit only hash-bound native artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001 REQ-MCP-CMD-002 REQ-MCP-001 REQ-MCP-003 REQ-MCP-005
step("Verify: should reject source fallback and require native wrapper contracts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should exercise MCP and LSP protocol functions through production wrappers
- Exercise MCP and LSP protocol functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001 REQ-MCP-CMD-002 REQ-MCP-001 REQ-MCP-003 REQ-MCP-005
step("Verify: should exercise MCP and LSP protocol functions through production wrappers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should keep warm MCP and LSP startup latency request p95 and RSS bounded
- Measure warm startup, request latency, and RSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001 REQ-MCP-CMD-002 REQ-MCP-001 REQ-MCP-003 REQ-MCP-005
step("Verify: should keep warm MCP and LSP startup latency request p95 and RSS bounded")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: should fail closed when the NFR sample count is invalid
- Reject an invalid performance evidence configuration
   - Expected: result.exit_code equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-MCP-CMD-001 REQ-MCP-CMD-002 REQ-MCP-001 REQ-MCP-003 REQ-MCP-005
step("Verify: should fail closed when the NFR sample count is invalid")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Reject an invalid performance evidence configuration")
val result = run_mcp_gate("env", [
    "MCP_LSP_NFR_SAMPLES=0",
    "sh", "scripts/check/check-mcp-lsp-nfr-evidence.shs"
], 10000)
expect(result.exit_code).to_equal(2)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5c839ec69517b1777710093432ff9de5b1b898466f9c7868565419204ef1adfb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c839ec69517b1777710093432ff9de5b1b898466f9c7868565419204ef1adfb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c839ec69517b1777710093432ff9de5b1b898466f9c7868565419204ef1adfb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl
mirror: doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep interpreted entries lazy and register the MCP file probe for JIT' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:102:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject source fallback and require native wrapper contracts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise MCP and LSP protocol functions through production wrappers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep warm MCP and LSP startup latency request p95 and RSS bounded' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:161:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when the NFR sample count is invalid' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

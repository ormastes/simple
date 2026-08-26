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
| Updated | 2026-08-26 |
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
### REQ-MCP-CMD-002: admitted production wrappers

#### should reject source fallback and require native wrapper contracts

- should reject source fallback and require native wrapper contracts
- Verify wrappers admit only hash-bound native artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject source fallback and require native wrapper contracts")
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

- should exercise MCP and LSP protocol functions through production wrappers
- Exercise MCP and LSP protocol functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exercise MCP and LSP protocol functions through production wrappers")
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

- should keep warm MCP and LSP startup latency request p95 and RSS bounded
- Measure warm startup, request latency, and RSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep warm MCP and LSP startup latency request p95 and RSS bounded")
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

- should fail closed when the NFR sample count is invalid
- Reject an invalid performance evidence configuration
   - Expected: result.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed when the NFR sample count is invalid")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MCP-CMD-001`
- `REQ-MCP-CMD-002`
- `REQ-MCP-003`
- `REQ-MCP-005`
- `REQ-MCP-005:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9dad582f53bea8423f3917aa6365e315454287a4471682defcf658931e66f90c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dad582f53bea8423f3917aa6365e315454287a4471682defcf658931e66f90c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dad582f53bea8423f3917aa6365e315454287a4471682defcf658931e66f90c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl
mirror: doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md (current)
findings: 13 blockers: 1
  narrative=100 structure=65 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/mcp/feature/mcp_failure_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:63:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep interpreted entries lazy and register the MCP file probe for JIT' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep interpreted entries lazy and register the MCP file probe for JIT' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject source fallback and require native wrapper contracts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject source fallback and require native wrapper contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise MCP and LSP protocol functions through production wrappers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exercise MCP and LSP protocol functions through production wrappers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep warm MCP and LSP startup latency request p95 and RSS bounded' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep warm MCP and LSP startup latency request p95 and RSS bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl:152:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when the NFR sample count is invalid' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

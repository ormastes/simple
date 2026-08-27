# MCP Lazy Loading Performance Specification

> Performance verification for MCP server startup with lazy imports. The MCP full server uses `use lazy` for 5 heavy tool modules (34 tools), deferring their loading until first tool invocation.

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
| Updated | 2026-08-26 |
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

- MCP main.spl exists and uses lazy imports
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP main.spl exists and uses lazy imports")
val exists = rt_file_exists("src/app/mcp/main.spl")
expect(exists).to_equal(true)
```

</details>

#### MCP helper modules are kept eager

- MCP helper modules are kept eager
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MCP helper modules are kept eager")
# Helpers and protocol are needed at startup
val exists = mcp_module_exists("helpers")
expect(exists).to_equal(true)
```

</details>

#### debug tools module exists for lazy loading

- debug tools module exists for lazy loading
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("debug tools module exists for lazy loading")
val exists = mcp_module_exists("main_lazy_debug_tools") or mcp_module_exists("debug_tools")
expect(exists).to_equal(true)
```

</details>

#### debug log tools module exists for lazy loading

- debug log tools module exists for lazy loading
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("debug log tools module exists for lazy loading")
val exists = mcp_module_exists("main_lazy_debug_log_tools") or mcp_module_exists("debug_log_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic read tools module exists for lazy loading

- diagnostic read tools module exists for lazy loading
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic read tools module exists for lazy loading")
val exists = mcp_module_exists("main_lazy_diag_tools") or mcp_module_exists("diag_read_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic edit tools module exists for lazy loading

- diagnostic edit tools module exists for lazy loading
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic edit tools module exists for lazy loading")
val exists = mcp_module_exists("main_lazy_diag_tools") or mcp_module_exists("diag_edit_tools")
expect(exists).to_equal(true)
```

</details>

#### diagnostic vcs tools module exists for lazy loading

- diagnostic vcs tools module exists for lazy loading
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostic vcs tools module exists for lazy loading")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e2b7d1c2a0ca39729356fd28452bc90fe2db1869317e820f258e2dbfd6a6ad7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2b7d1c2a0ca39729356fd28452bc90fe2db1869317e820f258e2dbfd6a6ad7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2b7d1c2a0ca39729356fd28452bc90fe2db1869317e820f258e2dbfd6a6ad7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/mcp/mcp_lazy_perf_spec.spl
mirror: doc/06_spec/03_system/tools/mcp/mcp_lazy_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/mcp/mcp_lazy_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/mcp/mcp_lazy_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/mcp/mcp_lazy_perf_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MCP main.spl exists and uses lazy imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/mcp/mcp_lazy_perf_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MCP helper modules are kept eager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/mcp/mcp_lazy_perf_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'debug tools module exists for lazy loading' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

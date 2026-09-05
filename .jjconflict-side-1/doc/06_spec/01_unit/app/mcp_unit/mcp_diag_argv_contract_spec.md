# Mcp Diag Argv Contract Specification

> Tests covering MCP diagnostic argv contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Diag Argv Contract Specification

## Scenarios

### MCP diagnostic argv contract

#### does not execute diagnostic API query as shell syntax

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not execute diagnostic API query as shell syntax
   - Expected: injected is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not execute diagnostic API query as shell syntax")
val sentinel = "/tmp/simple_mcp_diag_argv_injection_" + str(rt_getpid())
val _ = rt_file_delete(sentinel)
val body = "{\"query\":\"absent; touch " + sentinel + "\"}"

val _result = handle_simple_api("1", body)

val injected = rt_file_exists(sentinel)
if injected:
    val _ = rt_file_delete(sentinel)
expect(injected).to_equal(false)
```

</details>

#### rejects option-like status directories before find

- rejects option-like status directories before find


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects option-like status directories before find")
val source = file_read("src/app/mcp/main_lazy_diag_tools.spl")

expect(source).to_contain('scan_dir.starts_with("-")')
expect(source).to_contain("option-like paths are not allowed")
```

</details>

#### routes request-derived diagnostics through argv

- routes request-derived diagnostics through argv
   - Expected: source does not contain `shell_cmd(search_cmd)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("routes request-derived diagnostics through argv")
val source = file_read("src/app/mcp/main_lazy_diag_tools.spl")

expect(source).to_contain('mcp_run_argv(_bin, ["check", path], 30000, 262144)')
expect(source).to_contain('"symbols", path, "--requester", path')
expect(source).to_contain('mcp_run_argv("find", [scan_dir, "-name", "*.spl", "-type", "f"], 10000, 262144)')
expect(source).to_contain('mcp_run_argv("grep", ["-r", "-n", "--include=*.spl", "--", query, "src/"], 15000, 262144)')
expect(source.contains("shell_cmd(search_cmd)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP diagnostic argv contract.
- MCP diagnostic argv contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6defb7b449e137979bab1842e89e126da2b65324350bcc105381304946525ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6defb7b449e137979bab1842e89e126da2b65324350bcc105381304946525ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6defb7b449e137979bab1842e89e126da2b65324350bcc105381304946525ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl
mirror: doc/06_spec/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not execute diagnostic API query as shell syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects option-like status directories before find' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp_unit/mcp_diag_argv_contract_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes request-derived diagnostics through argv' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

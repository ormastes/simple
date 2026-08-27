# Lsp Diagnostics Timeout Specification

> Tests covering simple_lsp_mcp diagnostics timeout guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Diagnostics Timeout Specification

## Scenarios

### simple_lsp_mcp diagnostics timeout guard

#### uses a bounded process run for opt-in diagnostics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses a bounded process run for opt-in diagnostics
   - Expected: source does not contain `process_run_timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses a bounded process run for opt-in diagnostics")
val source = rt_file_read_text("src/app/simple_lsp_mcp/tools.spl") ?? ""

expect(source).to_contain("process_run_bounded")
expect(source.contains("process_run_timeout")).to_equal(false)
expect(source).to_contain("LSP_DIAGNOSTICS_OUTPUT_CAPTURE_BYTES")
expect(source).to_contain("find_simple_binary()")
expect(source).to_contain("10000")
expect(source).to_contain("diagnostics unavailable in source mode")
```

</details>

#### keeps client position parsing on the safe digit parser

- keeps client position parsing on the safe digit parser
   - Expected: main_source does not contain `line_raw.to_int()`
   - Expected: main_source does not contain `char_raw.to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps client position parsing on the safe digit parser")
val main_source = rt_file_read_text("src/app/simple_lsp_mcp/main.spl") ?? ""
val tools_source = rt_file_read_text("src/app/simple_lsp_mcp/tools.spl") ?? ""

expect(main_source).to_contain("arg_int_field(a, \"line\")")
expect(main_source).to_contain("arg_int_field(a, \"character\")")
expect(main_source.contains("line_raw.to_int()")).to_equal(false)
expect(main_source.contains("char_raw.to_int()")).to_equal(false)
expect(tools_source).to_contain("parse_nonnegative_int_or_minus_one(line_str)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_lsp_mcp diagnostics timeout guard.
- simple_lsp_mcp diagnostics timeout guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b37e5f123eb962b92f6d3ab4dfc01e10807212b5b87ca826429d3473d0ea2fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b37e5f123eb962b92f6d3ab4dfc01e10807212b5b87ca826429d3473d0ea2fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b37e5f123eb962b92f6d3ab4dfc01e10807212b5b87ca826429d3473d0ea2fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps client position parsing on the safe digit parser' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

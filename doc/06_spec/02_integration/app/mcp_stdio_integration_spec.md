# MCP Protocol Runtime

> Exercise initialize, tools/list, and an unknown tools/call request through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Protocol Runtime

Exercise initialize, tools/list, and an unknown tools/call request through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Source | `test/02_integration/app/mcp_stdio_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

**Requirements:** N/A

- The server accepts Content-Length framing and JSONL transport.
- Initialize and tools/list return valid full-server responses.
- Unknown tools return tool-level errors rather than JSON-RPC failures.

## Plan

Exercise initialize, tools/list, and an unknown tools/call request through the
installed wrapper with the full tool set enabled.

## Design

The spec writes protocol input to a temporary file and drives the production
stdio wrapper through a shell pipe.

## Research

N/A

## Scenarios

### MCP Protocol Runtime

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ee6f5959c215a47b3fb2c34150cd97e38b97fcc8249aa570fb802c3b9378496`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ee6f5959c215a47b3fb2c34150cd97e38b97fcc8249aa570fb802c3b9378496`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ee6f5959c215a47b3fb2c34150cd97e38b97fcc8249aa570fb802c3b9378496`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/mcp_stdio_integration_spec.spl
mirror: doc/06_spec/02_integration/app/mcp_stdio_integration_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=55 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/mcp_stdio_integration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/mcp_stdio_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/mcp_stdio_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/mcp_stdio_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/mcp_stdio_integration_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates a correlated core wrapper from tracked setup source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/mcp_stdio_integration_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves numeric and string request ids in the production core wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/mcp_stdio_integration_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles initialize, tools/list, and unknown-tool MCP startup flows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

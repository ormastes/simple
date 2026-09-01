# Query Visibility Workspace Symbols Specification

> Tests covering query_visibility workspace-symbols CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Workspace Symbols Specification

## Scenarios

### query_visibility workspace-symbols CLI

#### returns reachable symbols with structured visibility metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns reachable symbols with structured visibility metadata
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns reachable symbols with structured visibility metadata")
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query lsp_main --requester src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"lsp_main\""))
check(stdout.contains("\"simpleVisibility\""))
check(stdout.contains("\"display\":\"private\""))
check(stderr == "")
```

</details>

#### filters non reachable boundary-private symbols across boundaries

- filters non reachable boundary-private symbols across boundaries
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("filters non reachable boundary-private symbols across boundaries")
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query query_visibility --requester src/lib/nogc_sync_mut/lsp/main.spl"
)

expect(code).to_equal(0)
expect(stdout.trim()).to_equal("[]")
check(stderr == "")
```

</details>

#### returns same-boundary private symbols in stable ranked order

- returns same-boundary private symbols in stable ranked order
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns same-boundary private symbols in stable ranked order")
val (stdout, stderr, code) = run_shell(
    "bin/simple run src/app/cli/query_visibility.spl workspace-symbols --query query_visibility --requester src/app/cli/query_visibility.spl"
)

expect(code).to_equal(0)
check(stdout.contains("\"name\":\"query_visibility_main\""))
check(stdout.contains("\"name\":\"query_visibility_workspace_symbols\""))
val main_idx = stdout.index_of("\"name\":\"query_visibility_main\"")
val workspace_idx = stdout.index_of("\"name\":\"query_visibility_workspace_symbols\"")
check(main_idx >= 0)
check(workspace_idx >= 0)
check(main_idx < workspace_idx)
check(stdout.contains("\"boundaryModule\":\"app.cli\""))
check(stderr == "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/query_visibility_workspace_symbols_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering query_visibility workspace-symbols CLI.
- query_visibility workspace-symbols CLI

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62c96a326d71e7c52bafd6d13f9af70586283b859573f7802b628f16fed9bd64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62c96a326d71e7c52bafd6d13f9af70586283b859573f7802b628f16fed9bd64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62c96a326d71e7c52bafd6d13f9af70586283b859573f7802b628f16fed9bd64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/query_visibility_workspace_symbols_spec.spl
mirror: doc/06_spec/integration/app/query_visibility_workspace_symbols_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/query_visibility_workspace_symbols_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/query_visibility_workspace_symbols_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/query_visibility_workspace_symbols_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/query_visibility_workspace_symbols_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns reachable symbols with structured visibility metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/query_visibility_workspace_symbols_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters non reachable boundary-private symbols across boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/query_visibility_workspace_symbols_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns same-boundary private symbols in stable ranked order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

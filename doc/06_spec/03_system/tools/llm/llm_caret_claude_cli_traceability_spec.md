# LLM Caret Claude CLI Traceability Specification

> This system spec proves the Claude CLI migration trace remains current enough to guide hardening work. The checker computes the current `src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every current Simple function, struct, and extern symbol appears in the trace table.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Traceability Specification

This system spec proves the Claude CLI migration trace remains current enough to guide hardening work. The checker computes the current `src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every current Simple function, struct, and extern symbol appears in the trace table.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_harden.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_harden.md |
| Design | doc/05_design/llm_caret_claude_cli_harden.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves the Claude CLI migration trace remains current enough
to guide hardening work. The checker computes the current
`src/app/llm_caret/*.spl` file and LOC mapping coverage, then confirms every
current Simple function, struct, and extern symbol appears in the trace table.

## Syntax

```bash
sh scripts/check/check-llm-caret-claude-cli-trace.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl --mode=interpreter
```

## Examples

A passing checker prints `llm_caret_mapping_percent=100`,
`llm_caret_loc_mapping_percent=100`,
`llm_caret_symbol_traced_count=505`, and
`STATUS: PASS llm-caret-claude-cli-trace` for the current mapped caret.

## Workflow

1. Inspect the Claude source tree under `tmp/claude/claude-code-main/src`.
2. Extract feature groups, not copied implementation bodies.
3. Map each Simple source file in `src/app/llm_caret` to a Claude source file
   or to an explicit Simple-only provider extension.
4. Record the mapping in
   `doc/09_report/llm_caret_claude_cli_traceability.md`.
5. Run the checker.
6. Run this SSpec.
7. Regenerate this manual with `bin/simple spipe-docgen`.

## Source Contract

The report must keep these sections:

- `## MDSOC+ Caret Boundary`
- `## Extracted Claude CLI Features`
- `## Source File Mapping`
- `## Function Trace`
- `## Simple Symbol Trace`
- `## Claude Source Trace`
- `## Claude Key Symbol Trace`
- `## Verification`

The mapping table must include every current `src/app/llm_caret/*.spl` file,
and the symbol table must include every current function, struct, and extern
symbol as a backticked `kind:name` token. The checker computes those lists
from the filesystem, so adding a provider file or symbol without trace rows
fails the gate.

## Coverage Rule

The required threshold is 80% mapped files and 80% mapped LOC. A Simple-only
extension still counts when the row says it is Simple-only and names the role.
This keeps non-Claude providers such as OpenCode, OpenAI-compatible endpoints,
and local torch visible without pretending they came from Claude Code.

## MDSOC+ Rule

`src/app/llm_caret` remains one app-layer provider caret. The trace report may
point to runtime or HTTP facades as dependencies, but this lane must not move
runtime ownership into the app caret. Runtime boundary fixes belong in a
separate implementation lane.

## Out Of Scope

The gate does not prove live Claude authentication, remote control, OAuth,
terminal UI parity, or agent orchestration. It proves the migration map and the
offline traceability contract only.

## Failure Handling

If the checker prints `STATUS: FAIL`, inspect the key before editing code:

- `llm_caret_mapping_percent` below 80 means source files were added without
  trace rows.
- `llm_caret_loc_mapping_percent` below 80 means the unmapped files exceed the
  allowed LOC budget.
- `missing_symbol_trace` means a function, struct, or extern exists in source
  without a `kind:name` entry in the Simple Symbol Trace.
- `missing_marker` means the report lost a required operator section.
- `llm_caret_trace_report=missing` means the report path changed or was not
  generated.

Fix the report or checker first, then rerun this SSpec once. Do not bypass the
gate with placeholder rows; each row must name either a Claude source match or
an explicit Simple-only role.

## Operator Checklist

- The checker path exists.
- The report path exists.
- The report names the `tmp/claude/claude-code-main/src` evidence root.
- The report maps `src/app/llm_caret/claude_cli.spl`.
- The report names `src/entrypoints/cli.tsx`.
- The report names `src/QueryEngine.ts`.
- The report names key Claude-side symbols such as `class:QueryEngine`.
- The checker reports source-file count.
- The checker reports mapped-file count.
- The checker reports mapping percent.
- The checker reports source LOC.
- The checker reports mapped LOC.
- The checker reports LOC mapping percent.
- The checker reports symbol count.
- The checker reports traced symbol count.
- The checker reports `STATUS: PASS llm-caret-claude-cli-trace`.

## Evidence Produced

The passing SSpec output proves the trace report and checker are present and
that the checker accepts the current mapping. The checker output records the
current file count and percentage, which is the release evidence for the 80%
mapping gate.

## Scenarios

### LLM caret Claude CLI traceability

### REQ-LLM-CARET-CLAUDE-TRACE-001..002: mapped artifacts

#### should keep the report checker and exact symbol inventory together
#### should document MDSOC ownership and both Claude and Simple mappings

- should document MDSOC ownership and both Claude and Simple mappings
- Inspect the Claude-to-Simple trace report


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should document MDSOC ownership and both Claude and Simple mappings")
step("Inspect the Claude-to-Simple trace report")
val report = file_read(TRACE_REPORT)

expect(report).to_contain("## MDSOC+ Caret Boundary")
expect(report).to_contain("## Source File Mapping")
expect(report).to_contain("## Function Trace")
expect(report).to_contain("## Simple Symbol Trace")
expect(report).to_contain("## Claude Source Trace")
expect(report).to_contain("## Claude Key Symbol Trace")
expect(report).to_contain("tmp/claude/claude-code-main/src")
expect(report).to_contain("src/app/llm_caret/claude_cli.spl")
expect(report).to_contain("src/entrypoints/cli.tsx")
expect(report).to_contain("src/QueryEngine.ts")
expect(report).to_contain("class:QueryEngine")
```

</details>

### NFR-LLM-CARET-TRACE-001..004: offline deterministic derivation

#### should derive the inventory offline from files and stable text tools

- should derive the inventory offline from files and stable text tools
- Inspect the trace checker execution boundary
   - Expected: trace_checker_has_forbidden_network_command(source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive the inventory offline from files and stable text tools")
step("Inspect the trace checker execution boundary")
val source = file_read(TRACE_CHECK)

expect(trace_checker_has_forbidden_network_command(source)).to_equal(false)
expect(source).to_contain("find \"$src_dir\"")
expect(source).to_contain("sort -u")
expect(source).to_contain("mktemp")
expect(source).to_contain("trap")
```

</details>

### REQ-LLM-CARET-CLAUDE-TRACE-003..005: computed closure

#### should pass exact file LOC and declaration coverage for the current caret

- should pass exact file LOC and declaration coverage for the current caret
- Run the computed traceability checker once
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should pass exact file LOC and declaration coverage for the current caret")
step("Run the computed traceability checker once")
val result = run_trace_check()
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("llm_caret_source_files=25")
expect(output).to_contain("llm_caret_mapped_files=25")
expect(output).to_contain("llm_caret_mapping_percent=100")
expect(output).to_contain("llm_caret_source_loc=7194")
expect(output).to_contain("llm_caret_mapped_loc=7194")
expect(output).to_contain("llm_caret_loc_mapping_percent=100")
expect(output).to_contain("llm_caret_symbol_count=505")
expect(output).to_contain("llm_caret_symbol_traced_count=505")
expect(output).to_contain("STATUS: PASS llm-caret-claude-cli-trace")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_harden.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_harden.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_harden.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-CLAUDE-TRACE-001`
- `REQ-LLM-CARET-CLAUDE-TRACE-002`
- `REQ-LLM-CARET-CLAUDE-TRACE-003`
- `REQ-LLM-CARET-CLAUDE-TRACE-004`
- `REQ-LLM-CARET-CLAUDE-TRACE-005`
- `REQ-LLM-CARET-CLAUDE-TRACE-001..002`
- `REQ-LLM-CARET-CLAUDE-TRACE-003..005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80af5b91f1ee8868a6bcd607b9ce23365d3fb55062d84a7a24a98b8a5a76d229`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80af5b91f1ee8868a6bcd607b9ce23365d3fb55062d84a7a24a98b8a5a76d229`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80af5b91f1ee8868a6bcd607b9ce23365d3fb55062d84a7a24a98b8a5a76d229`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl
mirror: doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 7 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:165:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should keep the report checker and exact symbol inventory together' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:165:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the report checker and exact symbol inventory together' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:186:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should document MDSOC ownership and both Claude and Simple mappings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should document MDSOC ownership and both Claude and Simple mappings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:205:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive the inventory offline from files and stable text tools' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive the inventory offline from files and stable text tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:218:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass exact file LOC and declaration coverage for the current caret' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pass exact file LOC and declaration coverage for the current caret' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

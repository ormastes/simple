# Cli Helpers Cycle Specification

> Tests covering CLI helpers dependency shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Helpers Cycle Specification

## Scenarios

### CLI helpers dependency shape

#### loads on leaf imports without reaching back through app.cli.main

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads on leaf imports without reaching back through app.cli.main
   - Expected: sdn_line_indent("    run-config: x") equals `4`
   - Expected: sdn_line_indent("\trun-config: x") equals `4`
   - Expected: sdn_line_indent("run-config: x") equals `0`
   - Expected: strip_sdn_quotes("\"hello\"") equals `hello`
   - Expected: strip_sdn_quotes("'hello'") equals `hello`
   - Expected: strip_sdn_quotes("hello") equals `hello`
   - Expected: strip_sdn_quotes("\"") equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("loads on leaf imports without reaching back through app.cli.main")
# oracle: importing the module here and executing its leaf helpers is the
# runtime proof that no import cycle through app.cli.main exists — a cycle
# would fail module resolution before these calls could run.
expect(get_version()).to_contain("1.")
# oracle: indent counts leading spaces, tabs count as 4
expect(sdn_line_indent("    run-config: x")).to_equal(4)
expect(sdn_line_indent("\trun-config: x")).to_equal(4)
expect(sdn_line_indent("run-config: x")).to_equal(0)
# oracle: surrounding quotes are stripped once, inner text preserved
expect(strip_sdn_quotes("\"hello\"")).to_equal("hello")
expect(strip_sdn_quotes("'hello'")).to_equal("hello")
expect(strip_sdn_quotes("hello")).to_equal("hello")
expect(strip_sdn_quotes("\"")).to_equal("\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/cli_helpers_cycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI helpers dependency shape.
- CLI helpers dependency shape

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `121d644e3ea33f49d8f6267718f3481caa9743d351a3fd738b86617f42a7d420`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `121d644e3ea33f49d8f6267718f3481caa9743d351a3fd738b86617f42a7d420`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `121d644e3ea33f49d8f6267718f3481caa9743d351a3fd738b86617f42a7d420`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/cli/cli_helpers_cycle_spec.spl
mirror: doc/06_spec/01_unit/app/cli/cli_helpers_cycle_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/cli_helpers_cycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/cli_helpers_cycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/cli_helpers_cycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/cli_helpers_cycle_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads on leaf imports without reaching back through app.cli.main' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

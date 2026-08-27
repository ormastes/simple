# Query Diagnostics Specification

> Tests covering query diagnostics helpers, query dispatcher boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Diagnostics Specification

## Scenarios

### query diagnostics helpers

#### splits structured error metadata into core related and help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits structured error metadata into core related and help
   - Expected: structured.0 equals `10:4: variable not found`
   - Expected: structured.1.len() equals `1`
   - Expected: structured.1[0] equals `3:1:declared here`
   - Expected: structured.2 equals `did you mean `value`?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits structured error metadata into core related and help")
val structured = _split_structured_error("10:4: variable not found|||RELATED:3:1:declared here|||HELP:did you mean `value`?")
expect(structured.0).to_equal("10:4: variable not found")
expect(structured.1.len()).to_equal(1)
expect(structured.1[0]).to_equal("3:1:declared here")
expect(structured.2).to_equal("did you mean `value`?")
```

</details>

#### extracts explicit error code before fallback inference

- extracts explicit error code before fallback inference
   - Expected: code equals `E1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts explicit error code before fallback inference")
val code = _extract_error_code("error[E1234]: example failure", "TypeError")
expect(code).to_equal("E1234")
```

</details>

#### keeps lint json collection in the lint orchestrator

- keeps lint json collection in the lint orchestrator
   - Expected: content contains `fn _collect_lint_diagnostics_json(file: text, source: text)`
   - Expected: content contains `_emit_source_lint_diagnostics(file, source, "json")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps lint json collection in the lint orchestrator")
val content = rt_file_read_text("src/app/cli/query_lint.spl") ?? ""
expect(content.contains("fn _collect_lint_diagnostics_json(file: text, source: text)")).to_equal(true)
expect(content.contains("_emit_source_lint_diagnostics(file, source, \"json\")")).to_equal(true)
```

</details>

### query dispatcher boundaries

#### dispatcher delegates diagnostics commands through query_rich imports

- dispatcher delegates diagnostics commands through query_rich imports
   - Expected: content contains `use app.cli.query_rich.{`
   - Expected: content contains `query_check`
   - Expected: content contains `query_workspace_diagnostics`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatcher delegates diagnostics commands through query_rich imports")
val content = rt_file_read_text("src/app/cli/query.spl") ?? ""
expect(content.contains("use app.cli.query_rich.{")).to_equal(true)
expect(content.contains("query_check")).to_equal(true)
expect(content.contains("query_workspace_diagnostics")).to_equal(true)
```

</details>

#### dispatcher no longer defines local fallback diagnostics helpers

- dispatcher no longer defines local fallback diagnostics helpers
   - Expected: not content contains `fn _query_check_json(`
   - Expected: not content contains `fn _query_diag(`
   - Expected: not content contains `fn _query_line_of(`
   - Expected: not content contains `fn _query_line_after(`
   - Expected: not content contains `fn _query_error_count(`
   - Expected: not content contains `fn query_check(`
   - Expected: not content contains `fn query_workspace_diagnostics(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatcher no longer defines local fallback diagnostics helpers")
val content = rt_file_read_text("src/app/cli/query.spl") ?? ""
expect(not content.contains("fn _query_check_json(")).to_equal(true)
expect(not content.contains("fn _query_diag(")).to_equal(true)
expect(not content.contains("fn _query_line_of(")).to_equal(true)
expect(not content.contains("fn _query_line_after(")).to_equal(true)
expect(not content.contains("fn _query_error_count(")).to_equal(true)
expect(not content.contains("fn query_check(")).to_equal(true)
expect(not content.contains("fn query_workspace_diagnostics(")).to_equal(true)
```

</details>

#### diagnostics module depends on lint orchestrator instead of low-level lint internals

- diagnostics module depends on lint orchestrator instead of low-level lint internals
   - Expected: content contains `use app.cli.query_lint.{`
   - Expected: content does not contain `use app.cli.query_lint_checks.{`
   - Expected: content does not contain `use app.cli.query_lint_scan.{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diagnostics module depends on lint orchestrator instead of low-level lint internals")
val content = rt_file_read_text("src/app/cli/query_diagnostics.spl") ?? ""
expect(content.contains("use app.cli.query_lint.{")).to_equal(true)
expect(content.contains("use app.cli.query_lint_checks.{")).to_equal(false)
expect(content.contains("use app.cli.query_lint_scan.{")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_diagnostics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering query diagnostics helpers, query dispatcher boundaries.
- query diagnostics helpers
- query dispatcher boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75d50c4ff08ac191f2475a744ef8f11e4746f06f30931641c02e64dcf48d2879`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75d50c4ff08ac191f2475a744ef8f11e4746f06f30931641c02e64dcf48d2879`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75d50c4ff08ac191f2475a744ef8f11e4746f06f30931641c02e64dcf48d2879`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/cli/query_diagnostics_spec.spl
mirror: doc/06_spec/unit/app/cli/query_diagnostics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_diagnostics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_diagnostics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_diagnostics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_diagnostics_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits structured error metadata into core related and help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_diagnostics_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts explicit error code before fallback inference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/cli/query_diagnostics_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps lint json collection in the lint orchestrator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

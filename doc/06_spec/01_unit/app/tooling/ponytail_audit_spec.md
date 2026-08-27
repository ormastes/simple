# Ponytail Audit Specification

> Tests covering ponytail audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ponytail Audit Specification

## Scenarios

### ponytail audit

#### renders clean audit output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders clean audit output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders clean audit output")
val path = _write_ponytail_fixture("clean", "fn hello() -> text:\n    \"ok\"\n")
val output = ponytail_audit(path)
expect(output).to_contain("Ponytail Audit")
expect(output).to_contain("status: ok")
expect_absence_marker_hidden(output)
```

</details>

#### flags placeholder and abstraction markers

- flags placeholder and abstraction markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags placeholder and abstraction markers")
val path = _write_ponytail_fixture("smells", "interface FutureThing:\n    pass_todo\n")
val output = ponytail_audit(path)
expect(output).to_contain("status: review")
expect(output).to_contain("placeholder markers:")
expect(output).to_contain("abstraction smells:")
```

</details>

#### returns explicit missing status for absent source

- returns explicit missing status for absent source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns explicit missing status for absent source")
val output = ponytail_audit("build/test/ponytail/missing.spl")
expect(output).to_contain("status: missing")
expect(output).to_contain("reason: source unavailable")
expect_absence_marker_hidden(output)
```

</details>

#### renders simplification report suggestions

- renders simplification report suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders simplification report suggestions")
val path = _write_ponytail_fixture("report", "interface FutureThing:\n    pass_todo\n    # TODO simplify\n")
val output = ponytail_simplification_report(path)
expect(output).to_contain("Ponytail Simplification Report")
expect(output).to_contain("status: review")
expect(output).to_contain("cut placeholder passes:")
expect(output).to_contain("cut speculative abstraction:")
expect(output).to_contain("resolve todo markers:")
expect(output).to_contain("total_suggestions:")
expect_absence_marker_hidden(output)
```

</details>

#### renders clean simplification report without suggestions

- renders clean simplification report without suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders clean simplification report without suggestions")
val path = _write_ponytail_fixture("report_clean", "fn hello() -> text:\n    \"ok\"\n")
val output = ponytail_simplification_report(path)
expect(output).to_contain("status: ok")
expect(output).to_contain("summary: no simplification targets found")
expect(output).to_contain("total_suggestions: 0")
```

</details>

#### renders missing simplification report as explicit absence

- renders missing simplification report as explicit absence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders missing simplification report as explicit absence")
val output = ponytail_simplification_report("build/test/ponytail/report_missing.spl")
expect(output).to_contain("status: missing")
expect(output).to_contain("reason: source unavailable")
expect(output).to_contain("total_suggestions: 0")
expect_absence_marker_hidden(output)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/ponytail_audit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ponytail audit.
- ponytail audit

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

- Canonical SPipe generation for source `225f5bb07dbaf1db73900ff3175e4ceefa76bbbc1e83e6067c1dbd42a4197e76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `225f5bb07dbaf1db73900ff3175e4ceefa76bbbc1e83e6067c1dbd42a4197e76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `225f5bb07dbaf1db73900ff3175e4ceefa76bbbc1e83e6067c1dbd42a4197e76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/tooling/ponytail_audit_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/ponytail_audit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/ponytail_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/ponytail_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/ponytail_audit_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders clean audit output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/ponytail_audit_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags placeholder and abstraction markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/ponytail_audit_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns explicit missing status for absent source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

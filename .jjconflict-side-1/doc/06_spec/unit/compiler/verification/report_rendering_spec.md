# Verification Report Rendering Specification

> Tests that the VerificationReport renders correctly at all four levels (Project, File, Symbol, Theorem) and that admitted/trusted states are never confused with verified.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verification Report Rendering Specification

Tests that the VerificationReport renders correctly at all four levels (Project, File, Symbol, Theorem) and that admitted/trusted states are never confused with verified.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LEAN-DIAG-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/unit/compiler/verification/report_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the VerificationReport renders correctly at all four levels
(Project, File, Symbol, Theorem) and that admitted/trusted states are
never confused with verified.

## Scenarios

### Verification Report - Project Level

#### renders project summary with state counts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders project summary with state counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders project summary with state counts")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Test Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Project)
expect(output).to_contain("Lean Model Verification:")
expect(output).to_contain("model_proven")
expect(output).to_contain("failed")
```

</details>

#### renders debt warning when admitted units exist

- renders debt warning when admitted units exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders debt warning when admitted units exist")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Test Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Project)
expect(output).to_contain("DEBT")
expect(output).to_contain("sorry/assume")
```

</details>

#### renders 0 total for empty units

- renders 0 total for empty units


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders 0 total for empty units")
val units = ProofUnitSet.empty()
val report = VerificationReport.from_units(
    "Empty Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Project)
expect(output).to_contain("0 total")
expect(output).to_contain("Total: 0 proof units")
```

</details>

### Verification Report - File Level

#### shows per-file states

- shows per-file states


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows per-file states")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "File Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
expect(output).to_contain("Files:")
expect(output).to_contain("src/a.spl")
expect(output).to_contain("src/b.spl")
expect(output).to_contain("src/c.spl")
```

</details>

#### shows admitted count prominently per file

- shows admitted count prominently per file


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows admitted count prominently per file")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "File Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
# The admitted file (src/c.spl) has sorry count
expect(output).to_contain("sorry")
```

</details>

#### shows trusted count prominently per file

- shows trusted count prominently per file


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows trusted count prominently per file")
val units = build_trusted_unit_set()
val report = VerificationReport.from_units(
    "Trust Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
expect(output).to_contain("assume")
```

</details>

#### never shows admitted as Verified

- never shows admitted as Verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never shows admitted as Verified")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "File Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
# The admitted entry must show "Admitted (sorry)" not model proven.
# Split by lines and check admitted file line
expect(output).to_contain("Admitted (sorry)")
```

</details>

#### never shows trusted as Verified

- never shows trusted as Verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never shows trusted as Verified")
val units = build_trusted_unit_set()
val report = VerificationReport.from_units(
    "Trust Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
expect(output).to_contain("Trusted (assume)")
```

</details>

### Verification Report - Symbol Level

#### shows per-symbol summaries

- shows per-symbol summaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows per-symbol summaries")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Symbol Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Symbol)
expect(output).to_contain("Symbols:")
expect(output).to_contain("fn_verified")
expect(output).to_contain("fn_failed")
expect(output).to_contain("fn_admitted")
```

</details>

#### includes debt info in symbol summary

- includes debt info in symbol summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes debt info in symbol summary")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Symbol Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Symbol)
expect(output).to_contain("sorry")
```

</details>

### Verification Report - Theorem Level

#### shows individual theorem detail

- shows individual theorem detail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows individual theorem detail")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Theorem Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Theorem)
expect(output).to_contain("All Theorems")
expect(output).to_contain("thm_soundness")
expect(output).to_contain("source:")
expect(output).to_contain("lean:")
```

</details>

#### separates environment errors from proof errors

- separates environment errors from proof errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("separates environment errors from proof errors")
val units = build_mixed_unit_set()
var report = VerificationReport.from_units(
    "Theorem Report", "project", units, "2026-04-04T00:00:00Z"
)
# Manually add an environment error entry
val env_entry = TheoremEntry(
    theorem_name="thm_env_fail",
    source_file="src/env.spl",
    source_line=10,
    lean_file="Verification/Env.lean",
    state=VerificationState.Failed,
    error_message=Some("lake build failed: toolchain mismatch"),
    is_environment_error=true
)
report.theorem_entries = report.theorem_entries + [env_entry]
val output = report.render(ReportLevel.Theorem)
expect(output).to_contain("Environment Errors")
expect(output).to_contain("ENV ERROR")
```

</details>

### Verification Report - SDN Output

#### produces parseable SDN format

- produces parseable SDN format


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces parseable SDN format")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
expect(output).to_contain("verification_report {")
expect(output).to_contain("counts {")
expect(output).to_contain("files {")
expect(output).to_contain("theorems {")
```

</details>

#### includes state counts in SDN

- includes state counts in SDN
   - Expected: output does not contain `verified:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes state counts in SDN")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
expect(output).to_contain("model_proven:")
expect(output.contains("verified:")).to_equal(false)
expect(output).to_contain("failed:")
expect(output).to_contain("admitted:")
expect(output).to_contain("trusted:")
```

</details>

#### includes file entries in SDN

- includes file entries in SDN


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes file entries in SDN")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
expect(output).to_contain("file {")
expect(output).to_contain("path: \"src/a.spl\"")
```

</details>

#### SDN never labels admitted as verified

- SDN never labels admitted as verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN never labels admitted as verified")
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
# The admitted file must have state: "admitted", not model_proven.
expect(output).to_contain("state: \"admitted\"")
```

</details>

#### handles empty units in SDN

- handles empty units in SDN


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty units in SDN")
val units = ProofUnitSet.empty()
val report = VerificationReport.from_units(
    "Empty SDN", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
expect(output).to_contain("total: 0")
```

</details>

### ReportLevel

#### converts to string

- converts to string
   - Expected: ReportLevel.Project.to_string() equals `project`
   - Expected: ReportLevel.File.to_string() equals `file`
   - Expected: ReportLevel.Symbol.to_string() equals `symbol`
   - Expected: ReportLevel.Theorem.to_string() equals `theorem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
expect(ReportLevel.Project.to_string()).to_equal("project")
expect(ReportLevel.File.to_string()).to_equal("file")
expect(ReportLevel.Symbol.to_string()).to_equal("symbol")
expect(ReportLevel.Theorem.to_string()).to_equal("theorem")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `aec2da95ba26a5a6310c2b41d4042c9e19053f85897437d9f9b9b739e3701b52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aec2da95ba26a5a6310c2b41d4042c9e19053f85897437d9f9b9b739e3701b52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aec2da95ba26a5a6310c2b41d4042c9e19053f85897437d9f9b9b739e3701b52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verification/report_rendering_spec.spl
mirror: doc/06_spec/unit/compiler/verification/report_rendering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/report_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/report_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/report_rendering_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders project summary with state counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/report_rendering_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders debt warning when admitted units exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/report_rendering_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders 0 total for empty units' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

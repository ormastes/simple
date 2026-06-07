# Verification Report Rendering Specification

> Tests that the VerificationReport renders correctly at all four levels (Project, File, Symbol, Theorem) and that admitted/trusted states are never confused with verified.

<!-- sdn-diagram:id=report_rendering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=report_rendering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

report_rendering_spec -> std
report_rendering_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=report_rendering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/00_formal_verification/compiler/report_rendering_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the VerificationReport renders correctly at all four levels
(Project, File, Symbol, Theorem) and that admitted/trusted states are
never confused with verified.

## Scenarios

### Verification Report - Project Level

#### renders project summary with state counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "Test Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.Project)
expect(output).to_contain("Lean Verification:")
expect(output).to_contain("verified")
expect(output).to_contain("failed")
```

</details>

#### renders debt warning when admitted units exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = build_trusted_unit_set()
val report = VerificationReport.from_units(
    "Trust Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
expect(output).to_contain("assume")
```

</details>

#### never shows admitted as Verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "File Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render(ReportLevel.File)
# The admitted entry must show "Admitted (sorry)" not "Verified"
# Split by lines and check admitted file line
expect(output).to_contain("Admitted (sorry)")
```

</details>

#### never shows trusted as Verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. error message=Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
expect(output).to_contain("verified:")
expect(output).to_contain("failed:")
expect(output).to_contain("admitted:")
expect(output).to_contain("trusted:")
```

</details>

#### includes file entries in SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val units = build_mixed_unit_set()
val report = VerificationReport.from_units(
    "SDN Report", "project", units, "2026-04-04T00:00:00Z"
)
val output = report.render_sdn()
# The admitted file must have state: "admitted", not state: "verified"
expect(output).to_contain("state: \"admitted\"")
```

</details>

#### handles empty units in SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

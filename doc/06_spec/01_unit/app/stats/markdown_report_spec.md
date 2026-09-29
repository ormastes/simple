# Markdown Report Specification

> Tests covering stats Markdown report.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Report Specification

## Scenarios

### stats Markdown report

#### uses the repository report location by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the repository report location by default
   - Expected: stats_report_path([]) equals `doc/09_report/project_statistics.md`
   - Expected: stats_report_path(["--report=build/custom.md"]) equals `build/custom.md`
   - Expected: stats_report_path(["--report", "build/separate.md"]) equals `build/separate.md`
   - Expected: stats_report_path(["--no-report"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the repository report location by default")
expect(stats_report_path([])).to_equal("doc/09_report/project_statistics.md")
expect(stats_report_path(["--report=build/custom.md"])).to_equal("build/custom.md")
expect(stats_report_path(["--report", "build/separate.md"])).to_equal("build/separate.md")
expect(stats_report_path(["--no-report"])).to_equal("")
```

</details>

#### renders project, language, test, feature, and coverage metrics

- renders project, language, test, feature, and coverage metrics


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders project, language, test, feature, and coverage metrics")
val report = stats_markdown(
    [["app", "2", "20"], ["test", "3", "30"]],
    [["Simple", "5", "50"], ["Rust", "1", "10"], ["C/C headers", "2", "12"]],
    2, 20, 3, 30,
    1, 1, 1, 0,
    4, 2, 8, 1, 3,
    10, 9, 7, 4, 2, 1,
    5, 4
)
expect(report).to_contain("| app | 2 | 20 |")
expect(report).to_contain("| Rust | 1 | 10 |")
expect(report).to_contain("Markdown fenced tests | 2 | 8")
expect(report).to_contain("Source comment SDoctests (`>>>`) | 1 | 3")
expect(report).to_contain("Recorded tests passed | 9 / 10 (90%)")
expect(report).to_contain("Public API documentation | 4 / 5 (80%)")
```

</details>

#### projects one inventory into full, TLDR, and SimpleOS slide Markdown

- projects one inventory into full, TLDR, and SimpleOS slide Markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects one inventory into full, TLDR, and SimpleOS slide Markdown")
val inventory = StatsInventoryV2(
    projects: [StatsProjectRowV2(name: "compiler", total_files: 12, total_sloc: 1200, source_files: 8, source_sloc: 900, test_files: 4, test_sloc: 300)],
    focus_areas: [StatsProjectRowV2(name: "RISC-V", total_files: 3, total_sloc: 250, source_files: 2, source_sloc: 200, test_files: 1, test_sloc: 50)],
    languages: [StatsCountRowV2(name: "Simple", files: 12, sloc: 1200)],
    test_surfaces: [StatsTestSurfaceV2(name: "Unit SSpec", files: 4, runnable_sloc: 300)],
    markdown_files: 25,
    quality: [StatsQualityEvidenceV2(metric: "Duplication", status: "measured", source: "duplicate-check.json", measured_at: "2026-08-13T00:00:00Z", summary: "1.2% duplicated blocks")]
)
val full = stats_markdown_v2(inventory)
expect(full).to_contain("| compiler | 12 | 1200 |")
expect(full).to_contain("| compiler | 8 | 900 | 4 | 300 |")
expect(full).to_contain("Focus Areas (non-additive)")
expect(full).to_contain("| Duplication | measured | duplicate-check.json")

val tldr = stats_tldr_markdown_v2(inventory)
expect(tldr).to_contain("| Owned SLOC | 1200 |")
expect(tldr).to_contain("Runnable test LOC | 300")
expect(tldr).to_contain("Duplication: measured")

val slides = stats_slides_markdown_v2(inventory)
expect(slides).to_start_with("Project Statistics\n@layout: section")
expect(slides).to_contain("@notes: simpleos-default-theme")
expect(slides).to_contain("Risks\n")
expect(slides).to_contain("Methodology\n")
```

</details>

#### renders absent optional quality evidence truthfully

- renders absent optional quality evidence truthfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders absent optional quality evidence truthfully")
val inventory = StatsInventoryV2(
    projects: [], focus_areas: [], languages: [], test_surfaces: [],
    markdown_files: 0, quality: []
)
expect(stats_markdown_v2(inventory)).to_contain("| Quality analysis | unavailable | not requested")
expect(stats_tldr_markdown_v2(inventory)).to_contain("unavailable (not requested)")
expect(stats_slides_markdown_v2(inventory)).to_contain("analysis was not requested")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/markdown_report_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stats Markdown report.
- stats Markdown report

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `dc7545f574d1098845f1b386b9b7d87ba0e65021ae34123d08b7d290b96bfe3e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc7545f574d1098845f1b386b9b7d87ba0e65021ae34123d08b7d290b96bfe3e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc7545f574d1098845f1b386b9b7d87ba0e65021ae34123d08b7d290b96bfe3e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/stats/markdown_report_spec.spl
mirror: doc/06_spec/01_unit/app/stats/markdown_report_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/stats/markdown_report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/stats/markdown_report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/stats/markdown_report_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the repository report location by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/stats/markdown_report_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders project, language, test, feature, and coverage metrics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/stats/markdown_report_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects one inventory into full, TLDR, and SimpleOS slide Markdown' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

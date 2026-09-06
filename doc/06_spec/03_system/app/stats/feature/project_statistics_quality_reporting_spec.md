# Project Statistics Quality Reporting Specification

> Tests covering project statistics and quality reporting, REQ-STAT-001..006: Collect the owned inventory, REQ-STAT-007..008: Review quality evidence, REQ-STAT-009..010: Generate presentation artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Project Statistics Quality Reporting Specification

## Scenarios

### project statistics and quality reporting

### REQ-STAT-001..006: Collect the owned inventory

#### reports disjoint projects, overlapping focus areas, and all test surfaces
### REQ-STAT-007..008: Review quality evidence

#### distinguishes a measured zero from unavailable evidence

- distinguishes a measured zero from unavailable evidence
   - Expected: measured.status equals `measured`
   - Expected: unavailable.status equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distinguishes a measured zero from unavailable evidence")
val measured = classify_quality_evidence("coverage", "coverage.sdn", "summary:\n total_decisions: 0\n covered_decisions: 0\n total_conditions: 0\n covered_conditions: 0", 100, 101, 10)
val unavailable = classify_quality_evidence("coverage", "coverage.sdn", "", 0, 101, 10)
expect(measured.status).to_equal("measured")
expect(unavailable.status).to_equal("unavailable")
```

</details>

### REQ-STAT-009..010: Generate presentation artifacts

#### projects one inventory to JSON, report, TLDR, and native SimpleOS deck

- projects one inventory to JSON, report, TLDR, and native SimpleOS deck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("projects one inventory to JSON, report, TLDR, and native SimpleOS deck")
val base = setup_statistics_fixture()
val quality = StatsQualityEvidenceV2(metric: "coverage", status: "unavailable", source: "coverage.sdn", measured_at: "", summary: "artifact not found")
val inventory = StatsInventoryV2(projects: base.projects, focus_areas: base.focus_areas, languages: base.languages, test_surfaces: base.test_surfaces, markdown_files: base.markdown_files, quality: [quality])
expect(stats_json_v2(inventory)).to_contain("\"schema\":\"simple.stats.v2\"")
expect(stats_markdown_v2(inventory)).to_contain("## Quality Evidence")
expect(stats_tldr_markdown_v2(inventory)).to_contain("Project Statistics — TLDR")
expect(stats_slides_markdown_v2(inventory)).to_contain("@notes: simpleos-default-theme")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering project statistics and quality reporting, REQ-STAT-001..006: Collect the owned inventory, REQ-STAT-007..008: Review quality evidence, REQ-STAT-009..010: Generate presentation artifacts.
- project statistics and quality reporting
- REQ-STAT-001..006: Collect the owned inventory
- REQ-STAT-007..008: Review quality evidence
- REQ-STAT-009..010: Generate presentation artifacts

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

- `REQ-SSPEC-SYSTEM`
- `REQ-STAT-001..006`
- `REQ-STAT-007..008`
- `REQ-STAT-009..010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `acd8ac20471b472791264089640319582e9876e146bccec15354a175a62337ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `acd8ac20471b472791264089640319582e9876e146bccec15354a175a62337ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `acd8ac20471b472791264089640319582e9876e146bccec15354a175a62337ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl
mirror: doc/06_spec/03_system/app/stats/feature/project_statistics_quality_reporting_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/app/stats/feature/project_statistics_quality_reporting_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/stats/feature/project_statistics_quality_reporting_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports disjoint projects, overlapping focus areas, and all test surfaces' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/stats/feature/project_statistics_quality_reporting_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects one inventory to JSON, report, TLDR, and native SimpleOS deck' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

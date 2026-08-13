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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inventory = setup_statistics_fixture()
expect(inventory.projects[0].source_sloc).to_equal(20)
expect(inventory.focus_areas[0].source_sloc).to_equal(12)
expect(inventory.focus_areas[1].source_sloc).to_equal(12)
expect(inventory.markdown_files).to_equal(1)
expect(inventory.test_surfaces[0].runnable_sloc).to_equal(11)
```

</details>

### REQ-STAT-007..008: Review quality evidence

#### distinguishes a measured zero from unavailable evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val measured = classify_quality_evidence("coverage", "coverage.sdn", "summary:\n total_decisions: 0\n covered_decisions: 0\n total_conditions: 0\n covered_conditions: 0", 100, 101, 10)
val unavailable = classify_quality_evidence("coverage", "coverage.sdn", "", 0, 101, 10)
expect(measured.status).to_equal("measured")
expect(unavailable.status).to_equal("unavailable")
```

</details>

### REQ-STAT-009..010: Generate presentation artifacts

#### projects one inventory to JSON, report, TLDR, and native SimpleOS deck

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-08-13 |
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

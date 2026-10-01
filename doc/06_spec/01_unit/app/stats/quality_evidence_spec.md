# Quality Evidence Specification

> Tests covering stats quality evidence adapters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quality Evidence Specification

## Scenarios

### stats quality evidence adapters

#### reports measured zero coverage without fabricating unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports measured zero coverage without fabricating unavailable
   - Expected: row.status equals `measured`
   - Expected: row.measured_at equals `1000`
   - Expected: row.summary equals `decisions 0/0; conditions 0/0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports measured zero coverage without fabricating unavailable")
val content = "summary:\n  total_decisions: 0\n  covered_decisions: 0\n  total_conditions: 0\n  covered_conditions: 0\n"
val row = classify_quality_evidence("coverage", "coverage.sdn", content, 1000, 1100, 200)
expect(row.status).to_equal("measured")
expect(row.measured_at).to_equal("1000")
expect(row.summary).to_equal("decisions 0/0; conditions 0/0")
```

</details>

#### marks old valid duplication evidence stale

- marks old valid duplication evidence stale
   - Expected: row.status equals `stale`
   - Expected: row.summary equals `2 groups; 4 occurrences; 18 duplicated lines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("marks old valid duplication evidence stale")
val content = "metadata:\n  total_groups: 2\n  total_lines: 18\n  total_occurrences: 4\n\nduplicate_groups |group_id, occurrences, lines, impact|\n"
val row = classify_quality_evidence("duplication", "duplicate_db.sdn", content, 100, 1000, 300)
expect(row.status).to_equal("stale")
expect(row.summary).to_equal("2 groups; 4 occurrences; 18 duplicated lines")
```

</details>

#### fails closed for malformed evidence instead of reporting zero or PASS

- fails closed for malformed evidence instead of reporting zero or PASS
   - Expected: row.status equals `unavailable`
   - Expected: row.measured_at equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for malformed evidence instead of reporting zero or PASS")
val row = classify_quality_evidence("coupling", "coupling.json", "{}", 1000, 1001, 300)
expect(row.status).to_equal("unavailable")
expect(row.measured_at).to_equal("")
expect(row.summary).to_contain("missing required coupling evidence fields")
```

</details>

#### projects coupling and cohesion from the retained coupling owner report

- projects coupling and cohesion from the retained coupling owner report
   - Expected: coupling.status equals `measured`
   - Expected: cohesion.status equals `measured`
   - Expected: cohesion.summary equals `LCOM evidence for 1 classes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("projects coupling and cohesion from the retained coupling owner report")
val content = "{\n  \"modules\": [\n    {\"name\": \"a\", \"cbo\": 1},\n    {\"name\": \"b\", \"cbo\": 2}\n  ],\n  \"cycles\": [],\n  \"layer_violations\": [\n    {\"from\": \"a\", \"to\": \"b\"}\n  ],\n  \"lcom\": [\n    {\"class\": \"Thing\", \"lcom4\": 1}\n  ]\n}"
val coupling = classify_quality_evidence("coupling", "coupling.json", content, 1000, 1001, 300)
val cohesion = classify_quality_evidence("cohesion", "coupling.json", content, 1000, 1001, 300)
expect(coupling.status).to_equal("measured")
expect(coupling.summary).to_contain("2 modules; 1 layer violations")
expect(cohesion.status).to_equal("measured")
expect(cohesion.summary).to_equal("LCOM evidence for 1 classes")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/stats/quality_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stats quality evidence adapters.
- stats quality evidence adapters

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc3dc591c4bb9854a4e730d7fe7d739ebf22beda5d8e446537b018c42640e786`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc3dc591c4bb9854a4e730d7fe7d739ebf22beda5d8e446537b018c42640e786`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc3dc591c4bb9854a4e730d7fe7d739ebf22beda5d8e446537b018c42640e786`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/app/stats/quality_evidence_spec.spl
mirror: doc/06_spec/01_unit/app/stats/quality_evidence_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/stats/quality_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/stats/quality_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

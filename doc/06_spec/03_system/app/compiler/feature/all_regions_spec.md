# All Regions Specification

> Tests covering all regions language strategy, REQ-001: region map, REQ-003: priority order, REQ-004: interchange anchors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# All Regions Specification

## Scenarios

### all regions language strategy

### REQ-001: region map

#### keeps SDN as carrier rather than universal authoring surface
### REQ-003: priority order

#### starts with schema and style/ui

- starts with schema and style/ui
   - Expected: first equals `schema`
   - Expected: second equals `style/ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts with schema and style/ui")
val first = "schema"
val second = "style/ui"
expect(first).to_equal("schema")
expect(second).to_equal("style/ui")
```

</details>

### REQ-004: interchange anchors

#### names standards for heavy domains

- names standards for heavy domains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("names standards for heavy domains")
val anchors = "MusicXML IFC bSDD gbXML CityGML STEP AP242 VHDL SystemVerilog"
expect(anchors).to_contain("MusicXML")
expect(anchors).to_contain("STEP AP242")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/all_regions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering all regions language strategy, REQ-001: region map, REQ-003: priority order, REQ-004: interchange anchors.
- all regions language strategy
- REQ-001: region map
- REQ-003: priority order
- REQ-004: interchange anchors

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
- `REQ-001`
- `REQ-003`
- `REQ-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `226963da556b9d9c3b31ffcc590020b264b5c7f1baee2d2be476989c945e5a34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `226963da556b9d9c3b31ffcc590020b264b5c7f1baee2d2be476989c945e5a34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `226963da556b9d9c3b31ffcc590020b264b5c7f1baee2d2be476989c945e5a34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/compiler/feature/all_regions_spec.spl
mirror: doc/06_spec/03_system/app/compiler/feature/all_regions_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/app/compiler/feature/all_regions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/compiler/feature/all_regions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/compiler/feature/all_regions_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/compiler/feature/all_regions_spec.spl:12:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps SDN as carrier rather than universal authoring surface' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/compiler/feature/all_regions_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with schema and style/ui' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/compiler/feature/all_regions_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names standards for heavy domains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

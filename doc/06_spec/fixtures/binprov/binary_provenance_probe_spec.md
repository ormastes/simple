# Binary Provenance Probe Specification

> Tests covering binary provenance probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Binary Provenance Probe Specification

## Scenarios

### binary provenance probe

#### runs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/fixtures/binprov/binary_provenance_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering binary provenance probe.
- binary provenance probe

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

- `REQ-SSPEC-FIXTURES`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `14d096bf8d7af5bcf1517620c05bd190cde3aa6286f62888a839c73fa67f860f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14d096bf8d7af5bcf1517620c05bd190cde3aa6286f62888a839c73fa67f860f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14d096bf8d7af5bcf1517620c05bd190cde3aa6286f62888a839c73fa67f860f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/fixtures/binprov/binary_provenance_probe_spec.spl
mirror: doc/06_spec/fixtures/binprov/binary_provenance_probe_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=90 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/fixtures/binprov/binary_provenance_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/fixtures/binprov/binary_provenance_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/fixtures/binprov/binary_provenance_probe_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/fixtures/binprov/binary_provenance_probe_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/fixtures/binprov/binary_provenance_probe_spec.spl:14:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'runs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

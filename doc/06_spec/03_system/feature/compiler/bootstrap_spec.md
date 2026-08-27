# Direct Bootstrap System

> Tests the direct bootstrap system including stage transitions from Rust seed to self-hosted Simple compiler. Verifies that each bootstrap stage produces a functional compiler capable of compiling the next stage.

<details>
<summary>Full Scenario Manual</summary>

# Direct Bootstrap System

Tests the direct bootstrap system including stage transitions from Rust seed to self-hosted Simple compiler. Verifies that each bootstrap stage produces a functional compiler capable of compiling the next stage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/bootstrap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the direct bootstrap system including stage transitions from Rust seed to
self-hosted Simple compiler. Verifies that each bootstrap stage produces a
functional compiler capable of compiling the next stage.


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4357ef74def60462719399e707ebeb0408aec6cb715ce58e6a0666ea47a68973`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4357ef74def60462719399e707ebeb0408aec6cb715ce58e6a0666ea47a68973`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4357ef74def60462719399e707ebeb0408aec6cb715ce58e6a0666ea47a68973`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/compiler/bootstrap_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/bootstrap_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/03_system/feature/compiler/bootstrap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/bootstrap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/bootstrap_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/compiler/bootstrap_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->

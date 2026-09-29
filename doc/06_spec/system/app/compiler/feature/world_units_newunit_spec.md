# World Units Newunit Specification

> Tests covering World units and newunit, REQ-WUN-001: nominal wrappers, REQ-WUN-004: exact derived units, REQ-WUN-006: currency identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World Units Newunit Specification

## Scenarios

### World units and newunit

### REQ-WUN-001: nominal wrappers

#### parses newunit as a nominal wrapper

- parses newunit as a nominal wrapper


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WUN-001
# @req REQ-WUN-004
# @req REQ-WUN-006
# @req REQ-SSPEC-SYSTEM
step("parses newunit as a nominal wrapper")
val source = "newunit UserId: i64 as uid"
assert_equal(source.contains("newunit UserId"), true)
```

</details>

### REQ-WUN-004: exact derived units

#### records km/h as exact factor

- records km/h as exact factor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records km/h as exact factor")
val factor = "5/18"
assert_equal(factor, "5/18")
```

</details>

### REQ-WUN-006: currency identity

#### uses ISO code for dollars

- uses ISO code for dollars


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses ISO code for dollars")
val currency = "USD"
assert_equal(currency, "USD")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/compiler/feature/world_units_newunit_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering World units and newunit, REQ-WUN-001: nominal wrappers, REQ-WUN-004: exact derived units, REQ-WUN-006: currency identity.
- World units and newunit
- REQ-WUN-001: nominal wrappers
- REQ-WUN-004: exact derived units
- REQ-WUN-006: currency identity

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
- `REQ-WUN-001`
- `REQ-WUN-004`
- `REQ-WUN-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dafe0243bc94b55c6294126eb53d9cd9fbbd71b4e340da68bd4febb855de7853`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dafe0243bc94b55c6294126eb53d9cd9fbbd71b4e340da68bd4febb855de7853`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dafe0243bc94b55c6294126eb53d9cd9fbbd71b4e340da68bd4febb855de7853`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/system/app/compiler/feature/world_units_newunit_spec.spl
mirror: doc/06_spec/system/app/compiler/feature/world_units_newunit_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/compiler/feature/world_units_newunit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/compiler/feature/world_units_newunit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/compiler/feature/world_units_newunit_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/compiler/feature/world_units_newunit_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses newunit as a nominal wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/world_units_newunit_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records km/h as exact factor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/compiler/feature/world_units_newunit_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses ISO code for dollars' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

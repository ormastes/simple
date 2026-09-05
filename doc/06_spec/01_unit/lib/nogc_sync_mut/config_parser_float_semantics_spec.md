# Config Parser Float Semantics Specification

> Tests covering nogc_sync_mut config float semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Parser Float Semantics Specification

## Scenarios

### nogc_sync_mut config float semantics

#### parses valid decimal, negative, and exponent values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### defaults missing, empty, and malformed values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_config_float(section, "missing", 9.5)).to_equal(9.5)
expect(get_config_float(section, "empty", 9.5)).to_equal(9.5)
expect(get_config_float(section, "malformed", 9.5)).to_equal(9.5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_sync_mut config float semantics.
- nogc_sync_mut config float semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `df19b02d8aca1f888d73986bcb45363bca79afd5036482e63e2ba2e43d995887`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `df19b02d8aca1f888d73986bcb45363bca79afd5036482e63e2ba2e43d995887`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `df19b02d8aca1f888d73986bcb45363bca79afd5036482e63e2ba2e43d995887`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses valid decimal, negative, and exponent values' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/config_parser_float_semantics_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defaults missing, empty, and malformed values' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

# Flight Rule Census Scan Specification

> Tests covering flight rule census scan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flight Rule Census Scan Specification

## Scenarios

### flight rule census scan

#### finds zero violations on clean, fully-implemented source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-MC-023
```

</details>

#### catches a planted FLT-IMP-001 violation (placeholder body)

- catches a planted FLT-IMP-001 violation (placeholder body)
   - Expected: count_verdict(sites, "FLT-IMP-001", "violate") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("catches a planted FLT-IMP-001 violation (placeholder body)")
val sites = scan_single_file("fixture/weak.spl", placeholder_weak_comment_source())
expect(count_verdict(sites, "FLT-IMP-001", "violate")).to_equal(1)
```

</details>

#### catches a planted FLT-IMP-002 violation (weak/filler rationale on a placeholder)

- catches a planted FLT-IMP-002 violation (weak/filler rationale on a placeholder)
   - Expected: count_verdict(sites, "FLT-IMP-002", "violate") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("catches a planted FLT-IMP-002 violation (weak/filler rationale on a placeholder)")
val sites = scan_single_file("fixture/weak.spl", placeholder_weak_comment_source())
expect(count_verdict(sites, "FLT-IMP-002", "violate")).to_equal(1)
```

</details>

#### does not flag FLT-IMP-002 when a placeholder carries a substantive rationale

- does not flag FLT-IMP-002 when a placeholder carries a substantive rationale
   - Expected: count_verdict(sites, "FLT-IMP-001", "violate") equals `1`
   - Expected: count_verdict(sites, "FLT-IMP-002", "comply") equals `1`
   - Expected: count_verdict(sites, "FLT-IMP-002", "violate") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag FLT-IMP-002 when a placeholder carries a substantive rationale")
val sites = scan_single_file("fixture/documented.spl", placeholder_good_comment_source())
expect(count_verdict(sites, "FLT-IMP-001", "violate")).to_equal(1)
expect(count_verdict(sites, "FLT-IMP-002", "comply")).to_equal(1)
expect(count_verdict(sites, "FLT-IMP-002", "violate")).to_equal(0)
```

</details>

#### treats a real one-statement body as compliant, not a placeholder

- treats a real one-statement body as compliant, not a placeholder
   - Expected: count_verdict(sites, "FLT-IMP-001", "comply") equals `1`
   - Expected: count_verdict(sites, "FLT-IMP-001", "violate") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats a real one-statement body as compliant, not a placeholder")
val sites = scan_single_file("fixture/real.spl", real_return_source())
expect(count_verdict(sites, "FLT-IMP-001", "comply")).to_equal(1)
expect(count_verdict(sites, "FLT-IMP-001", "violate")).to_equal(0)
```

</details>

#### does not flag a bodiless trait signature as an empty-body violation

- does not flag a bodiless trait signature as an empty-body violation
   - Expected: count_verdict(sites, "FLT-IMP-001", "violate") equals `0`
   - Expected: count_verdict(sites, "FLT-IMP-001", "comply") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag a bodiless trait signature as an empty-body violation")
val sites = scan_single_file("fixture/trait.spl", bodiless_signature_source())
expect(count_verdict(sites, "FLT-IMP-001", "violate")).to_equal(0)
expect(count_verdict(sites, "FLT-IMP-001", "comply")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flight rule census scan.
- flight rule census scan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-MC-023`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f419e7055c53c0ccfbeb966ce6bb1f7d52407f61715820c6e35d05b37e7bfcb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f419e7055c53c0ccfbeb966ce6bb1f7d52407f61715820c6e35d05b37e7bfcb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f419e7055c53c0ccfbeb966ce6bb1f7d52407f61715820c6e35d05b37e7bfcb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/flight_rule_census_scan_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/flight_rule_census_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/flight_rule_census_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl:80:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'finds zero violations on clean, fully-implemented source' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'catches a planted FLT-IMP-001 violation (placeholder body)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'catches a planted FLT-IMP-002 violation (weak/filler rationale on a placeholder)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/flight_rule_census_scan_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag FLT-IMP-002 when a placeholder carries a substantive rationale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

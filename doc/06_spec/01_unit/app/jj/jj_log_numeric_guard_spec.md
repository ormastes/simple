# Jj Log Numeric Guard Specification

> Tests covering jj log numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jj Log Numeric Guard Specification

## Scenarios

### jj log numeric guard

#### defaults malformed limit values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults malformed limit values
   - Expected: parse_log_limit_or_default("notanumber", 25) equals `25`
   - Expected: parse_log_limit_or_default("", 25) equals `25`
   - Expected: parse_log_limit_or_default("   ", 25) equals `25`
   - Expected: parse_log_limit_or_default("-5", 25) equals `25`
   - Expected: parse_log_limit_or_default("12x", 25) equals `25`
   - Expected: parse_log_limit_or_default("40", 25) equals `40`
   - Expected: parse_log_limit_or_default("  7 ", 25) equals `7`
   - Expected: parse_log_limit_or_default("0", 25) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults malformed limit values")
# oracle: malformed, empty, or signed text falls back to the caller default
expect(parse_log_limit_or_default("notanumber", 25)).to_equal(25)
expect(parse_log_limit_or_default("", 25)).to_equal(25)
expect(parse_log_limit_or_default("   ", 25)).to_equal(25)
expect(parse_log_limit_or_default("-5", 25)).to_equal(25)
expect(parse_log_limit_or_default("12x", 25)).to_equal(25)
# oracle: decimal text parses exactly; whitespace is trimmed
expect(parse_log_limit_or_default("40", 25)).to_equal(40)
expect(parse_log_limit_or_default("  7 ", 25)).to_equal(7)
expect(parse_log_limit_or_default("0", 25)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/jj/jj_log_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering jj log numeric guard.
- jj log numeric guard

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2b68b3e615ab7bc4a06678ce9f795c7156209d7ade427b0bceaa2ecf55f3cb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2b68b3e615ab7bc4a06678ce9f795c7156209d7ade427b0bceaa2ecf55f3cb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2b68b3e615ab7bc4a06678ce9f795c7156209d7ade427b0bceaa2ecf55f3cb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/jj/jj_log_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/jj/jj_log_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/jj/jj_log_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/jj/jj_log_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/jj/jj_log_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/jj/jj_log_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed limit values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

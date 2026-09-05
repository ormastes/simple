# Search Limit Numeric Guard Specification

> Tests covering search limit numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Search Limit Numeric Guard Specification

## Scenarios

### search limit numeric guard

#### defaults malformed limit values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults malformed limit values
   - Expected: parse_limit_or_default("42") equals `42`
   - Expected: parse_limit_or_default(" 7 ") equals `7`
   - Expected: parse_limit_or_default("") equals `20`
   - Expected: parse_limit_or_default("   ") equals `20`
   - Expected: parse_limit_or_default("12x") equals `20`
   - Expected: parse_limit_or_default("-5") equals `20`
   - Expected: parse_limit_or_default("0") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults malformed limit values")
# oracle: well-formed limits parse exactly; every malformed shape falls back to the default 20
expect(parse_limit_or_default("42")).to_equal(42)
expect(parse_limit_or_default(" 7 ")).to_equal(7)
expect(parse_limit_or_default("")).to_equal(20)
expect(parse_limit_or_default("   ")).to_equal(20)
expect(parse_limit_or_default("12x")).to_equal(20)
expect(parse_limit_or_default("-5")).to_equal(20)
expect(parse_limit_or_default("0")).to_equal(20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/search/search_limit_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering search limit numeric guard.
- search limit numeric guard

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

- Canonical SPipe generation for source `0e07d5da403bd1a7cbe26ed6a8d6b21eb543fb2042998b9a10d830aa29be1d3b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e07d5da403bd1a7cbe26ed6a8d6b21eb543fb2042998b9a10d830aa29be1d3b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e07d5da403bd1a7cbe26ed6a8d6b21eb543fb2042998b9a10d830aa29be1d3b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/search/search_limit_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/search/search_limit_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/search/search_limit_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/search/search_limit_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/search/search_limit_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/search/search_limit_numeric_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed limit values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

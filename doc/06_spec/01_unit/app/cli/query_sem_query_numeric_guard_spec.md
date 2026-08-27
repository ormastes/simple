# Query Sem Query Numeric Guard Specification

> Tests covering semantic query numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Sem Query Numeric Guard Specification

## Scenarios

### semantic query numeric guard

#### rejects invalid integer predicates without direct parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects invalid integer predicates without direct parsing
   - Expected: _compare_int(5, "=", "5") is true
   - Expected: _compare_int(5, "=", "6") is false
   - Expected: _compare_int(5, "!=", "6") is true
   - Expected: _compare_int(5, ">", "3") is true
   - Expected: _compare_int(5, ">", "5") is false
   - Expected: _compare_int(5, "<", "9") is true
   - Expected: _compare_int(5, ">=", "5") is true
   - Expected: _compare_int(5, "<=", "4") is false
   - Expected: _compare_int(5, "=", "abc") is false
   - Expected: _compare_int(5, "~", "5") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects invalid integer predicates without direct parsing")
# oracle: every supported operator compares the parsed expected bound exactly
expect(_compare_int(5, "=", "5")).to_equal(true)
expect(_compare_int(5, "=", "6")).to_equal(false)
expect(_compare_int(5, "!=", "6")).to_equal(true)
expect(_compare_int(5, ">", "3")).to_equal(true)
expect(_compare_int(5, ">", "5")).to_equal(false)
expect(_compare_int(5, "<", "9")).to_equal(true)
expect(_compare_int(5, ">=", "5")).to_equal(true)
expect(_compare_int(5, "<=", "4")).to_equal(false)
# oracle: an unparsable expected bound must reject the predicate (false).
# (Non-numeric bounds with digit prefixes diverge between the JIT and
# interpreter `to_int`; plain non-numeric text is stable on both.)
expect(_compare_int(5, "=", "abc")).to_equal(false)
# oracle: an unsupported operator is never true
expect(_compare_int(5, "~", "5")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/query_sem_query_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering semantic query numeric guard.
- semantic query numeric guard

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

- Canonical SPipe generation for source `b1f20b2631e711b820eb26a9b87cc488b5af9cb9ad4b0097e2613d10372f0068`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1f20b2631e711b820eb26a9b87cc488b5af9cb9ad4b0097e2613d10372f0068`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1f20b2631e711b820eb26a9b87cc488b5af9cb9ad4b0097e2613d10372f0068`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/app/cli/query_sem_query_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/cli/query_sem_query_numeric_guard_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/query_sem_query_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/query_sem_query_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/query_sem_query_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid integer predicates without direct parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

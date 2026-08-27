# Expect Bool Specification

> Tests covering Concise boolean expectations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Expect Bool Specification

## Scenarios

### Concise boolean expectations

#### accepts bare true expectations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts bare true expectations


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("accepts bare true expectations")
assert_true(3 > 2)
```

</details>

#### accepts bare false expectations through expect_not

- accepts bare false expectations through expect_not


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("accepts bare false expectations through expect_not")
expect_not(3 < 2)
```

</details>

#### keeps non-boolean zero equality as a chained matcher

- keeps non-boolean zero equality as a chained matcher
   - Expected: 7 - 7 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SPEC
step("keeps non-boolean zero equality as a chained matcher")
# oracle: 7 - 7 is computed at runtime, so the matcher sees a real value, not a literal
expect(7 - 7).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/expect_bool_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Concise boolean expectations.
- Concise boolean expectations

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

- `REQ-SSPEC-SPEC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f4a7bb8b23a23b4c7d720f417a6193df0557fa4a7ba1a25bb69aee0b9204d4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f4a7bb8b23a23b4c7d720f417a6193df0557fa4a7ba1a25bb69aee0b9204d4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f4a7bb8b23a23b4c7d720f417a6193df0557fa4a7ba1a25bb69aee0b9204d4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/spec/expect_bool_spec.spl
mirror: doc/06_spec/01_unit/spec/expect_bool_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/spec/expect_bool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/spec/expect_bool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/spec/expect_bool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/spec/expect_bool_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bare true expectations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/spec/expect_bool_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bare false expectations through expect_not' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/spec/expect_bool_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps non-boolean zero equality as a chained matcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

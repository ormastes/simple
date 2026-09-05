# Bdd Eq Chained Matcher Provisional Specification

> Tests covering expect() Eq/NotEq comparison-form defers to a chained matcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bdd Eq Chained Matcher Provisional Specification

## Scenarios

### expect() Eq/NotEq comparison-form defers to a chained matcher

#### chained to_be(false) passes when the equality comparison is false

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- chained to_be(false) passes when the equality comparison is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained to_be(false) passes when the equality comparison is false")
expect(1 == 2).to_be(false)
```

</details>

#### chained to_be(true) passes when the equality comparison is true

- chained to_be(true) passes when the equality comparison is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained to_be(true) passes when the equality comparison is true")
expect(1 == 1).to_be(true)
```

</details>

#### chained to_be(false) passes when the inequality comparison is false

- chained to_be(false) passes when the inequality comparison is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained to_be(false) passes when the inequality comparison is false")
expect(1 != 1).to_be(false)
```

</details>

#### chained to_be(true) passes when the inequality comparison is true

- chained to_be(true) passes when the inequality comparison is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained to_be(true) passes when the inequality comparison is true")
expect(1 != 2).to_be(true)
```

</details>

#### chained to_equal(false) passes on a text mismatch comparison

- chained to_equal(false) passes on a text mismatch comparison
   - Expected: "a" == "b" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained to_equal(false) passes on a text mismatch comparison")
expect("a" == "b").to_equal(false)
```

</details>

#### bare equality mismatch deliberate-fail RED

- bare equality mismatch deliberate-fail RED


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare equality mismatch deliberate-fail RED")
expect 1 == 2
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering expect() Eq/NotEq comparison-form defers to a chained matcher.
- expect() Eq/NotEq comparison-form defers to a chained matcher

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c4df338a7d26c5f11aa4abd12508b568169c22b9b6c8cad345fcc78ad48ff8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c4df338a7d26c5f11aa4abd12508b568169c22b9b6c8cad345fcc78ad48ff8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c4df338a7d26c5f11aa4abd12508b568169c22b9b6c8cad345fcc78ad48ff8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl
mirror: doc/06_spec/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chained to_be(false) passes when the equality comparison is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chained to_be(true) passes when the equality comparison is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bdd_eq_chained_matcher_provisional_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chained to_be(false) passes when the inequality comparison is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

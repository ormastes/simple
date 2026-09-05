# Match Arm Early Return Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Arm Early Return Specification

## Scenarios

#### or-pattern first variant: explicit return inside if propagates

- or-pattern first variant: explicit return inside if propagates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern first variant: explicit return inside if propagates")
assert_equal(or_pattern_if_return(Dir.North), 1)
```

</details>

#### or-pattern second variant: explicit return inside if propagates

- or-pattern second variant: explicit return inside if propagates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern second variant: explicit return inside if propagates")
assert_equal(or_pattern_if_return(Dir.South), 1)
```

</details>

#### or-pattern: non-matching arm falls through to post-match return

- or-pattern: non-matching arm falls through to post-match return


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or-pattern: non-matching arm falls through to post-match return")
assert_equal(or_pattern_if_return(Dir.East), 0)
```

</details>

#### single-pattern: explicit return inside if propagates

- single-pattern: explicit return inside if propagates


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single-pattern: explicit return inside if propagates")
assert_equal(single_pattern_if_return(Dir.North), 1)
```

</details>

#### single-pattern: non-matching falls through

- single-pattern: non-matching falls through


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single-pattern: non-matching falls through")
assert_equal(single_pattern_if_return(Dir.South), 0)
```

</details>

#### arm value with no early return still works correctly

- arm value with no early return still works correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm value with no early return still works correctly")
assert_equal(arm_value_no_return(Dir.North), 42)
assert_equal(arm_value_no_return(Dir.East), 0)
```

</details>

#### false if-condition: arm does not return, falls through

- false if-condition: arm does not return, falls through


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false if-condition: arm does not return, falls through")
assert_equal(false_cond_fallthrough(Dir.North), 0)
```

</details>

#### nested match as last statement: return propagates

- nested match as last statement: return propagates


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested match as last statement: return propagates")
assert_equal(nested_match_return(Dir.North), 10)
assert_equal(nested_match_return(Dir.South), 20)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c1704591cb217f1a702177176941b5811099a313550443d5a582e86ce688eee8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1704591cb217f1a702177176941b5811099a313550443d5a582e86ce688eee8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1704591cb217f1a702177176941b5811099a313550443d5a582e86ce688eee8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/match_arm_early_return_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/match_arm_early_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/match_arm_early_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'or-pattern first variant: explicit return inside if propagates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'or-pattern second variant: explicit return inside if propagates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/match_arm_early_return_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'or-pattern: non-matching arm falls through to post-match return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

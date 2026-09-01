# Ternary Expression Specification

> Tests covering JS subset parser conditional expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ternary Expression Specification

## Scenarios

### JS subset parser conditional expressions

#### evaluates a false-branch ternary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates a false-branch ternary
   - Expected: eval_str("var x = 5 < 2 ? 1 : 2; x") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates a false-branch ternary")
expect(eval_str("var x = 5 < 2 ? 1 : 2; x")).to_equal("2")
```

</details>

#### evaluates a true-branch ternary

- evaluates a true-branch ternary
   - Expected: eval_str("var x = 2 < 5 ? 1 : 2; x") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("evaluates a true-branch ternary")
expect(eval_str("var x = 2 < 5 ? 1 : 2; x")).to_equal("1")
```

</details>

#### gives the ternary lower precedence than arithmetic

- gives the ternary lower precedence than arithmetic
   - Expected: eval_str("var x = 1 + 1 ? 10 + 1 : 20 + 2; x") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives the ternary lower precedence than arithmetic")
expect(eval_str("var x = 1 + 1 ? 10 + 1 : 20 + 2; x")).to_equal("11")
```

</details>

#### handles a nested ternary in the alternate position

- handles a nested ternary in the alternate position
   - Expected: eval_str("var x = 0 ? 1 : 0 ? 2 : 3; x") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a nested ternary in the alternate position")
expect(eval_str("var x = 0 ? 1 : 0 ? 2 : 3; x")).to_equal("3")
```

</details>

#### handles a nested ternary in the consequent position

- handles a nested ternary in the consequent position
   - Expected: eval_str("var x = 1 ? 0 ? 7 : 8 : 9; x") equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a nested ternary in the consequent position")
expect(eval_str("var x = 1 ? 0 ? 7 : 8 : 9; x")).to_equal("8")
```

</details>

#### does not mistake optional chaining or nullish coalescing for a ternary

- does not mistake optional chaining or nullish coalescing for a ternary
   - Expected: eval_str("var x = null ?? 5; x") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mistake optional chaining or nullish coalescing for a ternary")
expect(eval_str("var x = null ?? 5; x")).to_equal("5")
```

</details>

#### still evaluates a statement after a construct-closing brace

- still evaluates a statement after a construct-closing brace
   - Expected: eval_str("function f(x) { return x + 1 } f(3)") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still evaluates a statement after a construct-closing brace")
expect(eval_str("function f(x) { return x + 1 } f(3)")).to_equal("4")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/js/ternary_expression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS subset parser conditional expressions.
- JS subset parser conditional expressions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `71efe094f26d0fde86f1648f3023da9c60f3d01d6148eedfebcf2c8a6e0f2427`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71efe094f26d0fde86f1648f3023da9c60f3d01d6148eedfebcf2c8a6e0f2427`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71efe094f26d0fde86f1648f3023da9c60f3d01d6148eedfebcf2c8a6e0f2427`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/js/ternary_expression_spec.spl
mirror: doc/06_spec/01_unit/lib/js/ternary_expression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/js/ternary_expression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/js/ternary_expression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/js/ternary_expression_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates a false-branch ternary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/ternary_expression_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates a true-branch ternary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/js/ternary_expression_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives the ternary lower precedence than arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

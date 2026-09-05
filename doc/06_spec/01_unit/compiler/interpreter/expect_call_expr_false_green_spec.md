# expect(<call expr>) False-Green Regression

> Regression test for `doc/08_tracking/bug/expect_call_expr_hollow_false_green_2026-06-10.md`: `expect(<function call expr>)` with no `.to_*()` chain silently passed regardless of the call result in interpreter mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect(<call expr>) False-Green Regression

Regression test for `doc/08_tracking/bug/expect_call_expr_hollow_false_green_2026-06-10.md`: `expect(<function call expr>)` with no `.to_*()` chain silently passed regardless of the call result in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BDD-EXPECT-CALL-EXPR |
| Category | Interpreter / Spec Runner |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for
`doc/08_tracking/bug/expect_call_expr_hollow_false_green_2026-06-10.md`:
`expect(<function call expr>)` with no `.to_*()` chain silently passed
regardless of the call result in interpreter mode.

Root cause: `interpreter_call/bdd.rs` `"expect"` handler evaluated the call
result but only checked truthiness for `Expr::Binary` nodes.  For
`Expr::Call` / `Expr::MethodCall` nodes the value was returned unchecked.

Fix: the handler now checks truthiness for `Expr::Call` and `Expr::MethodCall`
nodes and sets `BDD_EXPECT_FAILED` if the result is falsy.  A downstream
`.to_*()` chain is unaffected because the chain always overwrites
`BDD_EXPECT_FAILED` with its own result.

These tests verify the PASSING side (true call results remain green) and use
`.to_equal()` chains to verify results where we need the false side confirmed
structurally (the false side is documented manually in the bug doc; a
meta-runner approach would require a second interpreter invocation that is out
of scope for a unit spec).

## Scenarios

### expect(<call expr>) truthiness — interpreter regression

#### passes when call returns true (chain form — baseline)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes when call returns true (chain form — baseline)
   - Expected: always_true() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when call returns true (chain form — baseline)")
expect(always_true()).to_equal(true)
```

</details>

#### passes when call returns false checked with chain form

- passes when call returns false checked with chain form
   - Expected: always_false() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when call returns false checked with chain form")
expect(always_false()).to_equal(false)
```

</details>

#### passes when call returns non-bool truthy value with chain

- passes when call returns non-bool truthy value with chain
   - Expected: add_one(41) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when call returns non-bool truthy value with chain")
expect(add_one(41)).to_equal(42)
```

</details>

#### bare expect(truthy_call()) is now checked and passes

- bare expect(truthy_call()) is now checked and passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bare expect(truthy_call()) is now checked and passes")
# After the fix, expect(<call>) checks truthiness.
# always_true() returns true → truthy → no failure flagged.
expect(always_true())
```

</details>

#### bare expect(truthy_call()) with explicit chain still passes

- bare expect(truthy_call()) with explicit chain still passes
   - Expected: always_true() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bare expect(truthy_call()) with explicit chain still passes")
expect(always_true()).to_equal(true)
```

</details>

#### chained expect(false_call()).to_equal(false) still passes after fix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("chained expect(false_call()).to_equal(false) still passes after fix")
# The fix only pre-checks before chain; chain overwrites BDD_EXPECT_FAILED.
expect(always_false()).to_equal(false)
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50bf07307a88f7e105a3b131a1ee4a375d3e457b61025b1f4341305dd0c886b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50bf07307a88f7e105a3b131a1ee4a375d3e457b61025b1f4341305dd0c886b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50bf07307a88f7e105a3b131a1ee4a375d3e457b61025b1f4341305dd0c886b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when call returns true (chain form — baseline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when call returns false checked with chain form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when call returns non-bool truthy value with chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

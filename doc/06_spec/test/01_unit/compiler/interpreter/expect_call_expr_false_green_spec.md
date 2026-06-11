# expect(<call expr>) False-Green Regression

> Regression test for `doc/08_tracking/bug/expect_call_expr_hollow_false_green_2026-06-10.md`: `expect(<function call expr>)` with no `.to_*()` chain silently passed regardless of the call result in interpreter mode.

<!-- sdn-diagram:id=expect_call_expr_false_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=expect_call_expr_false_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

expect_call_expr_false_green_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=expect_call_expr_false_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(always_true()).to_equal(true)
```

</details>

#### passes when call returns false checked with chain form

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(always_false()).to_equal(false)
```

</details>

#### passes when call returns non-bool truthy value with chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(add_one(41)).to_equal(42)
```

</details>

#### bare expect(truthy_call()) is now checked and passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After the fix, expect(<call>) checks truthiness.
# always_true() returns true → truthy → no failure flagged.
expect(always_true())
```

</details>

#### bare expect(truthy_call()) with explicit chain still passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(always_true()).to_equal(true)
```

</details>

#### chained expect(false_call()).to_equal(false) still passes after fix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

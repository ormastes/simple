# Parser: trailing-operator line continuation at the SAME indentation

> A line that ENDS in a binary operator cannot form a complete expression, so the next physical line must be layout-neutral: no INDENT/DEDENT is emitted and the right-hand side continues there. Crucially the continuation line may sit at the **same** indentation as the head line — an extra continuation indent must not be required.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: trailing-operator line continuation at the SAME indentation

A line that ENDS in a binary operator cannot form a complete expression, so the next physical line must be layout-neutral: no INDENT/DEDENT is emitted and the right-hand side continues there. Crucially the continuation line may sit at the **same** indentation as the head line — an extra continuation indent must not be required.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A line that ENDS in a binary operator cannot form a complete expression, so the
next physical line must be layout-neutral: no INDENT/DEDENT is emitted and the
right-hand side continues there. Crucially the continuation line may sit at the
**same** indentation as the head line — an extra continuation indent must not be
required.

```simple
use std.spec.step

val a = 1 +
2
```

The lexer-side predicate driving this is `token_requires_rhs`
(`src/compiler/10.frontend/core/tokens.spl`), shared by `CoreLexer` and the
legacy scanner. TODO-DB row 561.

## What is deliberately NOT a continuation

`token_requires_rhs` excludes open-ended `..` and the unary/postfix `not` / `!`
forms, and a line that already ends in a complete value never absorbs the line
below it. `same_indent_not_folded` pins that second half: folding it would turn
`a` into `a - 1`.

## Relationship to the leading-operator form

The mirror-image feature — an operator at the START of the continuation line —
is covered by `parser_leading_operator_continuation_spec.spl`. Both must hold;
this file only exercises the trailing form at same indentation.

## Scenarios

### trailing-operator line continuation at the same indentation

#### continues arithmetic operators onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### continues and/or onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_and(true, false), false)
assert_equal(trail_and(true, true), true)
assert_equal(trail_or(true, false), true)
assert_equal(trail_or(false, false), false)
```

</details>

#### continues comparison and equality operators onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_eq(2, 2), true)
assert_equal(trail_eq(2, 3), false)
assert_equal(trail_lt(1, 2), true)
assert_equal(trail_lt(2, 1), false)
```

</details>

#### continues bitwise operators onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_bit_or(4, 1), 5)
assert_equal(trail_bit_and(6, 3), 2)
```

</details>

#### absorbs every line of a chain spanning more than two lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_chain_four(1, 2, 3, 4), 10)
assert_equal(trail_chain_logical(true, false, false), false)
assert_equal(trail_chain_logical(false, false, true), true)
```

</details>

#### preserves operator precedence across the folded lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_chain_precedence(10, 3, 2), 4)
```

</details>

#### continues in return, reassignment and condition positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(trail_in_return("boom", "x"), "boom reason=x")
assert_equal(trail_in_reassign(5), 10)
assert_equal(trail_in_if_condition(2, 1), 1)
assert_equal(trail_in_if_condition(1, 2), 0)
```

</details>

#### does not fold a same-indent line that follows a complete expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(same_indent_not_folded(7), 7)
assert_equal(dedented_implicit_return(3), -1)
```

</details>

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

- Canonical SPipe generation for source `b3b4f6c752c2bb463640b2eb560c13dce5e17c783c5ce01841a83df2cac05c86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b3b4f6c752c2bb463640b2eb560c13dce5e17c783c5ce01841a83df2cac05c86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b3b4f6c752c2bb463640b2eb560c13dce5e17c783c5ce01841a83df2cac05c86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_trailing_operator_continuation_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_trailing_operator_continuation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_trailing_operator_continuation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl:175:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues arithmetic operators onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl:184:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues and/or onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl:190:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues comparison and equality operators onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_trailing_operator_continuation_spec.spl:196:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues bitwise operators onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

# Parser: newline continuation after a plain `=` and after an `elif` trailing operator

> Two line-continuation shapes used to be rejected while their near-neighbours parsed, which is what makes them easy to reintroduce:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: newline continuation after a plain `=` and after an `elif` trailing operator

Two line-continuation shapes used to be rejected while their near-neighbours parsed, which is what makes them easy to reintroduce:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / line continuation |
| Status | Active |
| Source | `test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Two line-continuation shapes used to be rejected while their near-neighbours
parsed, which is what makes them easy to reintroduce:

1. **Assignment-statement RHS.** `val x =` NEWLINE `expr` parsed, but the plain
   assignment `x =` NEWLINE `expr` did not — the assign-op consumer called a
   fresh top-level expression parser, so the Newline arrived before any
   continuation handling ran. Same for `self.f =` and for every compound
   assign (`+= -= *= /= %=`).
2. **`elif` condition with a trailing operator.** `if a and` NEWLINE `b:`
   parsed, but the identical `elif a and` NEWLINE `b:` did not: the
   `elif` / `else if` paths lacked the save-before / drain-after
   `deferred_dedent_count` handling that the primary `if` path applied around
   its block, so a stray Dedent leaked into the token stream. Both the *deep*
   (continuation column > body column) and *shallow* shapes are covered.

A parse error means this file does not load at all, so **the declarations
below are themselves the grammar coverage** — every `fn` here is written in
the shape being pinned. The `it` blocks assert the continued expressions still
*evaluate* correctly, which is what a silent mis-association would break.

## Syntax

```simple
c =
    a + 1          # plain assignment, RHS on the next line

elif a and
     b:            # elif condition continued after a trailing operator
```

## Scenarios

### assignment-statement RHS newline continuation

#### continues a plain local assignment onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### continues a field assignment onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(assign_field_continuation(21), 42)
```

</details>

#### continues compound assignments onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(assign_compound_continuation(1), 202)
```

</details>

#### keeps the val-declaration control parsing and evaluating

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(val_decl_continuation(), 42)
```

</details>

#### parses and runs the statement after a continued assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(assign_continuation_then_sibling(41), 420)
```

</details>

### elif condition trailing-operator continuation

#### takes the deep-shape elif branch when its condition holds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(elif_deep_continuation(5, 2), 2)
```

</details>

#### falls through the deep-shape elif when its condition fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(elif_deep_continuation(2, 5), 3)
```

</details>

#### takes the shallow-shape elif branch when its condition holds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(elif_shallow_continuation(7, 7), 2)
```

</details>

#### falls through the shallow-shape elif when its condition fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(elif_shallow_continuation(7, 8), 3)
```

</details>

#### evaluates a continued `or` elif and a following continued `and` elif

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(elif_logical_continuation(true, false), 2)
assert_equal(elif_logical_continuation(false, false), 4)
```

</details>

#### continues an `else if` condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(else_if_continuation(5, 2), 2)
assert_equal(else_if_continuation(2, 5), 3)
```

</details>

#### evaluates the real-world dispatch condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(dispatch_continuation("click", "form-reset"), 2)
assert_equal(dispatch_continuation("click", "submit"), 3)
```

</details>

#### continues a while condition and its body assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(while_continuation(4), 4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `dd004757ae944c969266d51eb1024053994d5d18de24f996dc2dfe0803f2171b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd004757ae944c969266d51eb1024053994d5d18de24f996dc2dfe0803f2171b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd004757ae944c969266d51eb1024053994d5d18de24f996dc2dfe0803f2171b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_line_continuation_assign_elif_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_line_continuation_assign_elif_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_line_continuation_assign_elif_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl:159:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues a plain local assignment onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl:164:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues a field assignment onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl:167:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues compound assignments onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl:170:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps the val-declaration control parsing and evaluating' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

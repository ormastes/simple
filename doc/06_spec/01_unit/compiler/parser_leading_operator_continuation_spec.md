# Parser: leading-operator line continuation

> An expression continued onto the next line with the operator at the START of the continuation line did not parse in the self-hosted frontend. The whole file was rejected with a location-less `error[PARSE001]: Source did not parse`, so a single such line made every importer of the module unbuildable. That is what took the frozen contract `src/lib/common/ui/gpu_web_capacity_manifest.spl` off the table for the DrawIR v3 lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: leading-operator line continuation

An expression continued onto the next line with the operator at the START of the continuation line did not parse in the self-hosted frontend. The whole file was rejected with a location-less `error[PARSE001]: Source did not parse`, so a single such line made every importer of the module unbuildable. That is what took the frozen contract `src/lib/common/ui/gpu_web_capacity_manifest.spl` off the table for the DrawIR v3 lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / Self-hosted frontend parity |
| Status | Active |
| Source | `test/01_unit/compiler/parser_leading_operator_continuation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

An expression continued onto the next line with the operator at the START of
the continuation line did not parse in the self-hosted frontend. The whole file
was rejected with a location-less `error[PARSE001]: Source did not parse`, so a
single such line made every importer of the module unbuildable. That is what
took the frozen contract `src/lib/common/ui/gpu_web_capacity_manifest.spl` off
the table for the DrawIR v3 lane.

The TRAILING form (`a +` then the next line) already worked: `token_requires_rhs`
suppresses the newline after an operator that still needs a right-hand side.
The LEADING form is its mirror and had no rule at all — only leading `.` and `|`
were continued. `023a60a05aa` fixed the trailing form for comparison and
equality; this covers the leading form for the binary-operator family.

A parse error means this file will not load, so the declarations below are
themselves the grammar coverage. The `it` blocks additionally assert that the
continued expression *evaluates* as one expression rather than being silently
truncated at the newline.

## Two shapes that must NOT be treated as continuations

Both are exercised below as negative coverage, because folding either one into
the previous line silently miscompiles working code:

1. A block body that legitimately begins with a unary operator — `if c:` then
   an indented `-1`. Guarded by requiring the previous token to be able to END
   an expression (`token_can_end_expr`).
2. An implicit return that DEDENTS out of a loop body — `i = i + 1` then, one
   level out, `-1`. This is the live shape in
   `src/runtime/simple_core/core_string.spl`, `core_array.spl` and
   `core_process.spl`. Guarded by requiring the continuation line to be
   indented strictly deeper than the current logical line.

## Coverage boundary — narrowed 2026-08-01, the seed has caught up

This spec previously withheld the comparison/equality/membership/coalesce
family (`== != < > <= >= is in ??`) and the condition position,
because the Rust bootstrap seed rejected them with
`Unexpected token: expected Colon, found Newline` and the seed is what executes
specs. `75f3da617b3` closed that gap in the three hand-written productions that
never inherited the `parse_binary_*!` macros' leading-continuation arm
(`parse_equality`, `parse_comparison`, and the `DoubleQuestion` postfix arm).
Those forms are now asserted below.

Measured on the seed rebuilt from `f93c9b2623` (sha256 `6f2f872e9bf2…`): every
form asserted below is a parse error on the previous seed
(`simple_seed.rollback2-jul30-workingcopy-2026-08-01.bak`, sha `af796ec5…`),
which already passed the TRAILING forms — so these assertions are RED against
that binary and are not vacuous.

What still cannot be asserted at the language level, and why:

1. **Shapes that must NOT parse** — the same-indent `a` / `< b` non-glue case,
   and the deliberate-syntax-error fixtures. A `.spl` spec cannot contain source
   that fails to parse, because the parse error takes the whole file down rather
   than failing one `it`. These stay in the parser-unit gate
   `src/compiler_rust/parser/tests/leading_comparison_continuation.rs`
   (`same_indent_leading_comparison_is_not_glued`,
   `deliberate_syntax_error_fixture_still_fails`). Both were verified to still
   REJECT on the current seed as well as the pre-fix one — the change is
   additive, not a general loosening.
2. **AST-shape assertions** — that a leading `<` builds an `Lt` node rather than
   merely parsing — are structural and also live in that Rust gate. Here the
   equivalent non-vacuity evidence is behavioural: each `it` below asserts the
   continued expression *evaluates* as one joined expression.

3. **The `while` condition position** — see the separate defect below. `if` and
   `elif` are asserted; `while` is withheld, and unlike the boundary this spec
   just removed, that withholding is backed by a reproducer rather than an
   assumption.

There is deliberately no assertion about an `if`/`elif` "indent boundary". The
boundary recorded in older notes was an artifact of the stale seed; at tip the
leading continuation parses in both `if` and `elif` conditions.

## Blocked: leading continuation in a `while` condition (found 2026-08-01)

A leading `<` continuation in a `while` HEADER parses and evaluates correctly on
its own — but when the same module also declares a function whose `if`/`else`
arms begin with a unary minus, the module fails to load with NO diagnostic at
all: the runner reports only `test-runner: no examples executed`. Deterministic,
3/3, on the `f93c9b2623` seed. Minimal reproducer — these two declarations plus
any `describe` are sufficient:

```simple
use std.spec.step

fn lead_while_cond(n: i64) -> i64:
    var i = 0
    var c = 0
    while i
        < n:
        i = i + 1
        c = c + 2
    return c

fn block_body_starts_with_minus(c: bool) -> i64:
    if c:
        -1
    else:
        -2
```

`block_body_starts_with_minus` is the guard-1 negative control this spec already
carries, so the `while` case cannot be added here until that is fixed. Asserting
it would take the whole file down and destroy the 14 assertions below rather
than fail one `it`. Tracked in the bug doc.

## Known-unrelated defect: the `in` operator

`a in b` evaluates to `false` for a present member on the current seed
interpreter — in the ONE-LINE, TRAILING and LEADING forms alike. That is a
pre-existing `in`-operator defect with nothing to do with line continuation, so
asserting membership truth here would go red for an unrelated reason. Instead
the leading form is asserted to agree with the one-line form, which is exactly
the continuation property this spec owns. Tracked in the bug doc.

## Syntax

```simple
val er = 1.0
    + r
    + r2 / 2.0
```

## Scenarios

### leading-operator line continuation

#### continues after postfix optional presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### continues arithmetic operators onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_plus(1, 2), 3)
assert_equal(lead_minus(5, 2), 3)
assert_equal(lead_star(3, 4), 12)
assert_equal(lead_slash(8, 2), 4)
assert_equal(lead_percent(9, 4), 1)
```

</details>

#### continues and/or onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_and(true, false), false)
assert_equal(lead_or(true, false), true)
```

</details>

#### continues comparison and equality operators onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both truth values per operator: a form that always returned the same
# constant would pass a one-sided check while being truncated.
assert_equal(lead_eq(2, 2), true)
assert_equal(lead_eq(2, 3), false)
assert_equal(lead_ne(2, 3), true)
assert_equal(lead_ne(2, 2), false)
assert_equal(lead_lt(1, 2), true)
assert_equal(lead_lt(2, 1), false)
assert_equal(lead_gt(5, 2), true)
assert_equal(lead_gt(2, 5), false)
assert_equal(lead_le(2, 2), true)
assert_equal(lead_le(3, 2), false)
assert_equal(lead_ge(3, 2), true)
assert_equal(lead_ge(1, 2), false)
```

</details>

#### continues the identity operator onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_is(2, 2), true)
assert_equal(lead_is(2, 3), false)
```

</details>

#### continues the membership operator identically to the one-line form

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parity, not membership truth - see the docstring: `in` is broken
# independently of line continuation on the seed interpreter.
assert_equal(lead_in(2, [1, 2, 3]), oneline_in(2, [1, 2, 3]))
assert_equal(lead_in(9, [1, 2, 3]), oneline_in(9, [1, 2, 3]))
```

</details>

#### continues the nil-coalesce operator onto the next line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_coalesce(nil, 7), 7)
assert_equal(lead_coalesce(4, 7), 4)
```

</details>

#### continues a leading operator in an if condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_if_cond(5, 2), 1)
assert_equal(lead_if_cond(1, 2), 2)
assert_equal(lead_if_eq_cond(2, 2), 1)
assert_equal(lead_if_eq_cond(1, 2), 2)
```

</details>

#### continues a leading operator in an elif condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_elif_cond(5, 2), 1)
assert_equal(lead_elif_cond(2, 2), 0)
assert_equal(lead_elif_cond(1, 2), -1)
```

</details>

#### continues a return expression - the frozen-contract shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_in_return("bound", "why"), "bound reason=why")
```

</details>

#### continues var bindings and plain reassignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_in_var(1), 2)
assert_equal(lead_in_reassign(1), 6)
```

</details>

#### absorbs every line of a multi-line continuation, not just the first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_multi_line(10), 16)
```

</details>

#### keeps bracketed and trailing-operator forms working

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(lead_in_call_arg(1), 202)
assert_equal(lead_in_list_elem(1), 2)
assert_equal(trailing_operator_form("bound", "why"), "bound reason=why")
```

</details>

#### does not fold a block body that begins with a unary operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(block_body_starts_with_minus(true), -1)
assert_equal(block_body_starts_with_minus(false), -2)
```

</details>

<details>
<summary>Advanced: does not fold an implicit return that dedents out of a loop body</summary>

#### does not fold an implicit return that dedents out of a loop body

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(dedented_implicit_return(3), -1)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `4f87aa2841056f63415684f70d0c1ed2fed585273f07d170d94a2f19249a28b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f87aa2841056f63415684f70d0c1ed2fed585273f07d170d94a2f19249a28b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f87aa2841056f63415684f70d0c1ed2fed585273f07d170d94a2f19249a28b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/parser_leading_operator_continuation_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_leading_operator_continuation_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_leading_operator_continuation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_leading_operator_continuation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_leading_operator_continuation_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/parser_leading_operator_continuation_spec.spl:345:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues after postfix optional presence' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_leading_operator_continuation_spec.spl:352:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues arithmetic operators onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_leading_operator_continuation_spec.spl:359:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues and/or onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_leading_operator_continuation_spec.spl:363:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'continues comparison and equality operators onto the next line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

# Parser: an inline `match` value may be terminated by the enclosing list

> A `match` used as a VALUE inside a call's argument list, a struct-literal field list, an array literal or a dict literal ends at that list's separator or closing bracket — the `,` / `)` / `]` / `}` shares the last arm's line, so the lexer has not flushed a DEDENT yet.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: an inline `match` value may be terminated by the enclosing list

A `match` used as a VALUE inside a call's argument list, a struct-literal field list, an array literal or a dict literal ends at that list's separator or closing bracket — the `,` / `)` / `]` / `}` shares the last arm's line, so the lexer has not flushed a DEDENT yet.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / Self-hosted frontend parity |
| Status | Active |
| Source | `test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A `match` used as a VALUE inside a call's argument list, a struct-literal field
list, an array literal or a dict literal ends at that list's separator or
closing bracket — the `,` / `)` / `]` / `}` shares the last arm's line, so the
lexer has not flushed a DEDENT yet.

The self-hosted arm loop in `parse_match_arms_common` only stopped on DEDENT or
EOF, so the terminator fell through to the caseless-arm branch and was handed to
`parse_expr` as if it began another pattern:

- `Box(a: match x: ... "other", b: x)` → `expected pattern, found Comma`
- `Box(b: x, a: match x: ... "other")` → `expected pattern, found RParen`

The Rust seed parses both. This blocked the hosted-WM showcase gate at
`src/os/hosted/hosted_web_content_session.spl:983` — a `semantic_target_id:`
field whose value is an inline `match` followed by the field-terminating comma.

A parse error means this file will not load, so the declarations below are
themselves the grammar coverage. The `it` blocks assert that each inline match
still selects the right arm, which is what a mis-terminated arm list would
corrupt.

## Syntax

```simple
Box(
    a: match x:
        1: "one"
        _: "other",      # <- field-terminating comma, not another pattern
    b: x
)
```

## Scenarios

### inline match terminated by the enclosing argument or field list

#### ends a struct-literal field at the field-terminating comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### ends the last struct-literal field at the closing paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_field_then_rparen(1), "one")
assert_equal(match_field_then_rparen(7), "other")
```

</details>

#### ends a call argument at the argument-separating comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_call_arg_then_comma(1), "one/1")
assert_equal(match_call_arg_then_comma(7), "other/7")
```

</details>

#### ends the last call argument at the closing paren on the arm's line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_last_call_arg_then_rparen(1), "one/1")
assert_equal(match_last_call_arg_then_rparen(7), "other/7")
```

</details>

#### ends an array element at the element-separating comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_array_element_then_comma(1), "one+tail")
assert_equal(match_array_element_then_comma(7), "other+tail")
```

</details>

#### ends case-spelled arms at the same terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_case_arms_then_comma(1), "one")
assert_equal(match_case_arms_then_comma(7), "other")
```

</details>

#### lets a nested match end without consuming the outer terminator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_match_then_comma(1, 2), "one-two")
assert_equal(nested_match_then_comma(1, 9), "one-other")
assert_equal(nested_match_then_comma(7, 2), "other")
```

</details>

#### still ends a statement match at the DEDENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_as_statement(1), "one")
assert_equal(match_as_statement(7), "other")
```

</details>

#### still ends a local-bound match at the DEDENT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(match_bound_to_local(1), "one")
assert_equal(match_bound_to_local(7), "other")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `311f8bd265c14c9939eee7813c1ca4e95c80a252e619b74aac1b0fa5743a86ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `311f8bd265c14c9939eee7813c1ca4e95c80a252e619b74aac1b0fa5743a86ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `311f8bd265c14c9939eee7813c1ca4e95c80a252e619b74aac1b0fa5743a86ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_inline_match_in_argument_list_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_inline_match_in_argument_list_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_inline_match_in_argument_list_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl:148:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ends a struct-literal field at the field-terminating comma' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl:154:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ends the last struct-literal field at the closing paren' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl:158:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ends a call argument at the argument-separating comma' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_inline_match_in_argument_list_spec.spl:162:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'ends the last call argument at the closing paren on the arm's line' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

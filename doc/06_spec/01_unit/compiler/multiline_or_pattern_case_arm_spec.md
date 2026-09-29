# A `case` or-pattern may wrap onto a continuation line

> `case A | B |` followed by the remaining alternatives on the next line died with `Unexpected token: expected pattern, found Indent`. The continuation line opens a lexer pseudo-INDENT whose compensating DEDENT arrives *before* the arm body (`Newline Dedent Indent <body>`), but `parse_match_arm` reconciled it only *after* the body. `parse_inline_or_block` then found a DEDENT where it wanted an INDENT, and the arm loop read the body's INDENT as the next pattern — hence the misleading diagnostic, which never mentioned `match`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A `case` or-pattern may wrap onto a continuation line

`case A | B |` followed by the remaining alternatives on the next line died with `Unexpected token: expected pattern, found Indent`. The continuation line opens a lexer pseudo-INDENT whose compensating DEDENT arrives *before* the arm body (`Newline Dedent Indent <body>`), but `parse_match_arm` reconciled it only *after* the body. `parse_inline_or_block` then found a DEDENT where it wanted an INDENT, and the arm loop read the body's INDENT as the next pattern — hence the misleading diagnostic, which never mentioned `match`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Parser / match-arm patterns |
| Status | Active |
| Source | `test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`case A | B |` followed by the remaining alternatives on the next line died
with `Unexpected token: expected pattern, found Indent`. The continuation line
opens a lexer pseudo-INDENT whose compensating DEDENT arrives *before* the arm
body (`Newline Dedent Indent <body>`), but `parse_match_arm` reconciled it only
*after* the body. `parse_inline_or_block` then found a DEDENT where it wanted
an INDENT, and the arm loop read the body's INDENT as the next pattern — hence
the misleading diagnostic, which never mentioned `match`.

The fix routes the pattern continuation through `deferred_dedent_count`, the
channel `if`/`while` header continuations already use, which handles both the
deep and shallow continuation shapes.

## Coverage

Both wrap styles are covered, because they take different paths through
`parse_pattern_inner`: a TRAILING `|` reaches the continuation via the
`while self.check(Pipe)` body, a LEADING `|` via
`peek_through_newlines_and_indents_is(Pipe)`. The single-line form is the
control — it parsed correctly on the buggy lane, so a red control means the
harness, not the defect.

Values, not merely parseability, are asserted: a pattern that parses but
selects the wrong alternative would be a silent wrong result.

## Scenarios

### multi-line or-pattern in a case arm

#### parses and selects with a trailing pipe continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### does not over-match with a trailing pipe continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(wrap_trailing(4), 0)
```

</details>

#### parses and selects with a leading pipe continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(wrap_leading(3), 9)
```

</details>

#### does not over-match with a leading pipe continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(wrap_leading(4), 0)
```

</details>

#### keeps the one-line control form correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(one_line(2), 9)
```

</details>

#### keeps the one-line control form from over-matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(one_line(4), 0)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5b4bf28a563eb09fd737d4dccc0a7ca32964ad206459de063b094f069d662040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b4bf28a563eb09fd737d4dccc0a7ca32964ad206459de063b094f069d662040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b4bf28a563eb09fd737d4dccc0a7ca32964ad206459de063b094f069d662040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl
mirror: doc/06_spec/01_unit/compiler/multiline_or_pattern_case_arm_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/multiline_or_pattern_case_arm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/multiline_or_pattern_case_arm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses and selects with a trailing pipe continuation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl:76:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not over-match with a trailing pipe continuation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl:79:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses and selects with a leading pipe continuation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/multiline_or_pattern_case_arm_spec.spl:82:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not over-match with a leading pipe continuation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

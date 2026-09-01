# Parser: contextual keywords are ordinary names in named-argument position

> `examples` is lexed as a dedicated soft-keyword token (`TokenKind::Examples`, for the Gherkin `examples name:` data-table block). The named-argument parser accepted many keyword tokens as argument labels but not this one, so `K(examples: "ok")` failed with "expected Comma, found Colon" even though the field *declared* and *read* fine.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser: contextual keywords are ordinary names in named-argument position

`examples` is lexed as a dedicated soft-keyword token (`TokenKind::Examples`, for the Gherkin `examples name:` data-table block). The named-argument parser accepted many keyword tokens as argument labels but not this one, so `K(examples: "ok")` failed with "expected Comma, found Colon" even though the field *declared* and *read* fine.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Syntax / Seed parser keyword hygiene |
| Status | Active |
| Source | `test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`examples` is lexed as a dedicated soft-keyword token (`TokenKind::Examples`,
for the Gherkin `examples name:` data-table block). The named-argument parser
accepted many keyword tokens as argument labels but not this one, so
`K(examples: "ok")` failed with "expected Comma, found Colon" even though the
field *declared* and *read* fine.

A parse error means this file will not load, so the constructions below are
themselves the grammar coverage; the `it` blocks assert the values round-trip.
The generalization probes exercise other contextual keywords in the same
named-arg position (`feature`, `scenario`, `given`, `when`, `then`, `context`,
`grid`) plus spec-DSL names that are plain identifiers (`describe`, `it`).

## Syntax

```simple
use std.spec.step

val k = K(examples: "ok")     # keyword token as a named-arg label
print(k.examples)
```

## Scenarios

### contextual keywords as named-argument labels

#### accepts `examples` as a named argument and reads it back

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### accepts gherkin soft keywords as named arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = Gherkinish(feature: "f", scenario: "s", given: "g", when: "w", then: "t")
assert_equal(g.feature, "f")
assert_equal(g.scenario, "s")
assert_equal(g.given, "g")
assert_equal(g.when, "w")
assert_equal(g.then, "t")
```

</details>

#### accepts spec DSL names describe/it/context as named arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SpecNames(describe: "d", it: "i", context: "c")
assert_equal(s.describe, "d")
assert_equal(s.it, "i")
assert_equal(s.context, "c")
```

</details>

#### accepts `grid` as a named argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = GridBox(grid: 7)
assert_equal(b.grid, 7)
```

</details>

#### accepts `and_then` as a named argument and reads it back

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Chained(and_then: "ok")
assert_equal(c.and_then, "ok")
```

</details>

### builtin names are shadowable by ordinary bindings

#### lets a user-defined `fn generator` shadow the lambda builtin

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(generator(5, fn(n): (n + 1, true)), 5)
```

</details>

#### resolves `generator` from another function in the same module

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(generator_caller(0, 3), 0)
```

</details>

#### accepts `generator` as a local binding name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val generator = 7
assert_equal(generator, 7)
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

- Canonical SPipe generation for source `9fd39c6f5a4e800509cd62713bf6cfad8d7ec08be1b395775d9a42114e59aa0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9fd39c6f5a4e800509cd62713bf6cfad8d7ec08be1b395775d9a42114e59aa0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9fd39c6f5a4e800509cd62713bf6cfad8d7ec08be1b395775d9a42114e59aa0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_contextual_keyword_named_arg_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_contextual_keyword_named_arg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_contextual_keyword_named_arg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl:76:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `examples` as a named argument and reads it back' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl:82:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts gherkin soft keywords as named arguments' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl:90:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts spec DSL names describe/it/context as named arguments' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl:96:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `grid` as a named argument' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

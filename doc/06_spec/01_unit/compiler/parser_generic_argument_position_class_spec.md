# Parser Generic Argument Position Class Specification

> Tests covering explicit generic-argument positions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Generic Argument Position Class Specification

## Scenarios

### explicit generic-argument positions

#### reports a const-generic argument nested inside another generic argument

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a const-generic argument nested inside another generic argument
- The numeric argument sits one generic level down
- The diagnostic still names const generics, not a stray token
   - Expected: out does not contain `expected expression, found Comma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a const-generic argument nested inside another generic argument")
step("The numeric argument sits one generic level down")
val out = compile_source("nested", NESTED_CONST_SOURCE)

step("The diagnostic still names const generics, not a stray token")
expect(out).to_contain("const generic")
expect(out.contains("expected expression, found Comma")).to_equal(false)
```

</details>

#### reports a const-generic argument in the dotted (non-call) position

- reports a const-generic argument in the dotted (non-call) position
- The lookahead also commits when the closing > is followed by a dot
- The diagnostic names const generics rather than a comparison error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a const-generic argument in the dotted (non-call) position")
step("The lookahead also commits when the closing > is followed by a dot")
val out = compile_source("dotted", METHOD_TURBOFISH_CONST_SOURCE)

step("The diagnostic names const generics rather than a comparison error")
expect(out).to_contain("const generic")
```

</details>

#### still parses an ordinary comparison chain that merely looks like generics

- still parses an ordinary comparison chain that merely looks like generics
- `take(a < b, c > d)` is two comparisons, not a generic argument list
- It runs, so the speculative parse still backtracks correctly
- Absence control: no const-generic diagnostic was emitted here
   - Expected: out does not contain `const generic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still parses an ordinary comparison chain that merely looks like generics")
step("`take(a < b, c > d)` is two comparisons, not a generic argument list")
val out = compile_source("comparison", COMPARISON_CHAIN_SOURCE)

step("It runs, so the speculative parse still backtracks correctly")
expect(out).to_contain("compared ok")

step("Absence control: no const-generic diagnostic was emitted here")
expect(out.contains("const generic")).to_equal(false)
```

</details>

#### leaves integer literals outside generic-argument position untouched

- leaves integer literals outside generic-argument position untouched
- An array index is an integer literal in a position the rule must ignore
   - Expected: out does not contain `const generic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves integer literals outside generic-argument position untouched")
step("An array index is an integer literal in a position the rule must ignore")
val out = compile_source("plain_integer", PLAIN_INTEGER_SOURCE)

expect(out).to_contain("indexed 30")
expect(out.contains("const generic")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser_generic_argument_position_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering explicit generic-argument positions.
- explicit generic-argument positions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `7f426121fcf45fa5ef494852fa717c022e572493d95edffd1c48fd4e6c76a21c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f426121fcf45fa5ef494852fa717c022e572493d95edffd1c48fd4e6c76a21c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f426121fcf45fa5ef494852fa717c022e572493d95edffd1c48fd4e6c76a21c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser_generic_argument_position_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_generic_argument_position_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_generic_argument_position_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_generic_argument_position_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_generic_argument_position_class_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a const-generic argument nested inside another generic argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_generic_argument_position_class_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a const-generic argument in the dotted (non-call) position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_generic_argument_position_class_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still parses an ordinary comparison chain that merely looks like generics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

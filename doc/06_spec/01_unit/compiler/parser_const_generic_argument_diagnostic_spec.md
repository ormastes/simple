# Parser Const Generic Argument Diagnostic Specification

> Tests covering const-generic argument in constructor-call position.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Const Generic Argument Diagnostic Specification

## Scenarios

### const-generic argument in constructor-call position

#### reports the const-generic limitation instead of blaming a later comma

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the const-generic limitation instead of blaming a later comma
- Compile a constructor call carrying a numeric generic argument
- The diagnostic names const generics — the actual limitation
- It no longer blames the comma that merely followed the real problem
   - Expected: out does not contain `expected expression, found Comma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the const-generic limitation instead of blaming a later comma")
step("Compile a constructor call carrying a numeric generic argument")
val out = compile_source("reject", CONST_ARG_SOURCE)

step("The diagnostic names const generics — the actual limitation")
expect(out).to_contain("const generic")

step("It no longer blames the comma that merely followed the real problem")
expect(out.contains("expected expression, found Comma")).to_equal(false)
```

</details>

#### still accepts a turbofish whose arguments are all real types

- still accepts a turbofish whose arguments are all real types
- Turbofish in expression position was never the limitation
- The program runs to completion
- Absence control: an accepted call emits no const-generic diagnostic
   - Expected: out does not contain `const generic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a turbofish whose arguments are all real types")
step("Turbofish in expression position was never the limitation")
val out = compile_source("accept", TYPE_ARG_SOURCE)

step("The program runs to completion")
expect(out).to_contain("built ok")

step("Absence control: an accepted call emits no const-generic diagnostic")
expect(out.contains("const generic")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering const-generic argument in constructor-call position.
- const-generic argument in constructor-call position

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `b841b2d7c3ba481cc03d96bf21f37587bce11b6c8923ff55287d8eb21247ec1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b841b2d7c3ba481cc03d96bf21f37587bce11b6c8923ff55287d8eb21247ec1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b841b2d7c3ba481cc03d96bf21f37587bce11b6c8923ff55287d8eb21247ec1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the const-generic limitation instead of blaming a later comma' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_const_generic_argument_diagnostic_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts a turbofish whose arguments are all real types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

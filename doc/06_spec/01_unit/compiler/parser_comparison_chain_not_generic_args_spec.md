# Parser Comparison Chain Not Generic Args Specification

> Tests covering comparison chain closed by a parenthesised expression.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Comparison Chain Not Generic Args Specification

## Scenarios

### comparison chain closed by a parenthesised expression

#### parses the incident shape in an if condition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses the incident shape in an if condition
- `if a < 0 or a > (b - c)` is a comparison chain, not generic args


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the incident shape in an if condition")
step("`if a < 0 or a > (b - c)` is a comparison chain, not generic args")
expect_parses("if", IF_SOURCE, "if ok")
```

</details>

#### parses the same shape in a while condition

- parses the same shape in a while condition
- Defect-class neighbour: loop condition position


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the same shape in a while condition")
step("Defect-class neighbour: loop condition position")
expect_parses("while", WHILE_SOURCE, "while ok")
```

</details>

#### parses the same shape in a returned expression

- parses the same shape in a returned expression
- Defect-class neighbour: value position, not condition position


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses the same shape in a returned expression")
step("Defect-class neighbour: value position, not condition position")
expect_parses("return", RETURN_SOURCE, "return ok")
```

</details>

#### parses an ident-only chain with no numeric literal

- parses an ident-only chain with no numeric literal
- Defect-class neighbour: the separator ratchet never arms here


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses an ident-only chain with no numeric literal")
step("Defect-class neighbour: the separator ratchet never arms here")
expect_parses("ident", IDENT_ONLY_SOURCE, "ident ok")
```

</details>

#### keeps `>>` a shift operator rather than two closing angles

- keeps `>>` a shift operator rather than two closing angles
- Defect-class neighbour: SHR must not close a phantom generic list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps `>>` a shift operator rather than two closing angles")
step("Defect-class neighbour: SHR must not close a phantom generic list")
expect_parses("shift", SHIFT_SOURCE, "shift ok")
```

</details>

#### still diagnoses a genuine const-generic argument

- still diagnoses a genuine const-generic argument
- Absence control — the diagnostic was narrowed, not removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still diagnoses a genuine const-generic argument")
step("Absence control — the diagnostic was narrowed, not removed")
val out = compile_source("real", REAL_CONST_ARG_SOURCE)
expect(out).to_contain("const generic")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering comparison chain closed by a parenthesised expression.
- comparison chain closed by a parenthesised expression

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

- Canonical SPipe generation for source `0a23f69064765866c6bba49220675aa8e6ac6bde3860ad0e7da755f79777a768`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a23f69064765866c6bba49220675aa8e6ac6bde3860ad0e7da755f79777a768`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a23f69064765866c6bba49220675aa8e6ac6bde3860ad0e7da755f79777a768`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the incident shape in an if condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the same shape in a while condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses the same shape in a returned expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

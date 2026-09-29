# Lexer Interp Literal Brace Specification

> Tests covering Lexer interpolation vs literal brace.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Interp Literal Brace Specification

## Scenarios

### Lexer interpolation vs literal brace

#### keeps concatenation operators around a literal brace

- keeps concatenation operators around a literal brace
   - Expected: lex_render(src) equals `"p " + lb() + " |+|v|+| " + rb()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps concatenation operators around a literal brace")
# "p { " + v + " }"
val src = q() + "p " + lb() + " " + q() + " + v + " + q() + " " + rb() + q()
expect(lex_render(src)).to_equal("p " + lb() + " |+|v|+| " + rb())
```

</details>

#### keeps concatenation operators for a css declaration brace

- keeps concatenation operators for a css declaration brace
   - Expected: lex_render(src) equals `"p " + lb() + " q: |+|v|+|; " + rb()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps concatenation operators for a css declaration brace")
# "p { q: " + v + "; }"
val src = q() + "p " + lb() + " q: " + q() + " + v + " + q() + "; " + rb() + q()
expect(lex_render(src)).to_equal("p " + lb() + " q: |+|v|+|; " + rb())
```

</details>

#### keeps a literal brace with trailing text

- keeps a literal brace with trailing text
   - Expected: lex_render(src) equals `x " + lb() + " |+|v|+| " + rb() + " y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a literal brace with trailing text")
# "x { " + v + " } y"
val src = q() + "x " + lb() + " " + q() + " + v + " + q() + " " + rb() + " y" + q()
expect(lex_render(src)).to_equal("x " + lb() + " |+|v|+| " + rb() + " y")
```

</details>

#### does not split a nested string inside a call

- does not split a nested string inside a call
   - Expected: lex_render(q() + inner + q()) equals `inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not split a nested string inside a call")
# "{xs.join("-")}"
val inner = lb() + "xs.join(" + q() + "-" + q() + ")" + rb()
expect(lex_render(q() + inner + q())).to_equal(inner)
```

</details>

#### does not split a plain interpolation

- does not split a plain interpolation
   - Expected: lex_render(q() + inner + q()) equals `inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not split a plain interpolation")
# "{a + b}"
val inner = lb() + "a + b" + rb()
expect(lex_render(q() + inner + q())).to_equal(inner)
```

</details>

#### allows a nested string right after a binary operator

- allows a nested string right after a binary operator
   - Expected: lex_render(q() + inner + q()) equals `inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows a nested string right after a binary operator")
# "{k != ""}"
val inner = lb() + "k != " + q() + q() + rb()
expect(lex_render(q() + inner + q())).to_equal(inner)
```

</details>

#### allows nested strings inside an inline conditional

- allows nested strings inside an inline conditional
   - Expected: lex_render(q() + inner + q()) equals `inner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows nested strings inside an inline conditional")
# "{if c: "y" else: "n"}"
val inner = lb() + "if c: " + q() + "y" + q() + " else: " + q() + "n" + q() + rb()
expect(lex_render(q() + inner + q())).to_equal(inner)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer interpolation vs literal brace.
- Lexer interpolation vs literal brace

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `d92efe50cc9571cdf093cd09da2e4cd1f9dd6b425221ef16b8e5f351a4226618`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d92efe50cc9571cdf093cd09da2e4cd1f9dd6b425221ef16b8e5f351a4226618`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d92efe50cc9571cdf093cd09da2e4cd1f9dd6b425221ef16b8e5f351a4226618`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps concatenation operators around a literal brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps concatenation operators for a css declaration brace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_interp_literal_brace_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a literal brace with trailing text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

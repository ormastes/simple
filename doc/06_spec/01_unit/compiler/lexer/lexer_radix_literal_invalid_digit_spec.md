# Lexer Radix Literal Invalid Digit Specification

> Tests covering Lexer radix literal invalid-digit diagnostics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Radix Literal Invalid Digit Specification

## Scenarios

### Lexer radix literal invalid-digit diagnostics

#### flags an octal literal containing an 8 as a lex error, not a silent INT

- flags an octal literal containing an 8 as a lex error, not a silent INT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags an octal literal containing an 8 as a lex error, not a silent INT")
val out = lex_first("0o789")
expect(out).to_start_with(TOK_ERROR.to_text() + ":")
```

</details>

#### reports the offending digit and the literal text for 0o789

- reports the offending digit and the literal text for 0o789


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the offending digit and the literal text for 0o789")
val out = lex_first("0o789")
expect(out).to_contain("8")
expect(out).to_contain("0o789")
```

</details>

#### flags 0o8 (single bad digit) as a lex error

- flags 0o8 (single bad digit) as a lex error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags 0o8 (single bad digit) as a lex error")
val out = lex_first("0o8")
expect(out).to_start_with(TOK_ERROR.to_text() + ":")
```

</details>

#### flags a binary literal containing a 2 as a lex error, not a silent split

- flags a binary literal containing a 2 as a lex error, not a silent split


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags a binary literal containing a 2 as a lex error, not a silent split")
val out = lex_first("0b123")
expect(out).to_start_with(TOK_ERROR.to_text() + ":")
```

</details>

#### reports the offending digit and the literal text for 0b123

- reports the offending digit and the literal text for 0b123


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the offending digit and the literal text for 0b123")
val out = lex_first("0b123")
expect(out).to_contain("2")
expect(out).to_contain("0b123")
```

</details>

#### still lexes a valid octal literal as a plain int

- still lexes a valid octal literal as a plain int
   - Expected: lex_first("0o644") equals `TOK_INT_LIT.to_text() + ":0o644"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes a valid octal literal as a plain int")
expect(lex_first("0o644")).to_equal(TOK_INT_LIT.to_text() + ":0o644")
```

</details>

#### still lexes a valid octal literal with a type suffix

- still lexes a valid octal literal with a type suffix
   - Expected: lex_first("0o644u32") equals `TOK_SUFFIXED_INT.to_text() + ":0o644"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes a valid octal literal with a type suffix")
expect(lex_first("0o644u32")).to_equal(TOK_SUFFIXED_INT.to_text() + ":0o644")
```

</details>

#### still lexes a valid binary literal as a plain int

- still lexes a valid binary literal as a plain int
   - Expected: lex_first("0b1010") equals `TOK_INT_LIT.to_text() + ":0b1010"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes a valid binary literal as a plain int")
expect(lex_first("0b1010")).to_equal(TOK_INT_LIT.to_text() + ":0b1010")
```

</details>

#### still lexes a valid binary literal with a type suffix

- still lexes a valid binary literal with a type suffix
   - Expected: lex_first("0b1010u64") equals `TOK_SUFFIXED_INT.to_text() + ":0b1010"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes a valid binary literal with a type suffix")
expect(lex_first("0b1010u64")).to_equal(TOK_SUFFIXED_INT.to_text() + ":0b1010")
```

</details>

#### still lexes a valid hex literal (unrelated radix, unaffected by this fix)

- still lexes a valid hex literal (unrelated radix, unaffected by this fix)
   - Expected: lex_first("0x1F") equals `TOK_INT_LIT.to_text() + ":0x1F"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes a valid hex literal (unrelated radix, unaffected by this fix)")
expect(lex_first("0x1F")).to_equal(TOK_INT_LIT.to_text() + ":0x1F")
```

</details>

#### still lexes an octal literal with underscore separators

- still lexes an octal literal with underscore separators
   - Expected: lex_first("0o7_5_5") equals `TOK_INT_LIT.to_text() + ":0o7_5_5"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still lexes an octal literal with underscore separators")
expect(lex_first("0o7_5_5")).to_equal(TOK_INT_LIT.to_text() + ":0o7_5_5")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer radix literal invalid-digit diagnostics.
- Lexer radix literal invalid-digit diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `417d1e877d4a09107972e2c30b2c3958ddf3e05c5f8d3a0a459b35cfb0e95d69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `417d1e877d4a09107972e2c30b2c3958ddf3e05c5f8d3a0a459b35cfb0e95d69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `417d1e877d4a09107972e2c30b2c3958ddf3e05c5f8d3a0a459b35cfb0e95d69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags an octal literal containing an 8 as a lex error, not a silent INT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the offending digit and the literal text for 0o789' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_radix_literal_invalid_digit_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags 0o8 (single bad digit) as a lex error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

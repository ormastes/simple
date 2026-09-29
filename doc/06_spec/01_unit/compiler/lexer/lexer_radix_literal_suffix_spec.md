# Lexer Radix Literal Suffix Specification

> Tests covering Lexer radix literal suffixes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Radix Literal Suffix Specification

## Scenarios

### Lexer radix literal suffixes

#### keeps a hex literal's type suffix on one token

- keeps a hex literal's type suffix on one token
   - Expected: lex_render("0x1010u64") equals `one_suffixed("0x1010", "u64")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a hex literal's type suffix on one token")
expect(lex_render("0x1010u64")).to_equal(one_suffixed("0x1010", "u64"))
```

</details>

#### keeps a hex literal's underscore-form suffix on one token

- keeps a hex literal's underscore-form suffix on one token
   - Expected: lex_render("0x1010_u64") equals `one_suffixed("0x1010", "u64")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a hex literal's underscore-form suffix on one token")
expect(lex_render("0x1010_u64")).to_equal(one_suffixed("0x1010", "u64"))
```

</details>

#### keeps a binary literal's type suffix on one token

- keeps a binary literal's type suffix on one token
   - Expected: lex_render("0b1010u64") equals `one_suffixed("0b1010", "u64")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a binary literal's type suffix on one token")
expect(lex_render("0b1010u64")).to_equal(one_suffixed("0b1010", "u64"))
```

</details>

#### keeps a binary literal's underscore-form suffix on one token

- keeps a binary literal's underscore-form suffix on one token
   - Expected: lex_render("0b1010_u64") equals `one_suffixed("0b1010", "u64")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a binary literal's underscore-form suffix on one token")
expect(lex_render("0b1010_u64")).to_equal(one_suffixed("0b1010", "u64"))
```

</details>

#### keeps an octal literal's type suffix on one token

- keeps an octal literal's type suffix on one token
   - Expected: lex_render("0o644u32") equals `one_suffixed("0o644", "u32")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an octal literal's type suffix on one token")
expect(lex_render("0o644u32")).to_equal(one_suffixed("0o644", "u32"))
```

</details>

#### keeps an octal literal's underscore-form suffix on one token

- keeps an octal literal's underscore-form suffix on one token
   - Expected: lex_render("0o755_u32") equals `one_suffixed("0o755", "u32")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an octal literal's underscore-form suffix on one token")
expect(lex_render("0o755_u32")).to_equal(one_suffixed("0o755", "u32"))
```

</details>

#### leaves an unsuffixed binary literal a plain int

- leaves an unsuffixed binary literal a plain int
   - Expected: lex_render("0b1010") equals `one_int("0b1010")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an unsuffixed binary literal a plain int")
expect(lex_render("0b1010")).to_equal(one_int("0b1010"))
```

</details>

#### leaves an unsuffixed octal literal a plain int

- leaves an unsuffixed octal literal a plain int
   - Expected: lex_render("0o644") equals `one_int("0o644")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an unsuffixed octal literal a plain int")
expect(lex_render("0o644")).to_equal(one_int("0o644"))
```

</details>

#### consumes a full 64-bit binary literal with underscore separators

- consumes a full 64-bit binary literal with underscore separators
   - Expected: lex_render(body) equals `one_int(body)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes a full 64-bit binary literal with underscore separators")
# 8 groups of 8 bits = 71 chars after `0b`, past the old 64 cap.
val body = "0b11111111_00000000_11111111_00000000_11111111_00000000_11111111_00000001"
expect(lex_render(body)).to_equal(one_int(body))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer radix literal suffixes.
- Lexer radix literal suffixes

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

- Canonical SPipe generation for source `3179fcdc1aa54f59d8cf4749e67e5349c36f2b19eb979731f210a97887d6244f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3179fcdc1aa54f59d8cf4749e67e5349c36f2b19eb979731f210a97887d6244f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3179fcdc1aa54f59d8cf4749e67e5349c36f2b19eb979731f210a97887d6244f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl
mirror: doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a hex literal's type suffix on one token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a hex literal's underscore-form suffix on one token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lexer/lexer_radix_literal_suffix_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a binary literal's type suffix on one token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

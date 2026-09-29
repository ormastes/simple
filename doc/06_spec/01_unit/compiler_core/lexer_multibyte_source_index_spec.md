# Lexer Multibyte Source Index Specification

> Tests covering lex_source_char_at/lex_source_slice with a preceding multi-byte codepoint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Multibyte Source Index Specification

## Scenarios

### lex_source_char_at/lex_source_slice with a preceding multi-byte codepoint

#### reads the correct char_at position after a multi-byte em-dash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the correct char_at position after a multi-byte em-dash
- source: x, em-dash (1 codepoint, 3 bytes), then a quoted string
- codepoint 2 is the opening quote; byte-indexing would land 2 bytes short
   - Expected: lex_source_char_at(2) equals `"`
   - Expected: lex_source_char_at(3) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("reads the correct char_at position after a multi-byte em-dash")
step("source: x, em-dash (1 codepoint, 3 bytes), then a quoted string")
lex_init("x—\"hi\"")
step("codepoint 2 is the opening quote; byte-indexing would land 2 bytes short")
expect(lex_source_char_at(2)).to_equal("\"")
expect(lex_source_char_at(3)).to_equal("h")
```

</details>

#### reads the correct slice after a multi-byte codepoint

- reads the correct slice after a multi-byte codepoint
- codepoints 3..5 are 'hi', the string body
   - Expected: lex_source_slice(3, 5) equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("reads the correct slice after a multi-byte codepoint")
step("codepoints 3..5 are 'hi', the string body")
lex_init("x—\"hi\"")
expect(lex_source_slice(3, 5)).to_equal("hi")
```

</details>

#### handles multiple multi-byte codepoints before the target position

- handles multiple multi-byte codepoints before the target position
- two multi-byte chars (— and é, 3+2 bytes) precede the quote
   - Expected: lex_source_char_at(2) equals `"`
   - Expected: lex_source_slice(3, 5) equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("handles multiple multi-byte codepoints before the target position")
step("two multi-byte chars (— and é, 3+2 bytes) precede the quote")
lex_init("é—\"ok\"")
expect(lex_source_char_at(2)).to_equal("\"")
expect(lex_source_slice(3, 5)).to_equal("ok")
```

</details>

#### leaves plain-ASCII indexing unaffected (regression guard)

- leaves plain-ASCII indexing unaffected (regression guard)
- no multi-byte prefix: byte and codepoint indices coincide
   - Expected: lex_source_char_at(1) equals `"`
   - Expected: lex_source_slice(2, 4) equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("leaves plain-ASCII indexing unaffected (regression guard)")
step("no multi-byte prefix: byte and codepoint indices coincide")
lex_init("x\"hi\"")
expect(lex_source_char_at(1)).to_equal("\"")
expect(lex_source_slice(2, 4)).to_equal("hi")
```

</details>

#### out-of-range positions still return empty, not a shifted char

- out-of-range positions still return empty, not a shifted char
   - Expected: lex_source_char_at(100) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("out-of-range positions still return empty, not a shifted char")
lex_init("—\"z\"")
expect(lex_source_char_at(100)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/lexer_multibyte_source_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lex_source_char_at/lex_source_slice with a preceding multi-byte codepoint.
- lex_source_char_at/lex_source_slice with a preceding multi-byte codepoint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d824422bbcd8e1a21397dc76ed38644c7dc6bab18a172392f2f8b88a997b89b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d824422bbcd8e1a21397dc76ed38644c7dc6bab18a172392f2f8b88a997b89b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d824422bbcd8e1a21397dc76ed38644c7dc6bab18a172392f2f8b88a997b89b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/lexer_multibyte_source_index_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/lexer_multibyte_source_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/lexer_multibyte_source_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/lexer_multibyte_source_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/lexer_multibyte_source_index_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the correct char_at position after a multi-byte em-dash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/lexer_multibyte_source_index_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the correct slice after a multi-byte codepoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/lexer_multibyte_source_index_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multiple multi-byte codepoints before the target position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Lexer Specification

> Tests covering core.lexer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lexer Specification

## Scenarios

### core.lexer

#### lexes basic tokens

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lexes basic tokens
   - Expected: kinds[0] equals `TOK_KW_VAL`
   - Expected: kinds[1] equals `TOK_IDENT`
   - Expected: kinds[2] equals `TOK_ASSIGN`
   - Expected: kinds[3] equals `TOK_INT_LIT`
   - Expected: kinds[kinds.len() - 1] equals `TOK_EOF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lexes basic tokens")
var kinds = collect_kinds("val x = 123\n")
expect(kinds[0]).to_equal(TOK_KW_VAL)
expect(kinds[1]).to_equal(TOK_IDENT)
expect(kinds[2]).to_equal(TOK_ASSIGN)
expect(kinds[3]).to_equal(TOK_INT_LIT)
expect(kinds[kinds.len() - 1]).to_equal(TOK_EOF)
```

</details>

#### lexes strings

- lexes strings
   - Expected: find_kind(kinds, TOK_STRING_LIT) is true
   - Expected: texts[0] equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lexes strings")
var kinds = collect_kinds("val s = \"hi\"\n")
expect(find_kind(kinds, TOK_STRING_LIT)).to_equal(true)
var texts = collect_texts("\"hi\"")
expect(texts[0]).to_equal("hi")
```

</details>

#### lexes floats and exponents

- lexes floats and exponents
   - Expected: find_kind(kinds, TOK_FLOAT_LIT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lexes floats and exponents")
var kinds = collect_kinds("val x = 1.5\nval y = 2e3\n")
expect(find_kind(kinds, TOK_FLOAT_LIT)).to_equal(true)
```

</details>

#### lexes hex/bin/oct and separators

- lexes hex/bin/oct and separators
   - Expected: find_kind(kinds, TOK_INT_LIT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lexes hex/bin/oct and separators")
var kinds = collect_kinds("val a = 0xFF\nval b = 0b1010\nval c = 0o10\nval d = 1_000\n")
expect(find_kind(kinds, TOK_INT_LIT)).to_equal(true)
```

</details>

#### handles indentation

- handles indentation
   - Expected: find_kind(kinds, TOK_INDENT) is true
   - Expected: find_kind(kinds, TOK_DEDENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles indentation")
var kinds = collect_kinds("fn main():\n    val x = 1\n    val y = 2\n")
expect(find_kind(kinds, TOK_INDENT)).to_equal(true)
expect(find_kind(kinds, TOK_DEDENT)).to_equal(true)
```

</details>

#### skips comments

- skips comments
   - Expected: first_non_trivia(kinds) equals `TOK_KW_VAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips comments")
var kinds = collect_kinds("# comment\nval x = 1\n")
expect(first_non_trivia(kinds)).to_equal(TOK_KW_VAL)
```

</details>

#### lexes special operators

- lexes special operators
   - Expected: find_kind(kinds, TOK_QUESTION_DOT) is true
   - Expected: find_kind(kinds, TOK_DOT_QUESTION) is true
   - Expected: find_kind(kinds, TOK_DOUBLE_QUESTION) is true
   - Expected: find_kind(kinds, TOK_PIPE_FORWARD) is true
   - Expected: find_kind(kinds, TOK_DOUBLE_STAR) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lexes special operators")
var kinds = collect_kinds("a?.b a.? b??c a|>b a**b\n")
expect(find_kind(kinds, TOK_QUESTION_DOT)).to_equal(true)
expect(find_kind(kinds, TOK_DOT_QUESTION)).to_equal(true)
expect(find_kind(kinds, TOK_DOUBLE_QUESTION)).to_equal(true)
expect(find_kind(kinds, TOK_PIPE_FORWARD)).to_equal(true)
expect(find_kind(kinds, TOK_DOUBLE_STAR)).to_equal(true)
```

</details>

#### reports unterminated strings

- reports unterminated strings
   - Expected: find_kind(kinds, TOK_ERROR) is true
   - Expected: texts[0] contains `unterminated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unterminated strings")
var kinds = collect_kinds("\"unterminated\n")
expect(find_kind(kinds, TOK_ERROR)).to_equal(true)
var texts = collect_texts("\"unterminated\n")
# Error message is stored in token text
expect(texts[0].contains("unterminated")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/lexer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering core.lexer.
- core.lexer

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

- Canonical SPipe generation for source `6863b95fa2e34a3f04fa43e063ddb397ff64c0f83ffa7c55bddb141d286678c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6863b95fa2e34a3f04fa43e063ddb397ff64c0f83ffa7c55bddb141d286678c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6863b95fa2e34a3f04fa43e063ddb397ff64c0f83ffa7c55bddb141d286678c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/lexer_spec.spl
mirror: doc/06_spec/unit/compiler_core/lexer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/lexer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/lexer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/lexer_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes basic tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/lexer_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/lexer_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lexes floats and exponents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

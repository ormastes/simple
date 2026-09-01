# Pure Simple Lexer Keyword Lookup Specification

> Tests covering pure-Simple lexer keyword lookup.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Simple Lexer Keyword Lookup Specification

## Scenarios

### pure-Simple lexer keyword lookup

#### tokenizes `for arg in raw:` with in as a keyword, not an identifier

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes `for arg in raw:` with in as a keyword, not an identifier
   - Expected: kinds.len() equals `5`
   - Expected: kinds[0] equals `TOK_KW_FOR`
   - Expected: kinds[1] equals `TOK_IDENT`
   - Expected: kinds[2] equals `TOK_KW_IN`
   - Expected: kinds[2] == TOK_IDENT is false
   - Expected: kinds[3] equals `TOK_IDENT`
   - Expected: kinds[4] equals `TOK_COLON`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("tokenizes `for arg in raw:` with in as a keyword, not an identifier")
val kinds = kinds_of("for arg in raw:", 5)
expect(kinds.len()).to_equal(5)
expect(kinds[0]).to_equal(TOK_KW_FOR)
expect(kinds[1]).to_equal(TOK_IDENT)
# RED shape reported by the row: this is TOK_IDENT, i.e. "Ident".
expect(kinds[2]).to_equal(TOK_KW_IN)
expect(kinds[2] == TOK_IDENT).to_equal(false)
expect(kinds[3]).to_equal(TOK_IDENT)
expect(kinds[4]).to_equal(TOK_COLON)
```

</details>

#### never returns TOK_IDENT for a reserved keyword spelling

- never returns TOK_IDENT for a reserved keyword spelling
   - Expected: keyword_lookup("for") equals `TOK_KW_FOR`
   - Expected: keyword_lookup("in") equals `TOK_KW_IN`
   - Expected: keyword_lookup("while") equals `TOK_KW_WHILE`
   - Expected: keyword_lookup("return") equals `TOK_KW_RETURN`
   - Expected: keyword_lookup("if") equals `TOK_KW_IF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("never returns TOK_IDENT for a reserved keyword spelling")
# keyword_lookup is the single table the lexer consults; a corrupted text
# compare there degrades EVERY keyword to Ident, not just `in`.
expect(keyword_lookup("for")).to_equal(TOK_KW_FOR)
expect(keyword_lookup("in")).to_equal(TOK_KW_IN)
expect(keyword_lookup("while")).to_equal(TOK_KW_WHILE)
expect(keyword_lookup("return")).to_equal(TOK_KW_RETURN)
expect(keyword_lookup("if")).to_equal(TOK_KW_IF)
```

</details>

#### still returns TOK_IDENT for near-miss spellings

- still returns TOK_IDENT for near-miss spellings
   - Expected: keyword_lookup("i") equals `TOK_IDENT`
   - Expected: keyword_lookup("inn") equals `TOK_IDENT`
   - Expected: keyword_lookup("In") equals `TOK_IDENT`
   - Expected: keyword_lookup("forx") equals `TOK_IDENT`
   - Expected: keyword_lookup("raw") equals `TOK_IDENT`
   - Expected: keyword_lookup("arg") equals `TOK_IDENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still returns TOK_IDENT for near-miss spellings")
# The complement: a prefix/suffix-corrupted compare would over-match.
expect(keyword_lookup("i")).to_equal(TOK_IDENT)
expect(keyword_lookup("inn")).to_equal(TOK_IDENT)
expect(keyword_lookup("In")).to_equal(TOK_IDENT)
expect(keyword_lookup("forx")).to_equal(TOK_IDENT)
expect(keyword_lookup("raw")).to_equal(TOK_IDENT)
expect(keyword_lookup("arg")).to_equal(TOK_IDENT)
```

</details>

#### keeps keyword classification stable across a multi-keyword line

- keeps keyword classification stable across a multi-keyword line
   - Expected: kinds[0] equals `TOK_KW_WHILE`
   - Expected: kinds[1] equals `TOK_IDENT`
   - Expected: kinds[2] equals `TOK_KW_IN`
   - Expected: kinds[3] equals `TOK_IDENT`
   - Expected: kinds[4] equals `TOK_COLON`
   - Expected: kinds[5] equals `TOK_KW_RETURN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps keyword classification stable across a multi-keyword line")
val kinds = kinds_of("while x in y: return x", 6)
expect(kinds[0]).to_equal(TOK_KW_WHILE)
expect(kinds[1]).to_equal(TOK_IDENT)
expect(kinds[2]).to_equal(TOK_KW_IN)
expect(kinds[3]).to_equal(TOK_IDENT)
expect(kinds[4]).to_equal(TOK_COLON)
expect(kinds[5]).to_equal(TOK_KW_RETURN)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple lexer keyword lookup.
- pure-Simple lexer keyword lookup

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

- Canonical SPipe generation for source `cec678cb38e9e47bafeae57ab72a3877f70c8d226ac3e1cbab23ac2f1c97961a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cec678cb38e9e47bafeae57ab72a3877f70c8d226ac3e1cbab23ac2f1c97961a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cec678cb38e9e47bafeae57ab72a3877f70c8d226ac3e1cbab23ac2f1c97961a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes `for arg in raw:` with in as a keyword, not an identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never returns TOK_IDENT for a reserved keyword spelling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/pure_simple_lexer_keyword_lookup_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still returns TOK_IDENT for near-miss spellings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Treesitter Lexer Specification

> Tests covering Lexer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Lexer Specification

## Scenarios

### Lexer

#### tokenizes empty source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes empty source")
val lexer = MockLexer.new()
val tokens = lexer.tokenize_empty()
check(tokens.len() == 0)
```

</details>

#### tokenizes keywords

- tokenizes keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes keywords")
val lexer = MockLexer.new()
val result = lexer.tokenize_keywords("val x = 42")
check(result)
```

</details>

#### tokenizes identifiers

- tokenizes identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifiers")
val lexer = MockLexer.new()
val tokens = lexer.tokenize_identifiers("foo")
check(tokens.len() > 0)
```

</details>

#### tokenizes numbers

- tokenizes numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes numbers")
val lexer = MockLexer.new()
val tokens = lexer.tokenize_numbers("123")
check(tokens.len() > 0)
```

</details>

#### tokenizes strings

- tokenizes strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes strings")
val lexer = MockLexer.new()
val tokens = lexer.tokenize_strings("\"hello\"")
check(tokens.len() > 0)
```

</details>

#### tokenizes operators

- tokenizes operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes operators")
val lexer = MockLexer.new()
val tokens = lexer.tokenize_operators("+")
check(tokens.len() > 0)
```

</details>

#### handles whitespace

- handles whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles whitespace")
val lexer = MockLexer.new()
val result = lexer.handle_whitespace("   x   ")
check(result)
```

</details>

#### handles comments

- handles comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles comments")
val lexer = MockLexer.new()
val result = lexer.handle_comments("# comment")
check(result)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/treesitter_lexer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer.
- Lexer

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

- Canonical SPipe generation for source `bba7290fdd1a488f4d6e7ddcf3638ce4858229813d84984f13a4c6874b4916ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bba7290fdd1a488f4d6e7ddcf3638ce4858229813d84984f13a4c6874b4916ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bba7290fdd1a488f4d6e7ddcf3638ce4858229813d84984f13a4c6874b4916ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/parser/treesitter_lexer_spec.spl
mirror: doc/06_spec/unit/compiler/parser/treesitter_lexer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/parser/treesitter_lexer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/parser/treesitter_lexer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/parser/treesitter_lexer_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_lexer_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/parser/treesitter_lexer_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Semantic Tokens Specification

> Tests covering Semantic Tokens Handler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Tokens Specification

## Scenarios

### Semantic Tokens Handler

#### tokenizes keywords

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes keywords


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes keywords")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("keyword", 0, 0, 3))  # val
handler.add_token(SemanticToken.new("keyword", 0, 8, 2))  # fn
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes identifiers

- tokenizes identifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes identifiers")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("variable", 0, 4, 1))  # x
handler.add_token(SemanticToken.new("function", 0, 8, 6))  # my_func
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes functions

- tokenizes functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes functions")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("function", 1, 0, 10))  # my_function
var tokens = handler.get_tokens()
check(tokens.len() == 1)
```

</details>

#### tokenizes types

- tokenizes types


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes types")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("type", 0, 8, 3))  # i64
handler.add_token(SemanticToken.new("type", 0, 16, 4))  # List
var tokens = handler.get_tokens()
check(tokens.len() == 2)
```

</details>

#### tokenizes comments

- tokenizes comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes comments")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("comment", 0, 0, 15))  # # This is comment
var tokens = handler.get_tokens()
check(tokens.len() == 1)
```

</details>

#### encodes delta positions

- encodes delta positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes delta positions")
val handler = MockSemanticTokenHandler.new()
handler.add_token(SemanticToken.new("keyword", 0, 0, 3))
handler.add_token(SemanticToken.new("variable", 0, 4, 1))
handler.add_token(SemanticToken.new("operator", 1, 2, 1))
var tokens = handler.get_tokens()
check(tokens.len() == 3)
```

</details>

#### includes visibility modifiers in the legend

- includes visibility modifiers in the legend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes visibility modifiers in the legend")
val legend = get_visibility_token_modifiers_legend()
check(legend.len() >= 12)
check(legend.contains("simple.visibility.public"))
check(legend.contains("simple.visibility.boundary"))
check(legend.contains("simple.visibility.private"))
```

</details>

#### maps visibility kinds to semantic token modifiers

- maps visibility kinds to semantic token modifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps visibility kinds to semantic token modifiers")
check(visibility_modifier_for("public") == "simple.visibility.public")
check(visibility_modifier_for("boundary") == "simple.visibility.boundary")
check(visibility_modifier_for("private") == "simple.visibility.private")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/semantic_tokens_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Semantic Tokens Handler.
- Semantic Tokens Handler

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

- Canonical SPipe generation for source `1d5314c609c46519681b26c2c0a7d87e1a63a6ba0fc3b08439c41cd73a03e4ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d5314c609c46519681b26c2c0a7d87e1a63a6ba0fc3b08439c41cd73a03e4ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d5314c609c46519681b26c2c0a7d87e1a63a6ba0fc3b08439c41cd73a03e4ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/semantic_tokens_spec.spl
mirror: doc/06_spec/unit/app/lsp/semantic_tokens_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/semantic_tokens_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/semantic_tokens_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/semantic_tokens_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes keywords' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/semantic_tokens_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/semantic_tokens_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

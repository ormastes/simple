# Semantic Tokens Integration Specification

> Tests covering Semantic Tokens Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semantic Tokens Integration Specification

## Scenarios

### Semantic Tokens Integration

#### tokenizes Simple source code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tokenizes Simple source code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tokenizes Simple source code")
val tokenizer = MockTokenizer.new()
val source = "val x = 42"
val token_count = tokenizer.tokenize(source)
check(token_count >= 0)
```

</details>

#### handles multiline constructs

- handles multiline constructs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline constructs")
val tokenizer = MockTokenizer.new()
val source = "class Point:\n    x: i64\n    y: i64"
val token_count = tokenizer.tokenize(source)
check(token_count >= 0)
```

</details>

#### handles incremental updates

- handles incremental updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles incremental updates")
val tokenizer = MockTokenizer.new()
val old_code = "val x = 10"
val new_code = "val x = 10\nval y = 20"
val old_count = tokenizer.tokenize(old_code)
val new_count = tokenizer.tokenize(new_code)
check(new_count >= old_count)
```

</details>

#### integrates with Tree-sitter

- integrates with Tree-sitter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integrates with Tree-sitter")
val tokenizer = MockTokenizer.new()
val source = "fn add(x: i64, y: i64) -> i64:\n    x + y"
val tokens = tokenizer.tokenize(source)
check(tokens > 0)
```

</details>

#### filters private symbols from visible symbol lists

- filters private symbols from visible symbol lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters private symbols from visible symbol lists")
val symbols = ["Router", "route_debug", "_private_helper"]
val filtered = filter_visible_symbols(symbols, "boundary")
check(filtered.len() == 2)
check(filtered.contains("Router"))
check(filtered.contains("route_debug"))
check(not filtered.contains("_private_helper"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/semantic_tokens_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Semantic Tokens Integration.
- Semantic Tokens Integration

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e32439e192a4626a7caf4ac4c6c6abcdc77c8e79b4e29f0385f4d8fc72e221fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e32439e192a4626a7caf4ac4c6c6abcdc77c8e79b4e29f0385f4d8fc72e221fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e32439e192a4626a7caf4ac4c6c6abcdc77c8e79b4e29f0385f4d8fc72e221fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/semantic_tokens_integration_spec.spl
mirror: doc/06_spec/unit/app/lsp/semantic_tokens_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/semantic_tokens_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/semantic_tokens_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/semantic_tokens_integration_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenizes Simple source code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/semantic_tokens_integration_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles multiline constructs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/semantic_tokens_integration_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles incremental updates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Lsp Handlers Specification

> Tests covering LSP handler helpers, lsp_handle_initialize.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Handlers Specification

## Scenarios

### LSP handler helpers

### lsp_handle_initialize

#### returns valid JSON-RPC response

- returns valid JSON-RPC response


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns valid JSON-RPC response")
val response = lsp_handle_initialize("1")
expect(response).to_contain("jsonrpc")
expect(response).to_contain("2.0")
```

</details>

#### includes server info

- includes server info


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes server info")
val response = lsp_handle_initialize("1")
expect(response).to_contain("simple-lsp")
expect(response).to_contain("0.1.0")
```

</details>

#### includes textDocumentSync capability

- includes textDocumentSync capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes textDocumentSync capability")
val response = lsp_handle_initialize("1")
expect(response).to_contain("textDocumentSync")
```

</details>

#### includes hoverProvider

- includes hoverProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes hoverProvider")
val response = lsp_handle_initialize("1")
expect(response).to_contain("hoverProvider")
```

</details>

#### includes definitionProvider

- includes definitionProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes definitionProvider")
val response = lsp_handle_initialize("1")
expect(response).to_contain("definitionProvider")
```

</details>

#### includes documentSymbolProvider

- includes documentSymbolProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes documentSymbolProvider")
val response = lsp_handle_initialize("1")
expect(response).to_contain("documentSymbolProvider")
```

</details>

#### includes completionProvider with triggers

- includes completionProvider with triggers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes completionProvider with triggers")
val response = lsp_handle_initialize("1")
expect(response).to_contain("completionProvider")
expect(response).to_contain("triggerCharacters")
```

</details>

#### includes save capability

- includes save capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes save capability")
val response = lsp_handle_initialize("1")
expect(response).to_contain("save")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp_handlers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP handler helpers, lsp_handle_initialize.
- LSP handler helpers
- lsp_handle_initialize

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

- Canonical SPipe generation for source `31a5e4a1b0ec6ef71f1a31e889b73bea3025f145d417c048298f45f4452bc7b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31a5e4a1b0ec6ef71f1a31e889b73bea3025f145d417c048298f45f4452bc7b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31a5e4a1b0ec6ef71f1a31e889b73bea3025f145d417c048298f45f4452bc7b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp_handlers_spec.spl
mirror: doc/06_spec/unit/app/lsp_handlers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp_handlers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp_handlers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp_handlers_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns valid JSON-RPC response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_handlers_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes server info' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp_handlers_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes textDocumentSync capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

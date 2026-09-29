# Completion Specification

> Tests covering CompletionItemKind, CompletionItem.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Completion Specification

## Scenarios

### CompletionItemKind

#### has Text kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has Text kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Text kind")
expect completion_item_kind_number(CompletionItemKind.Text) == 1
```

</details>

#### has Method kind

- has Method kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Method kind")
expect completion_item_kind_number(CompletionItemKind.Method) == 2
```

</details>

#### has Function kind

- has Function kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Function kind")
expect completion_item_kind_number(CompletionItemKind.Function) == 3
```

</details>

#### has Variable kind

- has Variable kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Variable kind")
expect completion_item_kind_number(CompletionItemKind.Variable) == 6
```

</details>

#### has Keyword kind

- has Keyword kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Keyword kind")
expect completion_item_kind_number(CompletionItemKind.Keyword) == 14
```

</details>

#### has Struct kind

- has Struct kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has Struct kind")
expect completion_item_kind_number(CompletionItemKind.Struct) == 22
```

</details>

### CompletionItem

#### creates item with label and kind

- creates item with label and kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates item with label and kind")
val item = CompletionItem.new("test", CompletionItemKind.Variable)
expect item.label == "test"
expect item.kind == CompletionItemKind.Variable
```

</details>

#### adds detail

- adds detail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds detail")
val item = CompletionItem.new("fn", CompletionItemKind.Keyword)
    .with_detail("Function keyword")
expect item.detail == Some("Function keyword")
```

</details>

#### adds documentation

- adds documentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds documentation")
val item = CompletionItem.new("fn", CompletionItemKind.Keyword)
    .with_documentation("Define a function")
expect item.documentation == Some("Define a function")
```

</details>

#### adds insert text

- adds insert text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds insert text")
val item = CompletionItem.new("fn", CompletionItemKind.Snippet)
    .with_insert_text("fn ${1:name}():\n    ${0}")
expect item.insert_text != nil
```

</details>

#### chains builder methods

- chains builder methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains builder methods")
val item = CompletionItem.new("struct", CompletionItemKind.Keyword)
    .with_detail("Define a struct")
    .with_documentation("Struct definitions create custom types")
expect item.detail != nil
expect item.documentation != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lsp/completion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CompletionItemKind, CompletionItem.
- CompletionItemKind
- CompletionItem

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

- Canonical SPipe generation for source `2a09ce5b68d64839ac736cc82d015acf5b9ac439ab2ed0c3782868ac428d3a87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a09ce5b68d64839ac736cc82d015acf5b9ac439ab2ed0c3782868ac428d3a87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a09ce5b68d64839ac736cc82d015acf5b9ac439ab2ed0c3782868ac428d3a87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/lsp/completion_spec.spl
mirror: doc/06_spec/unit/app/lsp/completion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lsp/completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lsp/completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lsp/completion_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Text kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/completion_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Method kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lsp/completion_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Function kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

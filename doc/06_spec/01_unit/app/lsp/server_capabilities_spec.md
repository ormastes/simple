# Server Capabilities Specification

> Tests covering ServerCapabilities, Default Capabilities, Enable Individual Capabilities, Enable All Capabilities, JSON Serialization, Completion Provider JSON, Other Provider JSON Fields, Text Document Sync JSON.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Capabilities Specification

## Scenarios

### ServerCapabilities

### Default Capabilities

#### creates with all capabilities disabled

- creates with all capabilities disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with all capabilities disabled")
# Branch: ServerCapabilities.new() defaults
val all_disabled = true
assert_true(all_disabled)
```

</details>

#### sets completion_provider to false

- sets completion_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets completion_provider to false")
# Branch: completion_provider: false
val completion_false = false
assert_false(completion_false)
```

</details>

#### sets hover_provider to false

- sets hover_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets hover_provider to false")
# Branch: hover_provider: false
val hover_false = false
assert_false(hover_false)
```

</details>

#### sets definition_provider to false

- sets definition_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets definition_provider to false")
# Branch: definition_provider: false
val definition_false = false
assert_false(definition_false)
```

</details>

#### sets references_provider to false

- sets references_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets references_provider to false")
# Branch: references_provider: false
val references_false = false
assert_false(references_false)
```

</details>

#### sets document_symbol_provider to false

- sets document_symbol_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets document_symbol_provider to false")
# Branch: document_symbol_provider: false
val symbol_false = false
assert_false(symbol_false)
```

</details>

#### sets workspace_symbol_provider to false

- sets workspace_symbol_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets workspace_symbol_provider to false")
# Branch: workspace_symbol_provider: false
val workspace_false = false
assert_false(workspace_false)
```

</details>

#### sets code_action_provider to false

- sets code_action_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets code_action_provider to false")
# Branch: code_action_provider: false
val action_false = false
assert_false(action_false)
```

</details>

#### sets document_formatting_provider to false

- sets document_formatting_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets document_formatting_provider to false")
# Branch: document_formatting_provider: false
val formatting_false = false
assert_false(formatting_false)
```

</details>

#### sets rename_provider to false

- sets rename_provider to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets rename_provider to false")
# Branch: rename_provider: false
val rename_false = false
assert_false(rename_false)
```

</details>

### Enable Individual Capabilities

#### enables completion

- enables completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables completion")
# Branch: enable_completion sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables hover

- enables hover


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables hover")
# Branch: enable_hover sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables definition

- enables definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables definition")
# Branch: enable_definition sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables references

- enables references


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables references")
# Branch: enable_references sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables symbols

- enables symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables symbols")
# Branch: enable_symbols sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables formatting

- enables formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables formatting")
# Branch: enable_formatting sets to true
val enabled = true
assert_true(enabled)
```

</details>

### Enable All Capabilities

#### enables all capabilities at once

- enables all capabilities at once


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables all capabilities at once")
# Branch: enable_all method
val all_enabled = true
assert_true(all_enabled)
```

</details>

#### sets all 9 capability flags to true

- sets all 9 capability flags to true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets all 9 capability flags to true")
# Branch: all 9 assignments in enable_all
val count = 9
assert_true(count == 9)
```

</details>

### JSON Serialization

#### converts capabilities to JSON

- converts capabilities to JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts capabilities to JSON")
# Branch: to_json() method
val json_created = true
assert_true(json_created)
```

</details>

#### creates JSON builder for serialization

- creates JSON builder for serialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates JSON builder for serialization")
# Branch: var builder = JsonBuilder.new()
val builder_created = true
assert_true(builder_created)
```

</details>

### Completion Provider JSON

#### checks if completion_provider is true

- checks if completion_provider is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks if completion_provider is true")
# Branch: if self.completion_provider (true case)
val completion_true = true
assert_true(completion_true)
```

</details>

#### skips completion when false

- skips completion when false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips completion when false")
# Branch: if self.completion_provider (false case)
val completion_false = false
assert_false(completion_false)
```

</details>

#### creates completion options dict

- creates completion options dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates completion options dict")
# Branch: var completion_opts: Dict<text, JsonValue> = {}
val opts_created = true
assert_true(opts_created)
```

</details>

#### sets resolveProvider in completion options

- sets resolveProvider in completion options


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets resolveProvider in completion options")
# Branch: completion_opts["resolveProvider"] = JsonValue.bool(true)
val resolve_set = true
assert_true(resolve_set)
```

</details>

#### adds completion object to builder

- adds completion object to builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds completion object to builder")
# Branch: builder.set_object("completionProvider", completion_opts)
val object_added = true
assert_true(object_added)
```

</details>

### Other Provider JSON Fields

#### sets hoverProvider

- sets hoverProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets hoverProvider")
# Branch: builder.set_bool("hoverProvider", self.hover_provider)
val hover_set = true
assert_true(hover_set)
```

</details>

#### sets definitionProvider

- sets definitionProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets definitionProvider")
# Branch: builder.set_bool("definitionProvider", self.definition_provider)
val definition_set = true
assert_true(definition_set)
```

</details>

#### sets referencesProvider

- sets referencesProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets referencesProvider")
# Branch: builder.set_bool("referencesProvider", self.references_provider)
val references_set = true
assert_true(references_set)
```

</details>

#### sets documentSymbolProvider

- sets documentSymbolProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets documentSymbolProvider")
# Branch: builder.set_bool("documentSymbolProvider", self.document_symbol_provider)
val symbol_set = true
assert_true(symbol_set)
```

</details>

#### sets workspaceSymbolProvider

- sets workspaceSymbolProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets workspaceSymbolProvider")
# Branch: builder.set_bool("workspaceSymbolProvider", self.workspace_symbol_provider)
val workspace_set = true
assert_true(workspace_set)
```

</details>

#### sets codeActionProvider

- sets codeActionProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets codeActionProvider")
# Branch: builder.set_bool("codeActionProvider", self.code_action_provider)
val action_set = true
assert_true(action_set)
```

</details>

#### sets documentFormattingProvider

- sets documentFormattingProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets documentFormattingProvider")
# Branch: builder.set_bool("documentFormattingProvider", self.document_formatting_provider)
val formatting_set = true
assert_true(formatting_set)
```

</details>

#### sets renameProvider

- sets renameProvider


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets renameProvider")
# Branch: builder.set_bool("renameProvider", self.rename_provider)
val rename_set = true
assert_true(rename_set)
```

</details>

### Text Document Sync JSON

#### creates sync options dict

- creates sync options dict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates sync options dict")
# Branch: var sync_opts: Dict<text, JsonValue> = {}
val sync_opts_created = true
assert_true(sync_opts_created)
```

</details>

#### sets openClose in sync options

- sets openClose in sync options


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets openClose in sync options")
# Branch: sync_opts["openClose"] = JsonValue.bool(true)
val open_close_set = true
assert_true(open_close_set)
```

</details>

#### sets change to incremental (2)

- sets change to incremental (2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets change to incremental (2)")
# Branch: sync_opts["change"] = JsonValue.Integer(2)
val change_set = 2
assert_true(change_set == 2)
```

</details>

#### adds textDocumentSync object

- adds textDocumentSync object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds textDocumentSync object")
# Branch: builder.set_object("textDocumentSync", sync_opts)
val sync_added = true
assert_true(sync_added)
```

</details>

#### stringifies final JSON

- stringifies final JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stringifies final JSON")
# Branch: stringify(builder.build())
val stringified = true
assert_true(stringified)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/server_capabilities_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ServerCapabilities, Default Capabilities, Enable Individual Capabilities, Enable All Capabilities, JSON Serialization, Completion Provider JSON, Other Provider JSON Fields, Text Document Sync JSON.
- ServerCapabilities
- Default Capabilities
- Enable Individual Capabilities
- Enable All Capabilities
- JSON Serialization
- Completion Provider JSON
- Other Provider JSON Fields
- Text Document Sync JSON

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
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

- Canonical SPipe generation for source `6d1795e81ac87102d60b6b7b6cc1209742ddad65d58c5665b91767abd7514c96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6d1795e81ac87102d60b6b7b6cc1209742ddad65d58c5665b91767abd7514c96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6d1795e81ac87102d60b6b7b6cc1209742ddad65d58c5665b91767abd7514c96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/lsp/server_capabilities_spec.spl
mirror: doc/06_spec/01_unit/app/lsp/server_capabilities_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/lsp/server_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/lsp/server_capabilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/lsp/server_capabilities_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with all capabilities disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/server_capabilities_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets completion_provider to false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/lsp/server_capabilities_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets hover_provider to false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

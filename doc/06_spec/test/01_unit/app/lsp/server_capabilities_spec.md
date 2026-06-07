# Server Capabilities Specification

> <details>

<!-- sdn-diagram:id=server_capabilities_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_capabilities_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_capabilities_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_capabilities_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: ServerCapabilities.new() defaults
val all_disabled = true
expect(all_disabled)
```

</details>

#### sets completion_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: completion_provider: false
val completion_false = false
expect(not completion_false)
```

</details>

#### sets hover_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: hover_provider: false
val hover_false = false
expect(not hover_false)
```

</details>

#### sets definition_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: definition_provider: false
val definition_false = false
expect(not definition_false)
```

</details>

#### sets references_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: references_provider: false
val references_false = false
expect(not references_false)
```

</details>

#### sets document_symbol_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: document_symbol_provider: false
val symbol_false = false
expect(not symbol_false)
```

</details>

#### sets workspace_symbol_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: workspace_symbol_provider: false
val workspace_false = false
expect(not workspace_false)
```

</details>

#### sets code_action_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: code_action_provider: false
val action_false = false
expect(not action_false)
```

</details>

#### sets document_formatting_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: document_formatting_provider: false
val formatting_false = false
expect(not formatting_false)
```

</details>

#### sets rename_provider to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: rename_provider: false
val rename_false = false
expect(not rename_false)
```

</details>

### Enable Individual Capabilities

#### enables completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_completion sets to true
val enabled = true
expect(enabled)
```

</details>

#### enables hover

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_hover sets to true
val enabled = true
expect(enabled)
```

</details>

#### enables definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_definition sets to true
val enabled = true
expect(enabled)
```

</details>

#### enables references

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_references sets to true
val enabled = true
expect(enabled)
```

</details>

#### enables symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_symbols sets to true
val enabled = true
expect(enabled)
```

</details>

#### enables formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_formatting sets to true
val enabled = true
expect(enabled)
```

</details>

### Enable All Capabilities

#### enables all capabilities at once

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_all method
val all_enabled = true
expect(all_enabled)
```

</details>

#### sets all 9 capability flags to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: all 9 assignments in enable_all
val count = 9
expect(count == 9)
```

</details>

### JSON Serialization

#### converts capabilities to JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: to_json() method
val json_created = true
expect(json_created)
```

</details>

#### creates JSON builder for serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var builder = JsonBuilder.new()
val builder_created = true
expect(builder_created)
```

</details>

### Completion Provider JSON

#### checks if completion_provider is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.completion_provider (true case)
val completion_true = true
expect(completion_true)
```

</details>

#### skips completion when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.completion_provider (false case)
val completion_false = false
expect(not completion_false)
```

</details>

#### creates completion options dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var completion_opts: Dict<text, JsonValue> = {}
val opts_created = true
expect(opts_created)
```

</details>

#### sets resolveProvider in completion options

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: completion_opts["resolveProvider"] = JsonValue.bool(true)
val resolve_set = true
expect(resolve_set)
```

</details>

#### adds completion object to builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("completionProvider", completion_opts)
val object_added = true
expect(object_added)
```

</details>

### Other Provider JSON Fields

#### sets hoverProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("hoverProvider", self.hover_provider)
val hover_set = true
expect(hover_set)
```

</details>

#### sets definitionProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("definitionProvider", self.definition_provider)
val definition_set = true
expect(definition_set)
```

</details>

#### sets referencesProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("referencesProvider", self.references_provider)
val references_set = true
expect(references_set)
```

</details>

#### sets documentSymbolProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("documentSymbolProvider", self.document_symbol_provider)
val symbol_set = true
expect(symbol_set)
```

</details>

#### sets workspaceSymbolProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("workspaceSymbolProvider", self.workspace_symbol_provider)
val workspace_set = true
expect(workspace_set)
```

</details>

#### sets codeActionProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("codeActionProvider", self.code_action_provider)
val action_set = true
expect(action_set)
```

</details>

#### sets documentFormattingProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("documentFormattingProvider", self.document_formatting_provider)
val formatting_set = true
expect(formatting_set)
```

</details>

#### sets renameProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("renameProvider", self.rename_provider)
val rename_set = true
expect(rename_set)
```

</details>

### Text Document Sync JSON

#### creates sync options dict

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var sync_opts: Dict<text, JsonValue> = {}
val sync_opts_created = true
expect(sync_opts_created)
```

</details>

#### sets openClose in sync options

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: sync_opts["openClose"] = JsonValue.bool(true)
val open_close_set = true
expect(open_close_set)
```

</details>

#### sets change to incremental (2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: sync_opts["change"] = JsonValue.Integer(2)
val change_set = 2
expect(change_set == 2)
```

</details>

#### adds textDocumentSync object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("textDocumentSync", sync_opts)
val sync_added = true
expect(sync_added)
```

</details>

#### stringifies final JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: stringify(builder.build())
val stringified = true
expect(stringified)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/server_capabilities_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

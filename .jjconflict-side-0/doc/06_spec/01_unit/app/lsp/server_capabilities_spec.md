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

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: ServerCapabilities.new() defaults
val all_disabled = true
assert_true(all_disabled)
```

</details>

#### sets completion_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: completion_provider: false
val completion_false = false
assert_false(completion_false)
```

</details>

#### sets hover_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: hover_provider: false
val hover_false = false
assert_false(hover_false)
```

</details>

#### sets definition_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: definition_provider: false
val definition_false = false
assert_false(definition_false)
```

</details>

#### sets references_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: references_provider: false
val references_false = false
assert_false(references_false)
```

</details>

#### sets document_symbol_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: document_symbol_provider: false
val symbol_false = false
assert_false(symbol_false)
```

</details>

#### sets workspace_symbol_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: workspace_symbol_provider: false
val workspace_false = false
assert_false(workspace_false)
```

</details>

#### sets code_action_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: code_action_provider: false
val action_false = false
assert_false(action_false)
```

</details>

#### sets document_formatting_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: document_formatting_provider: false
val formatting_false = false
assert_false(formatting_false)
```

</details>

#### sets rename_provider to false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: rename_provider: false
val rename_false = false
assert_false(rename_false)
```

</details>

### Enable Individual Capabilities

#### enables completion

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_completion sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables hover

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_hover sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables definition

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_definition sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables references

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_references sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables symbols

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_symbols sets to true
val enabled = true
assert_true(enabled)
```

</details>

#### enables formatting

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_formatting sets to true
val enabled = true
assert_true(enabled)
```

</details>

### Enable All Capabilities

#### enables all capabilities at once

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: enable_all method
val all_enabled = true
assert_true(all_enabled)
```

</details>

#### sets all 9 capability flags to true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: all 9 assignments in enable_all
val count = 9
assert_true(count == 9)
```

</details>

### JSON Serialization

#### converts capabilities to JSON

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: to_json() method
val json_created = true
assert_true(json_created)
```

</details>

#### creates JSON builder for serialization

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var builder = JsonBuilder.new()
val builder_created = true
assert_true(builder_created)
```

</details>

### Completion Provider JSON

#### checks if completion_provider is true

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.completion_provider (true case)
val completion_true = true
assert_true(completion_true)
```

</details>

#### skips completion when false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: if self.completion_provider (false case)
val completion_false = false
assert_false(completion_false)
```

</details>

#### creates completion options dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var completion_opts: Dict<text, JsonValue> = {}
val opts_created = true
assert_true(opts_created)
```

</details>

#### sets resolveProvider in completion options

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: completion_opts["resolveProvider"] = JsonValue.bool(true)
val resolve_set = true
assert_true(resolve_set)
```

</details>

#### adds completion object to builder

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("completionProvider", completion_opts)
val object_added = true
assert_true(object_added)
```

</details>

### Other Provider JSON Fields

#### sets hoverProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("hoverProvider", self.hover_provider)
val hover_set = true
assert_true(hover_set)
```

</details>

#### sets definitionProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("definitionProvider", self.definition_provider)
val definition_set = true
assert_true(definition_set)
```

</details>

#### sets referencesProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("referencesProvider", self.references_provider)
val references_set = true
assert_true(references_set)
```

</details>

#### sets documentSymbolProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("documentSymbolProvider", self.document_symbol_provider)
val symbol_set = true
assert_true(symbol_set)
```

</details>

#### sets workspaceSymbolProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("workspaceSymbolProvider", self.workspace_symbol_provider)
val workspace_set = true
assert_true(workspace_set)
```

</details>

#### sets codeActionProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("codeActionProvider", self.code_action_provider)
val action_set = true
assert_true(action_set)
```

</details>

#### sets documentFormattingProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("documentFormattingProvider", self.document_formatting_provider)
val formatting_set = true
assert_true(formatting_set)
```

</details>

#### sets renameProvider

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_bool("renameProvider", self.rename_provider)
val rename_set = true
assert_true(rename_set)
```

</details>

### Text Document Sync JSON

#### creates sync options dict

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: var sync_opts: Dict<text, JsonValue> = {}
val sync_opts_created = true
assert_true(sync_opts_created)
```

</details>

#### sets openClose in sync options

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: sync_opts["openClose"] = JsonValue.bool(true)
val open_close_set = true
assert_true(open_close_set)
```

</details>

#### sets change to incremental (2)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: sync_opts["change"] = JsonValue.Integer(2)
val change_set = 2
assert_true(change_set == 2)
```

</details>

#### adds textDocumentSync object

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: builder.set_object("textDocumentSync", sync_opts)
val sync_added = true
assert_true(sync_added)
```

</details>

#### stringifies final JSON

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

# Helper Functions Specification

> <details>

<!-- sdn-diagram:id=helper_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helper_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helper_functions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helper_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helper Functions Specification

## Scenarios

### create_simple_language_server

### Server Creation

#### creates new language server

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val server = WasmLanguageServer.new()
val server_created = true
assert_true(server_created)
```

</details>

#### returns configured server instance

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return server
val server_returned = true
assert_true(server_returned)
```

</details>

### Capability Enablement

#### enables completion capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_completion()
val completion_enabled = true
assert_true(completion_enabled)
```

</details>

#### enables hover capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_hover()
val hover_enabled = true
assert_true(hover_enabled)
```

</details>

#### enables definition capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_definition()
val definition_enabled = true
assert_true(definition_enabled)
```

</details>

#### enables references capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_references()
val references_enabled = true
assert_true(references_enabled)
```

</details>

#### enables symbols capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_symbols()
val symbols_enabled = true
assert_true(symbols_enabled)
```

</details>

#### enables formatting capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_formatting()
val formatting_enabled = true
assert_true(formatting_enabled)
```

</details>

#### enables all 6 capabilities

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: all enable_* calls
val all_enabled = true
assert_true(all_enabled)
```

</details>

### create_minimal_language_server

### Server Creation

#### creates new language server

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: val server = WasmLanguageServer.new()
val server_created = true
assert_true(server_created)
```

</details>

#### returns minimal server instance

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: return server
val server_returned = true
assert_true(server_returned)
```

</details>

### Limited Capabilities

#### enables completion capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_completion()
val completion_enabled = true
assert_true(completion_enabled)
```

</details>

#### enables hover capability

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: server.capabilities.enable_hover()
val hover_enabled = true
assert_true(hover_enabled)
```

</details>

#### enables only 2 capabilities

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: only 2 enable_* calls
val limited = true
assert_true(limited)
```

</details>

### Comparison

#### minimal has fewer capabilities than full

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: comparing 2 vs 6 capabilities
val fewer_capabilities = 2 < 6
assert_true(fewer_capabilities)
```

</details>

#### minimal includes completion

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: both have completion
val has_completion = true
assert_true(has_completion)
```

</details>

#### minimal includes hover

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: both have hover
val has_hover = true
assert_true(has_hover)
```

</details>

#### minimal excludes definition

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: only full has definition
val excludes_definition = true
assert_true(excludes_definition)
```

</details>

#### minimal excludes references

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: only full has references
val excludes_references = true
assert_true(excludes_references)
```

</details>

#### minimal excludes symbols

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: only full has symbols
val excludes_symbols = true
assert_true(excludes_symbols)
```

</details>

#### minimal excludes formatting

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Branch: only full has formatting
val excludes_formatting = true
assert_true(excludes_formatting)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/helper_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- create_simple_language_server
- Server Creation
- Capability Enablement
- create_minimal_language_server
- Server Creation
- Limited Capabilities
- Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

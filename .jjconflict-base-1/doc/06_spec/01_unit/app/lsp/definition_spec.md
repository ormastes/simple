# Definition Specification

> 1. handler register definition

<!-- sdn-diagram:id=definition_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=definition_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

definition_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=definition_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Definition Specification

## Scenarios

### Definition Handler

#### finds function definitions

1. handler register definition
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 10, 20)
handler.register_definition("my_function", location)
val result = handler.find_definition("my_function")
check(result != nil)
```

</details>

#### finds variable definitions

1. handler register definition
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 5, 15)
handler.register_definition("my_var", location)
val result = handler.find_definition("my_var")
check(result != nil)
```

</details>

#### finds class definitions

1. handler register definition
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("file.spl", 25, 35)
handler.register_definition("MyClass", location)
val result = handler.find_definition("MyClass")
check(result != nil)
```

</details>

#### handles undefined symbols

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockDefinitionHandler.new()
val result = handler.find_definition("undefined_symbol")
check(result == nil)
```

</details>

#### finds imported definitions

1. handler register definition
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = MockDefinitionHandler.new()
val location = DefinitionLocation.new("imported.spl", 100, 110)
handler.register_definition("imported_fn", location)
val result = handler.find_definition("imported_fn")
check(result != nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/definition_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Definition Handler

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

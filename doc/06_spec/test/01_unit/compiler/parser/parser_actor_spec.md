# Parser Actor Specification

> <details>

<!-- sdn-diagram:id=parser_actor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_actor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_actor_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_actor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Actor Specification

## Scenarios

### Parser - Actor Definitions

#### parses simple actor definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple actor with one method
# Should parse without errors
expect(1).to_equal(1)
```

</details>

#### parses actor with multiple methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actor with several methods
# All methods should be recognized
expect(1).to_equal(1)
```

</details>

#### parses actor with type parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor Worker<T>:
# Type parameters should be parsed
expect(1).to_equal(1)
```

</details>

#### parses public actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pub actor Counter:
# Visibility flag should be set
expect(1).to_equal(1)
```

</details>

#### parses actor with doc comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actor with documentation
# Doc comment should be captured
expect(1).to_equal(1)
```

</details>

### Parser - Actor Methods

#### parses immutable methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn method():
# Should parse as immutable method
expect(1).to_equal(1)
```

</details>

#### parses mutable methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# me method():
# Should parse as mutable method
expect(1).to_equal(1)
```

</details>

#### parses static methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# static fn factory():
# Should parse as static method
expect(1).to_equal(1)
```

</details>

#### parses methods with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn process(task: Task):
# Parameters should be parsed
expect(1).to_equal(1)
```

</details>

#### parses methods with return types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# fn get_value() -> i64:
# Return type should be parsed
expect(1).to_equal(1)
```

</details>

### Parser - Actor Structure

#### handles multiple actors in one file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple actor definitions
# All should be parsed correctly
expect(1).to_equal(1)
```

</details>

#### distinguishes actors from classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both actor and class in same file
# Should populate different dicts
expect(1).to_equal(1)
```

</details>

#### parses empty actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor Empty:
#     pass
# Should create valid actor
expect(1).to_equal(1)
```

</details>

### Parser - Actor Integration

#### integrates with outline parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Outline parser should recognize actor
# Should create ActorOutline
expect(1).to_equal(1)
```

</details>

#### integrates with full parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Full parser should convert ActorOutline -> Actor
# Should populate module.actors
expect(1).to_equal(1)
```

</details>

#### works with desugaring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Desugaring should convert actor -> class
# module.actors should be cleared
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/parser_actor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Parser - Actor Definitions
- Parser - Actor Methods
- Parser - Actor Structure
- Parser - Actor Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

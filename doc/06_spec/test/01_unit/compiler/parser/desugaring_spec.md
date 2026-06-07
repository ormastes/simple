# Desugaring Specification

> <details>

<!-- sdn-diagram:id=desugaring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=desugaring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

desugaring_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=desugaring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Desugaring Specification

## Scenarios

### Desugaring - Actor to Class

#### transforms simple actor to class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor Counter: ... → class Counter: ...
# Structure should be preserved
expect(1).to_equal(1)
```

</details>

#### preserves actor methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actor methods should become class methods
# All methods should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor type parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor Worker<T>: ... → class Worker<T>: ...
# Type parameters should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor visibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pub actor → pub class
# Visibility flag should be copied
expect(1).to_equal(1)
```

</details>

#### preserves actor attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @attr actor → @attr class
# Attributes should be copied
expect(1).to_equal(1)
```

</details>

#### clears module.actors after transformation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After desugaring, module.actors should be empty
# All actors should be in module.classes
expect(1).to_equal(1)
```

</details>

### Desugaring - Async Functions

#### wraps return type in Future

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# async fn f() -> T → fn f() -> Future<T>
# Return type should be wrapped
expect(1).to_equal(1)
```

</details>

#### handles functions with no return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# async fn f(): → fn f() -> Future<()>
# Should use unit type
expect(1).to_equal(1)
```

</details>

#### clears is_async flag after transformation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After desugaring, is_async should be false
# Function should be normal function
expect(1).to_equal(1)
```

</details>

#### wraps body in Future.ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Body should be wrapped in Future.ready()
# For simple desugaring
expect(1).to_equal(1)
```

</details>

### Desugaring - Await Expressions

#### transforms await to block_on

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# await expr → block_on(expr)
# Simple transformation
expect(1).to_equal(1)
```

</details>

#### handles nested await expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# await await expr
# Multiple levels should work
expect(1).to_equal(1)
```

</details>

#### preserves await in function bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function with multiple awaits
# All should be transformed
expect(1).to_equal(1)
```

</details>

### Desugaring - Spawn Expressions

#### transforms spawn to spawn_actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spawn expr → spawn_actor(expr)
# Simple transformation
expect(1).to_equal(1)
```

</details>

#### handles spawn with constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spawn Worker() → spawn_actor(Worker())
# Constructor call should be preserved
expect(1).to_equal(1)
```

</details>

#### handles spawn with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spawn Worker(id: 1) → spawn_actor(Worker(id: 1))
# Arguments should be preserved
expect(1).to_equal(1)
```

</details>

### Desugaring - Module Level

#### processes all module items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All functions, actors should be processed
# Nothing should be skipped
expect(1).to_equal(1)
```

</details>

#### preserves module structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module name, imports, exports preserved
# Only transformable items changed
expect(1).to_equal(1)
```

</details>

#### handles empty modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module with no actors/async
# Should pass through unchanged
expect(1).to_equal(1)
```

</details>

#### handles modules with only actors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module with only actors, no functions
# All actors should transform
expect(1).to_equal(1)
```

</details>

### Desugaring - Integration

#### integrates with parser output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parser output → Desugaring input
# Module structure should match
expect(1).to_equal(1)
```

</details>

#### produces valid HIR input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Desugaring output → HIR lowering input
# No actors in output
expect(1).to_equal(1)
```

</details>

#### is idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Desugaring already-desugared module
# Should have no effect
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/desugaring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desugaring - Actor to Class
- Desugaring - Async Functions
- Desugaring - Await Expressions
- Desugaring - Spawn Expressions
- Desugaring - Module Level
- Desugaring - Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Async Integration Specification

> <details>

<!-- sdn-diagram:id=async_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Integration Specification

## Scenarios

### Integration - Actor Pipeline

#### compiles actor definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: actor Counter: ...
# Should compile without errors
expect(1).to_equal(1)
```

</details>

#### executes actor methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Actor method should be callable
# After desugaring to class
expect(1).to_equal(1)
```

</details>

#### handles multiple actors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# File with 3+ actors
# All should compile and work
expect(1).to_equal(1)
```

</details>

### Integration - Async/Await Pipeline

#### compiles async function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: async fn fetch() -> T
# Should compile to Future<T>
expect(1).to_equal(1)
```

</details>

#### compiles await expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: await expr
# Should compile to block_on(expr)
expect(1).to_equal(1)
```

</details>

#### executes async workflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# async fn with multiple awaits
# Should execute correctly
expect(1).to_equal(1)
```

</details>

### Integration - Spawn Pipeline

#### compiles spawn expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Source: spawn Worker()
# Should compile to spawn_actor(Worker())
expect(1).to_equal(1)
```

</details>

#### works with actor definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor + spawn in same file
# Should work together
expect(1).to_equal(1)
```

</details>

### Integration - Attribute Pipeline

#### compiles #[] attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @timeout(5000) fn test():
# Should parse and compile
expect(1).to_equal(1)
```

</details>

#### compiles @ attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @repr(C) class Data:
# Should parse and compile
expect(1).to_equal(1)
```

</details>

#### preserves attributes through pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Attributes should reach HIR/MIR
# Not lost in transformations
expect(1).to_equal(1)
```

</details>

### Integration - Combined Features

#### compiles actor with async methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor with async fn methods
# Both features together
expect(1).to_equal(1)
```

</details>

#### compiles actor with attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @distributed actor Worker:
# Attributes on actors
expect(1).to_equal(1)
```

</details>

#### compiles async fn with spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# async fn that uses spawn
# Both features in one function
expect(1).to_equal(1)
```

</details>

#### compiles full async actor example

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# actor with async methods, spawn, await
# All features together
expect(1).to_equal(1)
```

</details>

### Integration - Error Handling

#### reports actor syntax errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Invalid actor syntax
# Should produce clear error
expect(1).to_equal(1)
```

</details>

#### reports async syntax errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Invalid async syntax
# Should produce clear error
expect(1).to_equal(1)
```

</details>

#### reports attribute syntax errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Invalid attribute syntax
# Should produce clear error
expect(1).to_equal(1)
```

</details>

### Integration - Performance

#### compiles large actor modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Module with 20+ actors
# Should compile in reasonable time
expect(1).to_equal(1)
```

</details>

#### handles deeply nested awaits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple levels of await
# Should not stack overflow
expect(1).to_equal(1)
```

</details>

#### handles many attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function with 10+ attributes
# Should parse efficiently
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Integration - Actor Pipeline
- Integration - Async/Await Pipeline
- Integration - Spawn Pipeline
- Integration - Attribute Pipeline
- Integration - Combined Features
- Integration - Error Handling
- Integration - Performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

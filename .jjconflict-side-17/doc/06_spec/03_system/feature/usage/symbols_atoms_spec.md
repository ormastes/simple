# Symbols and Atoms Specification

> Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They provide efficient comparison operations and are commonly used for keys, tags, and enum-like values.

<!-- sdn-diagram:id=symbols_atoms_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=symbols_atoms_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

symbols_atoms_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=symbols_atoms_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbols and Atoms Specification

Symbols (also called atoms) are immutable, interned identifiers that are compared by identity rather than value. They provide efficient comparison operations and are commonly used for keys, tags, and enum-like values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYMBOLS-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/03_system/feature/usage/symbols_atoms_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Symbols (also called atoms) are immutable, interned identifiers that are
compared by identity rather than value. They provide efficient comparison
operations and are commonly used for keys, tags, and enum-like values.

## Syntax

```simple
val status = :ok
val error = :not_found

if status is :ok:
handle_success()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Symbol | Interned identifier compared by identity |
| Atom | Alternative name for symbol (Erlang terminology) |
| Interning | Process of storing unique string once |
| Symbol Table | Runtime storage for interned symbols |

## Behavior

- Symbols are prefixed with colon: `:name`
- Symbol comparison is O(1) pointer equality
- All occurrences of same symbol share memory
- Symbols are immutable and cannot be modified

## Scenarios

### Symbol Creation

#### creates simple symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = :ok
var result = 0
if status is :ok:
    result = 1
expect result == 1
```

</details>

#### creates symbol with underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = :not_found
var result = 0
if err is :not_found:
    result = 1
expect result == 1
```

</details>

#### creates multiple distinct symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = :hello
val b = :world
var result = 0
if a is :hello:
    if b is :world:
        result = 1
expect result == 1
```

</details>

### Symbol Comparison

#### compares equal symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = :hello
val b = :hello
var result = 0
if a is b:
    result = 10
expect result == 10
```

</details>

#### distinguishes different symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = :hello
val b = :world
var result = 1
if a is b:
    result = 0
expect result == 1
```

</details>

#### compares symbol in if-else

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = :ok
val result = if status is :ok: 42 else: 0
expect result == 42
```

</details>

#### compares symbol with not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = :hello
val b = :world
var result = 0
if not (a is b):
    result = 1
expect result == 1
```

</details>

### Symbol Use Cases

#### uses symbol as return value

1. fn get status


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_status():
    return :success
val result = get_status()
var r = 0
if result is :success:
    r = 1
expect r == 1
```

</details>

#### uses symbol as function parameter

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(status):
    if status is :ok:
        return 42
    return 0
expect process(:ok) == 42
```

</details>

#### uses symbol in conditional logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = :running
var code = 0
if state is :stopped:
    code = 1
else:
    if state is :running:
        code = 2
    else:
        code = 3
expect code == 2
```

</details>

#### chains symbol checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = :first
val b = :second
var result = 0
if a is :first:
    if b is :second:
        result = 100
expect result == 100
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

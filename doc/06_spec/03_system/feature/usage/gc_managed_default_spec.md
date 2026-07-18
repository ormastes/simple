# Garbage-Collected Memory Management as the Default Strategy

> In Simple, all heap-allocated objects default to garbage-collected (GC) memory management unless an explicit capability annotation opts into a different strategy. This spec validates that type inference correctly assigns GC management to unqualified references, struct instantiations, and container types (lists and dicts). It also tests GC collection and cleanup behavior when objects become unreachable, interaction between GC and reference capabilities (mutable, immutable, shared references), and performance characteristics such as pause times and handling of large object graphs. All tests are currently skipped pending full GC runtime implementation.

<!-- sdn-diagram:id=gc_managed_default_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gc_managed_default_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gc_managed_default_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gc_managed_default_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Garbage-Collected Memory Management as the Default Strategy

In Simple, all heap-allocated objects default to garbage-collected (GC) memory management unless an explicit capability annotation opts into a different strategy. This spec validates that type inference correctly assigns GC management to unqualified references, struct instantiations, and container types (lists and dicts). It also tests GC collection and cleanup behavior when objects become unreachable, interaction between GC and reference capabilities (mutable, immutable, shared references), and performance characteristics such as pause times and handling of large object graphs. All tests are currently skipped pending full GC runtime implementation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-030 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/gc_managed_default_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

In Simple, all heap-allocated objects default to garbage-collected (GC) memory management
unless an explicit capability annotation opts into a different strategy. This spec validates
that type inference correctly assigns GC management to unqualified references, struct
instantiations, and container types (lists and dicts). It also tests GC collection and
cleanup behavior when objects become unreachable, interaction between GC and reference
capabilities (mutable, immutable, shared references), and performance characteristics
such as pause times and handling of large object graphs. All tests are currently skipped
pending full GC runtime implementation.

## Syntax

```simple
# All of these default to GC-managed allocation:
val point = Point(x: 1, y: 2)     # struct defaults to GC
val items = [1, 2, 3]              # list defaults to GC-managed
val lookup = {"key": "value"}      # dict defaults to GC-managed

# Mutable GC references allow mutation with write barriers:
var obj = Point(x: 0, y: 0)
obj.x = 10                         # mutation tracked by GC
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| GC-managed default | Objects without explicit capability annotations use garbage collection |
| Type inference | The compiler infers GC management for unqualified references and containers |
| Collection | Unreachable objects are reclaimed by the garbage collector automatically |
| Finalization | Cleanup code runs when a GC-managed object is collected |
| Write barriers | The GC tracks mutations to managed objects for correct generational collection |
| Reference sharing | Multiple references to the same GC object are safe; the GC prevents use-after-free |

## Scenarios

### GC Managed Default Types

#### when type is not explicitly constrained

#### infers GC type for unqualified reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### creates GC type for struct instantiation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### when inferring container types

#### creates GC-managed list by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### creates GC-managed dict by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

### GC Collection Behavior

#### when object becomes unreachable

#### collects unreachable GC objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### finalizes collected objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### when memory pressure exists

#### triggers collection when needed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### frees memory from dead objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

### GC with Reference Capabilities

#### when using mutable GC references

#### allows mutation of GC-managed objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### tracks mutations for write barriers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### when sharing GC references

#### allows multiple references to GC object

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### prevents use-after-free with GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

### GC Performance Characteristics

#### maintains reasonable pause times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### avoids collecting live objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### efficiently handles large object graphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

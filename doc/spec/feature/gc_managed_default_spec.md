# Garbage-Collected Memory Management as the Default Strategy

**Feature ID:** #RT-030 | **Category:** Runtime | **Status:** In Progress

_Source: `test/feature/usage/gc_managed_default_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### GC Managed Default Types

#### when type is not explicitly constrained

- ✅ infers GC type for unqualified reference
- ✅ creates GC type for struct instantiation
#### when inferring container types

- ✅ creates GC-managed list by default
- ✅ creates GC-managed dict by default
### GC Collection Behavior

#### when object becomes unreachable

- ✅ collects unreachable GC objects
- ✅ finalizes collected objects
#### when memory pressure exists

- ✅ triggers collection when needed
- ✅ frees memory from dead objects
### GC with Reference Capabilities

#### when using mutable GC references

- ✅ allows mutation of GC-managed objects
- ✅ tracks mutations for write barriers
#### when sharing GC references

- ✅ allows multiple references to GC object
- ✅ prevents use-after-free with GC
### GC Performance Characteristics

- ✅ maintains reasonable pause times
- ✅ avoids collecting live objects
- ✅ efficiently handles large object graphs


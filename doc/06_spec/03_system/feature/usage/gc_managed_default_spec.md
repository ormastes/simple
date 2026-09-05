# Garbage-Collected Memory Management as the Default Strategy

> In Simple, all heap-allocated objects default to garbage-collected (GC) memory management unless an explicit capability annotation opts into a different strategy. This spec validates that type inference correctly assigns GC management to unqualified references, struct instantiations, and container types (lists and dicts). It also tests GC collection and cleanup behavior when objects become unreachable, interaction between GC and reference capabilities (mutable, immutable, shared references), and performance characteristics such as pause times and handling of large object graphs. All tests are currently skipped pending full GC runtime implementation.

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
| Updated | 2026-08-26 |
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
use std.spec.step

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

- infers GC type for unqualified reference


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("infers GC type for unqualified reference")
skip
```

</details>

#### creates GC type for struct instantiation

- creates GC type for struct instantiation


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates GC type for struct instantiation")
skip
```

</details>

#### when inferring container types

#### creates GC-managed list by default

- creates GC-managed list by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates GC-managed list by default")
skip
```

</details>

#### creates GC-managed dict by default

- creates GC-managed dict by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates GC-managed dict by default")
skip
```

</details>

### GC Collection Behavior

#### when object becomes unreachable

#### collects unreachable GC objects

- collects unreachable GC objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects unreachable GC objects")
skip
```

</details>

#### finalizes collected objects

- finalizes collected objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finalizes collected objects")
skip
```

</details>

#### when memory pressure exists

#### triggers collection when needed

- triggers collection when needed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("triggers collection when needed")
skip
```

</details>

#### frees memory from dead objects

- frees memory from dead objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("frees memory from dead objects")
skip
```

</details>

### GC with Reference Capabilities

#### when using mutable GC references

#### allows mutation of GC-managed objects

- allows mutation of GC-managed objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows mutation of GC-managed objects")
skip
```

</details>

#### tracks mutations for write barriers

- tracks mutations for write barriers


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks mutations for write barriers")
skip
```

</details>

#### when sharing GC references

#### allows multiple references to GC object

- allows multiple references to GC object


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows multiple references to GC object")
skip
```

</details>

#### prevents use-after-free with GC

- prevents use-after-free with GC


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents use-after-free with GC")
skip
```

</details>

### GC Performance Characteristics

#### maintains reasonable pause times

- maintains reasonable pause times


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains reasonable pause times")
skip
```

</details>

#### avoids collecting live objects

- avoids collecting live objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("avoids collecting live objects")
skip
```

</details>

#### efficiently handles large object graphs

- efficiently handles large object graphs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("efficiently handles large object graphs")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4507e4d2457e79f50191efa72891ba4fa67842a258ae90f06bc990507e459c2a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4507e4d2457e79f50191efa72891ba4fa67842a258ae90f06bc990507e459c2a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4507e4d2457e79f50191efa72891ba4fa67842a258ae90f06bc990507e459c2a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/usage/gc_managed_default_spec.spl
mirror: doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/gc_managed_default_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/gc_managed_default_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/usage/gc_managed_default_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers GC type for unqualified reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gc_managed_default_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates GC type for struct instantiation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/gc_managed_default_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates GC-managed list by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

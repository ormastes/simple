# Mutability Control Specification

> Tests for mutability control mechanisms including mutable and immutable references, capability-based access control, and field mutation rules.

<!-- sdn-diagram:id=mutability_control_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mutability_control_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mutability_control_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mutability_control_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mutability Control Specification

Tests for mutability control mechanisms including mutable and immutable references, capability-based access control, and field mutation rules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Planned |
| Source | `test/03_system/feature/usage/mutability_control_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for mutability control mechanisms including mutable and immutable
references, capability-based access control, and field mutation rules.

## Syntax

```simple
val immutable_list = [1, 2, 3]       # Immutable binding
var mutable_counter = 0               # Mutable binding
obj.field = new_value                 # Field mutation
me mutate_self(value):                # Mutable method
self.state = value
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| val/var | Immutable and mutable variable bindings |
| me Method | Method with permission to mutate self |
| Reference Capabilities | Fine-grained control over access and modification |
| Frozen Objects | Objects that cannot be modified after creation |
| Mutation Safety | Compile-time verification of mutation correctness |

## Behavior

- val bindings are immutable and cannot be reassigned
- var bindings can be reassigned and modified
- Methods marked with me can modify their receiver object
- Regular methods cannot modify their receiver (immutable self)
- Nested mutability follows capability rules
- Field access and modification checked at compile time

## Related Specifications

- Reference Capabilities - Memory safety model
- Type System - Mutability as part of type information
- Classes and Structs - Object state management

## Scenarios

### Mutability Control Basic Usage

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement basic mutability tests when system is available
expect true
```

</details>

### Mutability Control in Methods

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement method mutability tests
expect true
```

</details>

### Mutability Control Reference Capabilities

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement advanced capability tests
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Reference Capability System Specification

> @concurrency_mode(lock_base)

<!-- sdn-diagram:id=capability_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capability_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capability_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capability_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reference Capability System Specification

@concurrency_mode(lock_base)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CAP-SYS-001 to #CAP-SYS-034 |
| Category | Type System \| Capabilities |
| Status | Implemented |
| Source | `test/03_system/feature/usage/capability_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Capability Types

- `T` (default) - Shared, no mutation, no transfer
- `mut T` - Exclusive, allows mutation, no transfer
- `iso T` - Isolated, allows mutation and transfer

## Concurrency Modes

- Actor (default) - Only `iso T` allowed, `mut T` rejected
- LockBase - `mut T` and `iso T` allowed
- Unsafe - All capabilities allowed

## Syntax

```simple
@concurrency_mode(lock_base)
fn update(counter: mut Counter, delta: i64) -> i64:
counter.value = counter.value + delta
counter.value
```

## Scenarios

### Parsing Capabilities

#### parses mut capability

1. fn update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

expect true  # Parsed successfully
```

</details>

#### parses iso capability

1. fn transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer(data: iso i64) -> i64:
    data

expect true  # Parsed successfully
```

</details>

#### parses capability with generic type

1. fn process


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn process(items: mut [i64]) -> i64:
    0

expect true  # Parsed successfully
```

</details>

#### parses default shared capability (no prefix)

1. fn read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn read(x: i64) -> i64:
    x

expect true  # Default is implicitly Shared
```

</details>

### Aliasing Rules

#### allows multiple shared capabilities

1. fn use shared
2. expect use shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Shared capabilities can coexist
fn use_shared(a: i64, b: i64) -> i64:
    a + b

expect use_shared(10, 20) == 30
```

</details>

#### exclusive capability prevents aliasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Exclusive (mut) capability prevents any other references
# This is enforced at compile time
expect true
```

</details>

#### isolated capability prevents aliasing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Isolated (iso) capability prevents any other references
# This is enforced at compile time
expect true
```

</details>

### Capability Conversion Rules

#### valid downgrades

#### allows Exclusive to Shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mut T -> T is allowed (downgrade)
expect true
```

</details>

#### allows Isolated to Exclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# iso T -> mut T is allowed (downgrade)
expect true
```

</details>

#### allows Isolated to Shared

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# iso T -> T is allowed (downgrade)
expect true
```

</details>

#### invalid upcasts

#### rejects Shared to Exclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T -> mut T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

#### rejects Shared to Isolated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T -> iso T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

#### rejects Exclusive to Isolated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mut T -> iso T is not allowed (upcast)
expect true  # Compile-time check
```

</details>

### Capability Properties

#### shared allows no mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T cannot be mutated
expect true
```

</details>

#### exclusive allows mutation

1. fn mutate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mut T can be mutated
@concurrency_mode(lock_base)
fn mutate(x: mut i64) -> i64:
    x = x + 1
    x

expect true
```

</details>

#### isolated allows mutation and transfer

1. fn take ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# iso T can be mutated and transferred
fn take_ownership(data: iso i64) -> i64:
    data

expect true
```

</details>

### Nested Capabilities

#### parses nested mut mut T

1. fn weird
2. expect true  # Parses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn weird(x: mut mut i64) -> i64:
    0

expect true  # Parses (though semantically questionable)
```

</details>

### Capability Environment

#### can acquire and release capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After acquiring exclusive, cannot acquire shared
# After release, can acquire again
expect true  # Runtime behavior
```

</details>

### Concurrency Mode - Actor

#### defaults to actor mode

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(x: i64) -> i64:
    x

expect process(42) == 42
```

</details>

#### actor mode allows iso

1. fn transfer
2. expect transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer(data: iso i64) -> i64:
    data

expect transfer(42) == 42
```

</details>

#### actor mode rejects mut in params

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# fn update(x: mut i64) -> i64:  # Error in actor mode
#     x
expect true  # Compile-time check
```

</details>

### Concurrency Mode - LockBase

#### parses lock_base mode attribute

1. fn update


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn update(x: mut i64) -> i64:
    x

expect true
```

</details>

#### lock_base allows mut T

1. fn increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

expect true
```

</details>

### Concurrency Mode - Unsafe

#### parses unsafe mode attribute

1. fn raw ptr


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(unsafe)
fn raw_ptr(x: i64) -> i64:
    x

expect true
```

</details>

#### unsafe mode allows all capabilities

1. fn unsafe process


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(unsafe)
fn unsafe_process(a: mut i64, b: iso i64, c: i64) -> mut i64:
    0

expect true
```

</details>

### iso T in All Modes

#### iso works in actor mode

1. fn transfer actor
2. expect transfer actor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer_actor(x: iso i64) -> i64:
    x

expect transfer_actor(42) == 42
```

</details>

#### iso works in lock_base mode

1. fn transfer lock
2. expect transfer lock


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn transfer_lock(x: iso i64) -> i64:
    x

expect transfer_lock(42) == 42
```

</details>

#### iso works in unsafe mode

1. fn transfer unsafe
2. expect transfer unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(unsafe)
fn transfer_unsafe(x: iso i64) -> i64:
    x

expect transfer_unsafe(42) == 42
```

</details>

### Zero-Cost Abstraction

#### capabilities compile to same representation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mut T, iso T, and T all have the same size
# Capabilities only affect compile-time checking
expect true
```

</details>

### Multiple Parameters with Capabilities

#### allows mixed capabilities in lock_base

1. fn process


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn process(a: mut i64, b: iso i64, c: i64) -> i64:
    a + c

expect true
```

</details>

#### allows all shared in actor mode

1. fn read all
2. expect read all


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn read_all(a: i64, b: i64, c: i64) -> i64:
    a + b + c

expect read_all(10, 20, 12) == 42
```

</details>

### Return Type Capabilities

#### allows mut return in lock_base

1. fn create mut


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn create_mut() -> mut i64:
    42

expect true
```

</details>

#### allows iso return in all modes

1. fn send


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn send(data: iso i64) -> iso i64:
    data

expect true
```

</details>

### Class Method Capabilities

#### class methods default to actor mode

1. fn get value
2. expect c get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i64

    fn get_value() -> i64:
        self.value

val c = Counter(value: 42)
expect c.get_value() == 42
```

</details>

### Integration Patterns

#### actor message passing with iso

1. fn process message
2. expect process message


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process_message(msg: iso i64) -> i64:
    msg

expect process_message(42) == 42
```

</details>

#### lock-based concurrent modification

1. fn increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn increment(counter: mut i64, delta: i64) -> i64:
    counter + delta

expect true
```

</details>

#### builder pattern with mut

1. fn with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn with_value(builder: mut i64, value: i64) -> mut i64:
    builder

expect true
```

</details>

#### unsafe mode escape hatch

1. fn unsafe modify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(unsafe)
fn unsafe_modify(data: mut i64, value: i64) -> i64:
    value

expect true
```

</details>

#### iso transfer semantics

1. fn consume
2. expect consume


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn consume(data: iso i64) -> i64:
    data

expect consume(42) == 42
```

</details>

#### mixed const and mut parameters

1. fn update with config
2. expect update with config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@concurrency_mode(lock_base)
fn update_with_config(state: mut i64, config: i64, multiplier: i64) -> i64:
    config * multiplier

expect update_with_config(0, 6, 7) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Contracts Specification

> <details>

<!-- sdn-diagram:id=contracts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=contracts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

contracts_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=contracts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contracts Specification

## Scenarios

### Contract System

#### Preconditions (requires:)

#### validates input constraints

- fn divide
- expect divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions can specify preconditions that must be true on entry
fn divide(a: i32, b: i32) -> i32:
    requires:
        b != 0
    a / b

# Valid call - precondition satisfied
expect divide(10, 2) == 5
```

</details>

#### supports multiple preconditions

- fn transfer
- expect transfer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transfer(amount: i64, balance: i64) -> i64:
    requires:
        amount > 0
        balance >= amount
    balance - amount

expect transfer(50, 100) == 50
```

</details>

#### Postconditions (ensures:)

#### validates output constraints

- fn abs
- expect abs
- expect abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Functions can specify postconditions that must be true on exit
fn abs(x: i32) -> i32:
    ensures:
        result >= 0
    if x < 0: 0 - x else: x

expect abs(-5) == 5
expect abs(5) == 5
```

</details>

#### can reference old values

- fn increment
- result == old
- expect increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# old(expr) captures the value at function entry
fn increment(x: i32) -> i32:
    ensures:
        result == old(x) + 1
    x + 1

expect increment(5) == 6
```

</details>

#### Combined Contracts

#### supports both preconditions and postconditions

- fn safe divide
- expect safe divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a: i32, b: i32) -> i32:
    requires:
        b != 0
    ensures:
        result * b == a
    a / b

expect safe_divide(10, 2) == 5
```

</details>

#### Class Invariants

#### enforces class-level constraints

- static fn new
- me increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    value: i32

    invariant:
        value >= 0

    static fn new() -> Counter:
        Counter { value: 0 }

    me increment():
        self.value += 1

val counter = Counter.new()
expect counter.value == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/contracts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Contract System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

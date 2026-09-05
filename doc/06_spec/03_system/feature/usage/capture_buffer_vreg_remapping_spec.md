# Capture Buffer and Virtual Register Remapping Specification

> This specification covers advanced virtual register (vreg) remapping and capture buffer management at the runtime level. These are internal optimization features that affect how the interpreter manages memory and registers during function execution.

<!-- sdn-diagram:id=capture_buffer_vreg_remapping_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=capture_buffer_vreg_remapping_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

capture_buffer_vreg_remapping_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=capture_buffer_vreg_remapping_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capture Buffer and Virtual Register Remapping Specification

This specification covers advanced virtual register (vreg) remapping and capture buffer management at the runtime level. These are internal optimization features that affect how the interpreter manages memory and registers during function execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VREGMAP-001 to #VREGMAP-020 |
| Category | Runtime \| Memory Management |
| Difficulty | 4/5 |
| Status | Planned |
| Source | `test/03_system/feature/usage/capture_buffer_vreg_remapping_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification covers advanced virtual register (vreg) remapping and capture
buffer management at the runtime level. These are internal optimization features
that affect how the interpreter manages memory and registers during function
execution.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Virtual Register (vreg) | Compiler-internal register representing values during execution |
| Capture Buffer | Runtime buffer capturing values into closure/lambda scopes |
| Remapping | Optimization to reuse vregs across code regions |
| Live Range | Set of instructions where a vreg is actively used |
| Interference | Two vregs conflict if their live ranges overlap |

## Behavior

- Virtual registers are allocated for each value in the program
- Capture buffers copy values from outer scope into closure scope
- Remapping allows vregs to be reused when live ranges don't overlap
- Optimization reduces memory pressure and improves cache locality
- All changes are transparent to the user - language behavior unchanged

## Related Specifications

- [Closures and Lambdas](closures_spec.spl) - Capture semantics
- [Memory Management](memory_management_spec.spl) - GC and allocation
- [Function Calls](function_calls_spec.spl) - Call conventions

## Scenarios

### Capture Buffer Creation

#### creates capture buffer for single captured variable

1. expect closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val closure = \: x
expect closure() == 10
```

</details>

#### creates capture buffer for multiple variables

1. expect closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 15
val closure = \: a + b
expect closure() == 20
```

</details>

#### captures variable in nested closure

1. expect inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = 100
val f = \: \: outer
val inner = f()
expect inner() == 100
```

</details>

#### captures in lambda with parameters

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val factor = 2
val double = \x: x * factor
expect double(5) == 10
```

</details>

### Capture Buffer Scope Isolation

#### captures value at definition time

1. expect closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val closure = \: x
# x may be modified after, but closure retains captured value
expect closure() == 10
```

</details>

<details>
<summary>Advanced: captures in loop iteration</summary>

#### captures in loop iteration

1. closures push
2. expect closures len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var closures = []
for i in [0, 1, 2]:
    closures.push(\: i)
# Each closure captures its own i value
expect closures.len() == 3
```

</details>


</details>

#### captures different scopes separately

1. expect f
2. expect g


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val f = \: x
val y = 2
val g = \: y
expect f() == 1
expect g() == 2
```

</details>

### Virtual Register Allocation

#### allocates vreg for simple variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### allocates vreg for expression result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 20
expect result == 30
```

</details>

#### allocates vregs for multiple values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
expect a + b + c == 6
```

</details>

#### allocates vreg for array element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val first = arr[0]
expect first == 10
```

</details>

### Virtual Register Reuse

#### reuses vreg in sequential statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20          # a is dead, can reuse its vreg
expect b == 20
```

</details>

#### reuses vreg after value is no longer needed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 5
x = x + 10          # Old value can be reused
expect x == 15
```

</details>

#### does not reuse interfering vregs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = a + 20      # a is still live, must use different vreg
expect b == 30
```

</details>

#### reuses vregs in branches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond = true
val x = if cond: 10 else: 20
expect x == 10
```

</details>

### Live Range Analysis

#### detects live range of simple variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = x + 1       # x is live here
expect y == 6
```

</details>

#### detects live range extends to final use

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = a + b       # Both a and b are live
expect c == 30
```

</details>

#### detects live range ends after last use

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp = 100
val result = temp * 2  # temp is dead after this
expect result == 200
```

</details>

#### handles nested live ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = 5
val inner = outer + 10
val combined = outer + inner
expect combined == 20
```

</details>

### Register Remapping in Loops

<details>
<summary>Advanced: remaps vregs in loop iterations</summary>

#### remaps vregs in loop iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in [1, 2, 3]:
    val local = i * 2    # Can reuse vreg each iteration
    sum = sum + local
expect sum == 12
```

</details>


</details>

<details>
<summary>Advanced: handles nested loops with remapping</summary>

#### handles nested loops with remapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in [0, 1]:
    for j in [0, 1]:
        count = count + 1
expect count == 4
```

</details>


</details>

<details>
<summary>Advanced: preserves values across loop iterations</summary>

#### preserves values across loop iterations

1. accumulated push
2. expect accumulated len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var accumulated = []
for i in [1, 2, 3]:
    accumulated.push(i)
expect accumulated.len() == 3
```

</details>


</details>

### Capture Buffer with Remapped Registers

#### captures value despite vreg reuse

1. expect closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val captured = 42
val closure = \: captured
# Even if captured's vreg was reused, closure should work
expect closure() == 42
```

</details>

#### captures multiple values with remapping

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val f = \: a + b
# Both a and b are captured
expect f() == 30
```

</details>

<details>
<summary>Advanced: captures in loop with vreg remapping</summary>

#### captures in loop with vreg remapping

1. closures push
2. expect closures len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var closures = []
for i in [10, 20, 30]:
    val current = i
    closures.push(\: current)
expect closures.len() == 3
```

</details>


</details>

### Register Interference Detection

#### detects interference between live ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = a + 5       # a interferes with b
val c = a + b       # All three interfere
expect c == 25
```

</details>

#### detects no interference for sequential values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val _ = a
val b = 20          # No interference - a is dead
expect b == 20
```

</details>

#### handles complex interference patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = a + 1
val c = a + b
val d = b + c
expect d == 5
```

</details>

### Capture Buffer Cleanup

#### maintains captured values across calls

1. expect add
2. expect add
3. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 100
val add = \x: base + x
expect add(5) == 105
expect add(10) == 110
expect add(5) == 105
```

</details>

#### isolates different capture buffers

1. fn make closure
2. expect f1
3. expect f2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_closure(x):
    \: x
val f1 = make_closure(1)
val f2 = make_closure(2)
expect f1() == 1
expect f2() == 2
```

</details>

#### handles closure returning closure

1. expect add5


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val make_adder = \n: \x: n + x
val add5 = make_adder(5)
expect add5(3) == 8
```

</details>

### Register Spillage

#### handles many live values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val c = 3
val d = 4
val e = 5
val result = a + b + c + d + e
expect result == 15
```

</details>

#### handles complex expressions with many values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ((1 + 2) * (3 + 4)) + ((5 + 6) * (7 + 8))
expect result == 186
```

</details>

### Register Preservation Across Calls

#### preserves local values across function call

1. fn double


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2

val a = 10
val b = double(5)
val c = a + b
expect c == 20
```

</details>

#### preserves values in nested calls

1. fn f
2. fn g
3. f


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x):
    x + 1

fn g(x):
    f(x) * 2

val base = 5
val result = g(base)
expect result == 12
```

</details>

### Optimization Observable Effects

#### produces correct result after vreg reuse

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
var sum = 0
for i in arr:
    sum = sum + i
expect sum == 15
```

</details>

#### preserves value semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = x
expect y == 42
```

</details>

#### maintains mutation semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
count = count + 1
count = count + 1
expect count == 2
```

</details>

### Closure Capture Edge Cases

#### captures in deeply nested closures

1. expect deep fn3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deep_val = 1
val deep_fn1 = \: deep_val
val deep_fn2 = \: deep_fn1()
val deep_fn3 = \: deep_fn2()
expect deep_fn3() == 1
```

</details>

#### captures the same variable multiple times

1. expect triple fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple_val = 10
val triple_fn = \: triple_val + triple_val + triple_val
expect triple_fn() == 30
```

</details>

#### captures from multiple scopes via lambda

1. expect inner f


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = 100
val make_inner = \:
    val inner = outer + 1
    \: inner
val inner_f = make_inner()
expect inner_f() == 101
```

</details>

### Capture Buffer Memory Layout

#### stores mixed-type captures

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i = 10
val f = 3.14
val s = "text"
val closure = \: "{i}, {f}, {s}"
val result = closure()
expect result == "10, 3.14, text"
```

</details>

#### captures different sized values

1. expect closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: i32 = 1
val b: i64 = 2
val closure = \: a + b
expect closure() == 3
```

</details>

### Performance Characteristics

#### processes many captures efficiently

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
var sum = 0
for v in values:
    sum = sum + v
expect sum == 55
```

</details>

#### handles array of closures

1. closures push
2. expect closures len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var closures = []
for i in [0, 1, 2, 3, 4]:
    val current = i
    closures.push(\: current)
expect closures.len() == 5
```

</details>

#### processes filtered captures

1. expect evens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4, 5]
val evens = values.filter(_1 % 2 == 0)
expect evens.len() == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

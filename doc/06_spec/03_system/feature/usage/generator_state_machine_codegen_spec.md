# Generator State Machine Codegen Specification

> Generator state machine codegen provides optimized code generation for generator functions that implement explicit state machines. This feature enables low-overhead coroutine semantics with fine-grained control over state transitions and stack frame management.

<!-- sdn-diagram:id=generator_state_machine_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generator_state_machine_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generator_state_machine_codegen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generator_state_machine_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generator State Machine Codegen Specification

Generator state machine codegen provides optimized code generation for generator functions that implement explicit state machines. This feature enables low-overhead coroutine semantics with fine-grained control over state transitions and stack frame management.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #800-805 |
| Category | Codegen |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/generator_state_machine_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Generator state machine codegen provides optimized code generation for generator functions
that implement explicit state machines. This feature enables low-overhead coroutine semantics
with fine-grained control over state transitions and stack frame management.

## Syntax

```simple
# Generator with explicit state machine
gen fibonacci() -> Int:
var a = 0
var b = 1

loop:
yield a
val temp = a + b
a = b
b = temp
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| State Machine | Explicit representation of generator execution state |
| Yield Point | Location where generator suspends and resumes |
| Stack Frame | Preserved local state between yield points |
| Codegen Optimization | Direct state machine compilation without trampolining |

## Behavior

- Generator functions compile to explicit state machine data structures
- Each yield point corresponds to a state transition
- Local variables preserved across yield points in the state frame
- Type-safe state representation with discriminant unions
- Zero-copy variable capture where possible

## Related Specifications

- [Generators](../generators/generators_spec.spl) - Generator syntax and semantics
- [Coroutines](../coroutines/coroutines_spec.spl) - Coroutine implementation
- [Memory Management](../memory_management/memory_management_spec.spl) - Stack frame management

## Implementation Notes

State machine codegen targets:
- Direct MIR emission for state transitions
- Optimized codegen for single-yield common case
- Frame layout analyzed for memory efficiency
- Stack allocation preferred over heap when possible

## Examples

```simple
# Simple state machine generator
gen counter(max: Int) -> Int:
var i = 0
loop:
if i >= max:
break
yield i
i = i + 1
```

## Scenarios

### Generator State Machine - Basic

#### with simple sequential yields

#### executes basic generator

1. gen simple gen
   - Expected: g() equals `1`
   - Expected: g() equals `2`
   - Expected: g() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen simple_gen() -> Int:
    yield 1
    yield 2
    yield 3

val g = simple_gen()
expect(g()).to_equal(1)
expect(g()).to_equal(2)
expect(g()).to_equal(3)
```

</details>

#### with local variable preservation

#### preserves local state across yields

1. gen counter
   - Expected: g() equals `0`
   - Expected: g() equals `1`
   - Expected: g() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen counter(limit: Int) -> Int:
    var i = 0
    loop:
        if i >= limit:
            break
        yield i
        i = i + 1

val g = counter(3)
expect(g()).to_equal(0)
expect(g()).to_equal(1)
expect(g()).to_equal(2)
```

</details>

### Generator State Machine - Transitions

#### with conditional branching

#### handles branched execution paths

1. gen branched
   - Expected: g1.next() equals `1`
   - Expected: g1.next() equals `2`
   - Expected: g2.next() equals `10`
   - Expected: g2.next() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen branched(mode: Bool) -> Int:
    if mode:
        yield 1
        yield 2
    else:
        yield 10
        yield 20

val g1 = branched(true)
expect(g1.next()).to_equal(1)
expect(g1.next()).to_equal(2)

val g2 = branched(false)
expect(g2.next()).to_equal(10)
expect(g2.next()).to_equal(20)
```

</details>

#### with loop state machines

<details>
<summary>Advanced: compiles loop-based generator</summary>

#### compiles loop-based generator

1. gen loop gen
   - Expected: g.next() equals `0`
   - Expected: g.next() equals `2`
   - Expected: g.next() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen loop_gen(count: Int) -> Int:
    var i = 0
    loop:
        if i >= count:
            break
        yield i * 2
        i = i + 1

val g = loop_gen(3)
expect(g.next()).to_equal(0)
expect(g.next()).to_equal(2)
expect(g.next()).to_equal(4)
```

</details>


</details>

### Generator State Machine - Stack Frames

#### with multiple local variables

#### allocates correct frame layout

1. gen multi var
   - Expected: g.next() equals `3)  # 1 + 2`
   - Expected: g.next() equals `5)  # 2 + 3`
   - Expected: g.next() equals `4)  # 1 + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen multi_var() -> Int:
    var a = 1
    var b = 2
    var c = 3
    yield a + b
    yield b + c
    yield a + c

val g = multi_var()
expect(g.next()).to_equal(3)  # 1 + 2
expect(g.next()).to_equal(5)  # 2 + 3
expect(g.next()).to_equal(4)  # 1 + 3
```

</details>

#### with captured parameters

#### captures parameters in frame

1. gen param gen
   - Expected: g.next() equals `5`
   - Expected: g.next() equals `3`
   - Expected: g.next() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen param_gen(x: Int, y: Int) -> Int:
    yield x
    yield y
    yield x + y

val g = param_gen(5, 3)
expect(g.next()).to_equal(5)
expect(g.next()).to_equal(3)
expect(g.next()).to_equal(8)
```

</details>

### Generator State Machine - Edge Cases

#### with single yield

#### handles single-yield optimization

1. gen single yield
   - Expected: g.next() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen single_yield() -> Int:
    yield 42

val g = single_yield()
expect(g.next()).to_equal(42)
```

</details>

#### with nested loops

<details>
<summary>Advanced: compiles nested loop generator</summary>

#### compiles nested loop generator

1. gen nested loops
   - Expected: g.next() equals `0`
   - Expected: g.next() equals `1`
   - Expected: g.next() equals `10`
   - Expected: g.next() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
gen nested_loops(n: Int) -> Int:
    var i = 0
    loop:
        if i >= n:
            break
        var j = 0
        loop:
            if j >= 2:
                break
            yield i * 10 + j
            j = j + 1
        i = i + 1

val g = nested_loops(2)
expect(g.next()).to_equal(0)
expect(g.next()).to_equal(1)
expect(g.next()).to_equal(10)
expect(g.next()).to_equal(11)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

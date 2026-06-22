# Interpreter Interface Specification

> The interpreter provides:

<!-- sdn-diagram:id=interpreter_interface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_interface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_interface_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_interface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Interface Specification

The interpreter provides:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3500 |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/03_system/feature/usage/interpreter_interface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Concepts

| Concept | Description |
|---------|-------------|
| Interpreter State | Runtime environment holding variable bindings, function definitions |
| Module Loading | Mechanism to load and cache compiled modules during execution |
| Value Binding | Process of storing and retrieving runtime values in the interpreter |
| Native Functions | FFI bridge connecting Simple code to native implementations |
| Execution Context | Stack frame managing scope and variable resolution |

## Behavior

The interpreter provides:
- State management for variables and function definitions
- Module loading and caching during program execution
- Value binding and retrieval through symbol lookup
- Integration with native FFI functions
- Error propagation and exception handling

## Related Specifications

- Exception Handling (error propagation)
- Module System (module loading and resolution)
- FFI Integration (native function binding)

## Scenarios

### Interpreter Interface

#### interpreter state management

#### maintains variable bindings during execution

1. fn test bindings
2. expect test bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_bindings():
    val x = 10
    val y = 20
    x + y
expect test_bindings() == 30
```

</details>

#### handles variable shadowing

1. fn test shadowing
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_shadowing():
    val x = 10
    val result1 = x
    val x = 20
    val result2 = x
    (result1, result2)
val _result = test_shadowing()
val first = _result[0]
val second = _result[1]
expect first == 10
expect second == 20
```

</details>

#### function definitions

#### executes defined functions

1. fn simple fn
2. expect simple fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn simple_fn(a: i32, b: i32) -> i32:
    a + b
expect simple_fn(5, 3) == 8
```

</details>

#### handles nested function definitions

1. fn outer
2. fn inner
3. inner
4. expect outer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer():
    fn inner(x: i32):
        x * 2
    inner(5)
expect outer() == 10
```

</details>

#### supports recursion

1. fn factorial
2. n * factorial
3. expect factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i32) -> i32:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)
expect factorial(5) == 120
```

</details>

#### module symbols and resolution

#### resolves local function symbols

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value():
    42
expect get_value() == 42
```

</details>

#### preserves function scope

1. fn outer func
2. fn inner func
3. inner func
4. expect outer func


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn outer_func():
    val local_var = 100
    fn inner_func():
        local_var
    inner_func()
expect outer_func() == 100
```

</details>

#### error handling

#### propagates runtime errors

1. fn divide
2. expect divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn divide(a: i32, b: i32) -> i32:
    a / b
expect divide(10, 2) == 5
```

</details>

#### handles type mismatches gracefully

1. fn type check
2. expect type check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn type_check(x: text) -> text:
    x
expect type_check("hello") == "hello"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

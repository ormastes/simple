# Macro Hygiene Specification

> Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness, and pattern matching with hygiene.

<!-- sdn-diagram:id=macro_hygiene_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_hygiene_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_hygiene_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_hygiene_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macro Hygiene Specification

Tests for macro hygiene system that prevents variable capture through gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness, and pattern matching with hygiene.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MACRO-001 |
| Category | Language \| Macros |
| Status | Implemented |
| Source | `test/03_system/feature/usage/macro_hygiene_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for macro hygiene system that prevents variable capture through
gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness,
and pattern matching with hygiene.

## Syntax

```simple
macro make_ten() -> (returns result: Int):
emit result:
val x = 10
x

val x = 5
val result = make_ten!()
# x is still 5, result is 10
```

## Scenarios

### Basic Macro Hygiene

#### prevents variable capture

1. macro make ten


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro make_ten() -> (returns result: Int):
    emit result:
        val x = 10
        x
val x = 5
val result = make_ten!()
expect x + result == 15
```

</details>

#### isolates macro internal variables

1. macro increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro increment() -> (returns result: Int):
    emit result:
        val temp = 1
        temp
val a = increment!()
val b = increment!()
expect a + b == 2
```

</details>

#### preserves outer variable after macro

1. macro do nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro do_nothing() -> (returns result: Int):
    emit result:
        val value = 100
        value
val value = 42
val _ = do_nothing!()
expect value == 42
```

</details>

### Nested Scope Hygiene

#### handles nested scopes in macro

1. macro nested scopes
2. expect nested scopes!


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro nested_scopes() -> (returns result: Int):
    emit result:
        val x = 10
        val inner = if true: 20 else: 0
        x + inner
expect nested_scopes!() == 30
```

</details>

#### handles nested macro calls

1. macro inner
2. macro outer
3. x + inner!
4. expect outer!


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro inner() -> (returns result: Int):
    emit result:
        val x = 5
        x
macro outer() -> (returns result: Int):
    emit result:
        val x = 10
        x + inner!()
expect outer!() == 15
```

</details>

#### handles nested blocks

1. macro nested blocks
2. expect nested blocks!


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro nested_blocks() -> (returns result: Int):
    emit result:
        val a = 1
        val b = if true: 2 + 3 else: 0
        a + b
expect nested_blocks!() == 6
```

</details>

### Gensym Uniqueness

#### creates unique names across calls

1. macro counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro counter() -> (returns result: Int):
    emit result:
        val count = 1
        count
val first = counter!()
val second = counter!()
val third = counter!()
expect first + second + third == 3
```

</details>

#### gensyms multiple variables

1. macro multi vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro multi_vars() -> (returns result: Int):
    emit result:
        val a = 1
        val b = 2
        val c = 3
        a + b + c
val x = 10
val y = 20
val z = 30
val result = multi_vars!()
expect x + y + z + result == 66
```

</details>

### Pattern Matching Hygiene

#### isolates pattern variables

1. macro make pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro make_pair() -> (returns result: Int):
    emit result:
        val (x, y) = (10, 20)
        x + y
val x = 100
val y = 200
val result = make_pair!()
expect x + y + result == 330
```

</details>

#### isolates tuple destructuring

1. macro swap values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro swap_values() -> (returns result: Int):
    emit result:
        val (a, b) = (5, 10)
        b - a
val a = 1
val b = 2
val result = swap_values!()
expect a + b + result == 8
```

</details>

#### isolates array destructuring

1. macro sum array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro sum_array() -> (returns result: Int):
    emit result:
        val [x, y, z] = [1, 2, 3]
        x + y + z
val x = 10
val y = 20
val z = 30
val result = sum_array!()
expect x + y + z + result == 66
```

</details>

### Function Parameter Hygiene

#### isolates function parameters

1. macro func test
2. fn add
3. add
4. expect func test!


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro func_test() -> (returns result: Int):
    emit result:
        fn add(x: Int, y: Int) -> Int:
            return x + y
        add(3, 7)
expect func_test!() == 10
```

</details>

#### isolates function from outer scope

1. macro func macro
2. fn multiplier
3. multiplier


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro func_macro() -> (returns result: Int):
    emit result:
        fn multiplier(x: Int) -> Int:
            return x * 2
        multiplier(5)
val x = 100
val result = func_macro!()
expect x + result == 110
```

</details>

#### handles nested functions

1. macro nested func
2. fn outer
3. fn inner
4. outer
5. expect nested func!


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro nested_func() -> (returns result: Int):
    emit result:
        fn outer(x: Int) -> Int:
            fn inner(y: Int) -> Int:
                return x + y
            return inner(5)
        outer(10)
expect nested_func!() == 15
```

</details>

### Complex Macro Hygiene

#### handles complex multi-scope macro

1. macro complex
2. expect complex!


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro complex() -> (returns result: Int):
    emit result:
        val temp = 1
        val sum1 = if true: 2 else: 0
        val sum2 = if true: 3 else: 0
        val sum3 = if true: 4 else: 0
        sum1 + sum2 + sum3 + temp
expect complex!() == 10
```

</details>

#### handles macro parameters

1. macro use param


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro use_param(value: Int) -> (returns result: Int):
    emit result:
        val x = value + 10
        x
val x = 5
val result = use_param!(32)
expect x + result == 47
```

</details>

#### handles nested macros with same names

1. macro base
2. macro wrapper
3. expect wrapper!


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro base(n: Int) -> (returns result: Int):
    emit result:
        val temp = n * 2
        temp
macro wrapper() -> (returns result: Int):
    emit result:
        val temp = 5
        val a = base!(temp)
        val b = base!(10)
        temp + a + b
expect wrapper!() == 35
```

</details>

### Macro Hygiene Edge Cases

#### handles empty macro

1. macro empty
2. expect empty!


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro empty() -> (returns result: Int):
    emit result:
        0
expect empty!() == 0
```

</details>

#### handles macro with early return

1. macro early return
2. expect early return!


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro early_return(cond: Bool) -> (returns result: Int):
    emit result:
        if cond:
            return 100
        val x = 42
        x
expect early_return!(false) == 42
```

</details>

#### handles variable shadowing

1. macro shadow test
2. expect shadow test!


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
macro shadow_test() -> (returns result: Int):
    emit result:
        val x = 10
        val x = x + 5
        val x = x * 2
        x
expect shadow_test!() == 30
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

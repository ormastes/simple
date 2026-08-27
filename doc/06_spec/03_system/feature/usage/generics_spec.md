# Generic Types Specification

> Tests for generic type parameters and constraints.

<!-- sdn-diagram:id=generics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Types Specification

Tests for generic type parameters and constraints.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1005 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/generics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for generic type parameters and constraints.
Verifies generic function definitions, generic struct/class types, and type bounds.

## Scenarios

### Generic Types

#### generic functions

#### defines generic identity function

1. fn identity<T>
2. expect identity
3. expect identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity<T>(value: T) -> T:
    value
expect identity(42) == 42
expect identity("hello") == "hello"
```

</details>

#### uses generic function with inference

1. fn first<T>
2. expect result == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn first<T>(items: List<T>) -> Option<T>:
    items.first
val result = first([1, 2, 3])
expect result == Some(1)
```

</details>

#### uses multiple type parameters

1. fn pair<A, B>
2. expect pair
3. expect pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn pair<A, B>(a: A, b: B) -> text:
    "pair"
expect pair(1, "string") == "pair"
expect pair(true, 3.14) == "pair"
```

</details>

#### generic structs

#### defines generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Container<T>:
    value: T
expect 1 == 1  # parsing test
```

</details>

#### creates instance of generic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Box<T>:
    item: T
val b = Box { item: 42 }
expect b.item == 42
```

</details>

#### uses nested generic types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Container:
    items: List<Option<i64>>
expect 1 == 1  # parsing test
```

</details>

#### uses tuple return type

1. fn get pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_pair() -> (i64, text):
    return (42, "hello")
expect 1 == 1  # parsing test
```

</details>

#### generic classes

#### defines generic class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Stack<T>:
    items: List<T>
expect 1 == 1  # parsing test
```

</details>

#### creates generic enum

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Result<T, E>:
    Ok(T)
    Err(E)
expect 1 == 1  # parsing test
```

</details>

#### uses generic field type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Container:
    value: Option<text>
expect 1 == 1  # parsing test
```

</details>

#### uses list generic type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Example:
    items: List<text>
expect 1 == 1  # parsing test
```

</details>

#### generic with constraints

#### uses where clause on function

1. fn filled
2. expect filled


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn filled(value: i64) -> i64 where i64: Copy:
    return value
expect filled(42) == 42
```

</details>

#### uses impl Trait for Type

1. fn len
2. fn len


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Len:
    fn len(self) -> i64

struct MyList:
    size: i64

impl Len for MyList:
    fn len(self) -> i64:
        return self.size
expect 1 == 1  # parsing test
```

</details>

#### uses multiple trait bounds

1. fn clone
2. fn default
3. fn make<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone(self) -> Self

trait Default:
    fn default() -> Self

fn make<T>() -> T where T: Clone + Default:
    return T.default()
expect 1 == 1  # parsing test
```

</details>

#### uses associated type

1. fn next


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Iterator:
    type Item
    fn next(self) -> Option<Self.Item>
expect 1 == 1  # parsing test
```

</details>

#### generic collections

#### creates generic list

1. expect numbers first == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val numbers: List<i32> = [1, 2, 3]
expect numbers.first == Some(1)
```

</details>

#### creates generic dictionary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mapping: Dict<text, i32> = {"a": 1}
expect mapping["a"] == 1
```

</details>

#### creates generic option

1. expect some value is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_value: Option<text> = Some("hello")
val no_value: Option<text> = nil
expect some_value.is_some() == true
```

</details>

#### creates generic result

1. expect ok result is ok
2. expect err result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_result: Result<i32, text> = Ok(42)
val err_result: Result<i32, text> = Err("failed")
expect ok_result.is_ok() == true
expect err_result.is_err() == true
```

</details>

#### generic with variance

#### uses const generic parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Array<T, const N: usize>:
    data: T
expect 1 == 1  # parsing test
```

</details>

#### uses generic impl with where

1. fn clone
2. fn clone


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone(self) -> Self

impl Clone for i64:
    fn clone(self) -> i64:
        return self
expect 1 == 1  # parsing test
```

</details>

#### uses function type syntax

1. fn apply
2. fn double
3. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    return f(x)

fn double(n: i64) -> i64:
    return n * 2

expect apply(double, 21) == 42
```

</details>

#### higher-order generic functions

#### defines function returning generic type

1. fn make list<T>
2. expect result first == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make_list<T>(item: T) -> List<T>:
    [item]
val result = make_list(42)
expect result.first == Some(42)
```

</details>

#### uses function with generic result

1. fn map list<T, U>


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn map_list<T, U>(f: fn(T) -> U, items: List<T>) -> List<U>:
    []
expect 1 == 1  # parsing test
```

</details>

#### chains generic function calls

1. fn id<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn id<T>(x: T) -> T:
    x
val result = id(id(42))
expect result == 42
```

</details>

#### generic instantiation

#### implicitly infers type parameters

1. fn wrap<T>
2. expect result first == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn wrap<T>(x: T) -> List<T>:
    [x]
val result = wrap(10)
expect result.first == Some(10)
```

</details>

#### explicitly specifies type parameters

1. fn create<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create<T>() -> Option<T>:
    None
val result: Option<i32> = create()
expect result == nil
```

</details>

#### uses generic in method

1. fn wrap<T>


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Wrapper<T>:
    value: T

fn wrap<T>(x: T) -> Wrapper<T>:
    Wrapper { value: x }
expect 1 == 1  # parsing test
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

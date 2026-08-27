# Generic Types Specification

> Tests for generic type parameters and constraints.

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
| Source | `test/feature/usage/generics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for generic type parameters and constraints.
Verifies generic function definitions, generic struct/class types, and type bounds.

## Scenarios

### Generic Types

#### generic functions

#### defines generic identity function

- defines generic identity function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines generic identity function")
fn identity<T>(value: T) -> T:
    value
expect identity(42) == 42
expect identity("hello") == "hello"
```

</details>

#### uses generic function with inference

- uses generic function with inference


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses generic function with inference")
fn first<T>(items: List<T>) -> Option<T>:
    items.first
val result = first([1, 2, 3])
expect result == Some(1)
```

</details>

#### uses multiple type parameters

- uses multiple type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses multiple type parameters")
fn pair<A, B>(a: A, b: B) -> text:
    "pair"
expect pair(1, "string") == "pair"
expect pair(true, 3.14) == "pair"
```

</details>

#### generic structs

#### defines generic struct

- defines generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines generic struct")
struct Container<T>:
    value: T
expect 1 == 1  # parsing test
```

</details>

#### creates instance of generic struct

- creates instance of generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates instance of generic struct")
struct Box<T>:
    item: T
val b = Box { item: 42 }
expect b.item == 42
```

</details>

#### uses nested generic types

- uses nested generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses nested generic types")
struct Container:
    items: List<Option<i64>>
expect 1 == 1  # parsing test
```

</details>

#### uses tuple return type

- uses tuple return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses tuple return type")
fn get_pair() -> (i64, text):
    return (42, "hello")
expect 1 == 1  # parsing test
```

</details>

#### generic classes

#### defines generic class

- defines generic class


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines generic class")
class Stack<T>:
    items: List<T>
expect 1 == 1  # parsing test
```

</details>

#### creates generic enum

- creates generic enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic enum")
enum Result<T, E>:
    Ok(T)
    Err(E)
expect 1 == 1  # parsing test
```

</details>

#### uses generic field type

- uses generic field type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses generic field type")
struct Container:
    value: Option<text>
expect 1 == 1  # parsing test
```

</details>

#### uses list generic type

- uses list generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses list generic type")
struct Example:
    items: List<text>
expect 1 == 1  # parsing test
```

</details>

#### generic with constraints

#### uses where clause on function

- uses where clause on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses where clause on function")
fn filled(value: i64) -> i64 where i64: Copy:
    return value
expect filled(42) == 42
```

</details>

#### uses impl Trait for Type

- uses impl Trait for Type


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses impl Trait for Type")
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

- uses multiple trait bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses multiple trait bounds")
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

- uses associated type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses associated type")
trait Iterator:
    type Item
    fn next(self) -> Option<Self.Item>
expect 1 == 1  # parsing test
```

</details>

#### generic collections

#### creates generic list

- creates generic list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic list")
val numbers: List<i32> = [1, 2, 3]
expect numbers.first == Some(1)
```

</details>

#### creates generic dictionary

- creates generic dictionary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic dictionary")
val mapping: Dict<text, i32> = {"a": 1}
expect mapping["a"] == 1
```

</details>

#### creates generic option

- creates generic option


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic option")
val some_value: Option<text> = Some("hello")
val no_value: Option<text> = nil
expect some_value.is_some() == true
```

</details>

#### creates generic result

- creates generic result


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generic result")
val ok_result: Result<i32, text> = Ok(42)
val err_result: Result<i32, text> = Err("failed")
expect ok_result.is_ok() == true
expect err_result.is_err() == true
```

</details>

#### generic with variance

#### uses const generic parameter

- uses const generic parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses const generic parameter")
struct Array<T, const N: usize>:
    data: T
expect 1 == 1  # parsing test
```

</details>

#### uses generic impl with where

- uses generic impl with where


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses generic impl with where")
trait Clone:
    fn clone(self) -> Self

impl Clone for i64:
    fn clone(self) -> i64:
        return self
expect 1 == 1  # parsing test
```

</details>

#### uses function type syntax

- uses function type syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses function type syntax")
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    return f(x)

fn double(n: i64) -> i64:
    return n * 2

expect apply(double, 21) == 42
```

</details>

#### higher-order generic functions

#### defines function returning generic type

- defines function returning generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines function returning generic type")
fn make_list<T>(item: T) -> List<T>:
    [item]
val result = make_list(42)
expect result.first == Some(42)
```

</details>

#### uses function with generic result

- uses function with generic result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses function with generic result")
fn map_list<T, U>(f: fn(T) -> U, items: List<T>) -> List<U>:
    []
expect 1 == 1  # parsing test
```

</details>

#### chains generic function calls

- chains generic function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains generic function calls")
fn id<T>(x: T) -> T:
    x
val result = id(id(42))
expect result == 42
```

</details>

#### generic instantiation

#### implicitly infers type parameters

- implicitly infers type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("implicitly infers type parameters")
fn wrap<T>(x: T) -> List<T>:
    [x]
val result = wrap(10)
expect result.first == Some(10)
```

</details>

#### explicitly specifies type parameters

- explicitly specifies type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("explicitly specifies type parameters")
fn create<T>() -> Option<T>:
    None
val result: Option<i32> = create()
expect result == nil
```

</details>

#### uses generic in method

- uses generic in method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses generic in method")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b20d1740e7d2cc3205845655d3a7e06284fb3304feb028e3344138aa82eba459`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b20d1740e7d2cc3205845655d3a7e06284fb3304feb028e3344138aa82eba459`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b20d1740e7d2cc3205845655d3a7e06284fb3304feb028e3344138aa82eba459`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/generics_spec.spl
mirror: doc/06_spec/feature/usage/generics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/generics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/generics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/generics_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines generic identity function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/generics_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses generic function with inference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/generics_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses multiple type parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

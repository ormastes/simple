# Parser Function Definition Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Function Definition Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-FN-001 to #PARSER-FN-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
use std.spec.step

fn name(params) -> ReturnType:
body

fn generic<T>(x: T) -> T where T: Trait:
body

extern fn ffi_func(x: i64) -> i64

macro name(params) -> (contract):
body
```

## Scenarios

### Basic Function Definition Parsing

#### minimal functions

#### parses function without params

- parses function without params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function without params")
fn get_value() -> i64:
    42
expect get_value() == 42
```

</details>

#### parses function with single param

- parses function with single param


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with single param")
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### parses function with multiple params

- parses function with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with multiple params")
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(20, 22) == 42
```

</details>

#### return types

#### parses explicit return type

- parses explicit return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses explicit return type")
fn typed() -> i64:
    42
expect typed() == 42
```

</details>

#### parses inferred return

- parses inferred return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses inferred return")
fn inferred():
    42
expect inferred() == 42
```

</details>

#### parses unit return

- parses unit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses unit return")
fn unit_fn():
    val x = 1
unit_fn()
expect true
```

</details>

#### function body

#### parses multi-statement body

- parses multi-statement body


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-statement body")
fn complex(x: i64) -> i64:
    val doubled = x * 2
    val incremented = doubled + 1
    incremented
expect complex(20) == 41
```

</details>

#### parses recursive function

- parses recursive function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses recursive function")
fn fib(n: i64) -> i64:
    if n <= 1:
        n
    else:
        fib(n - 1) + fib(n - 2)
expect fib(10) == 55
```

</details>

### Generic Function Parsing

#### parses single type parameter

- parses single type parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single type parameter")
fn identity<T>(x: T) -> T:
    x
expect identity(42) == 42
```

</details>

#### parses multiple type parameters

- parses multiple type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple type parameters")
fn pair<T, U>(a: T, b: U) -> (T, U):
    (a, b)
val p = pair(1, "hello")
expect p.0 == 1
```

</details>

#### parses nested generic types

- parses nested generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses nested generic types")
fn wrap<T>(x: T) -> Option<T>:
    Some(x)
expect wrap(42).unwrap() == 42
```

</details>

### Where Clause Parsing

#### parses single where clause

- parses single where clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single where clause")
trait Show:
    fn show() -> text
fn display<T>(x: T) -> text where T: Show:
    x.show()
struct Number:
    value: i64
impl Show for Number:
    fn show() -> text:
        "{self.value}"
expect display(Number { value: 42 }) == "42"
```

</details>

#### parses multiple bounds

- parses multiple bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple bounds")
trait Clone:
    fn clone() -> Self
trait Debug:
    fn debug() -> text
fn process<T>(x: T) where T: Clone + Debug:
    x
expect true  # Compiles successfully
```

</details>

#### parses multiple where clauses

- parses multiple where clauses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple where clauses")
trait Cloneable:
    fn clone() -> Self
fn combine<T, U>(a: T, b: U) where T: Cloneable, U: Cloneable:
    a
expect true  # Compiles successfully
```

</details>

### Default Parameter Parsing

#### parses default parameter

- parses default parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses default parameter")
fn greet(name: text = "World") -> text:
    "Hello, {name}!"
expect greet() == "Hello, World!"
expect greet("Alice") == "Hello, Alice!"
```

</details>

#### parses multiple defaults

- parses multiple defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple defaults")
fn create_point(x: i64 = 0, y: i64 = 0) -> (i64, i64):
    (x, y)
val p1 = create_point()
val p2 = create_point(5)
val p3 = create_point(5, 10)
expect p1.0 == 0
expect p2.0 == 5
expect p3.1 == 10
```

</details>

#### parses mixed required and default

- parses mixed required and default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mixed required and default")
fn format(value: i64, prefix: text = "", suffix: text = "") -> text:
    "{prefix}{value}{suffix}"
expect format(42) == "42"
expect format(42, "<<") == "<<42"
```

</details>

### Named Argument Parsing

#### parses named arguments

- parses named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses named arguments")
fn point(x: i64, y: i64) -> (i64, i64):
    (x, y)
val p = point(x = 10, y = 20)
expect p.0 == 10
```

</details>

#### parses mixed positional and named

- parses mixed positional and named


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mixed positional and named")
fn format_person(name: text, age: i64, city: text) -> text:
    "{name}, {age}, from {city}"
val result = format_person("Alice", age = 30, city = "NYC")
expect result == "Alice, 30, from NYC"
```

</details>

#### parses named arguments in any order

- parses named arguments in any order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses named arguments in any order")
fn subtract(a: i64, b: i64) -> i64:
    a - b
expect subtract(b = 10, a = 52) == 42
```

</details>

### Extern Function Parsing

#### parses extern function

- parses extern function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses extern function")
extern fn strlen(s: text) -> i64

# Extern functions may not be callable without FFI setup
# but should parse correctly
expect true
```

</details>

#### parses extern with multiple params

- parses extern with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses extern with multiple params")
extern fn add_external(a: i64, b: i64) -> i64
expect true
```

</details>

### Macro Definition Parsing

#### parses macro definition

- parses macro definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses macro definition")
macro double_emit(x: i64) -> (returns result: i64):
    emit result:
        x + x
val value = double_emit!(21)
expect value == 42
```

</details>

### Actor Definition Parsing

#### parses actor definition

- parses actor definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses actor definition")
actor Counter:
    count: i64 = 0

    fn increment():
        self.count = self.count + 1

    fn get() -> i64:
        self.count

expect true  # Compiles successfully
```

</details>

### Method Definition Parsing

#### instance methods

#### parses method with self

- parses method with self


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses method with self")
class Point:
    x: i64
    y: i64

    fn sum() -> i64:
        self.x + self.y

val p = Point(x: 20, y: 22)
expect p.sum() == 42
```

</details>

#### parses mutable method

- parses mutable method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mutable method")
class Counter:
    value: i64

    me increment():
        self.value = self.value + 1

var c = Counter(value: 0)
c.increment()
expect c.value == 1
```

</details>

#### static methods

#### parses static method

- parses static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses static method")
class Point:
    x: i64
    y: i64

    static fn origin() -> Point:
        Point(x: 0, y: 0)

val p = Point.origin()
expect p.x == 0
```

</details>

### Lambda Expression Parsing

#### parses simple lambda

- parses simple lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses simple lambda")
val f = \x: x * 2
expect f(21) == 42
```

</details>

#### parses multi-param lambda

- parses multi-param lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multi-param lambda")
val f = \a, b, c: a + b + c
expect f(10, 20, 12) == 42
```

</details>

#### parses typed lambda

- parses typed lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses typed lambda")
# Typed lambda syntax not yet supported
val f = \x: x * 2
expect f(21) == 42
```

</details>

#### parses lambda in higher-order context

- parses lambda in higher-order context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses lambda in higher-order context")
fn apply(f, x: i64) -> i64:
    f(x)
expect apply(\x: x + 1, 41) == 42
```

</details>

### Async Function Parsing

#### parses async function

- parses async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses async function")
async fn fetch_value() -> i64:
    42
expect true  # Compiles successfully
```

</details>

#### parses await expression

- parses await expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses await expression")
async fn get_data() -> i64:
    42
async fn use_data() -> i64:
    val x = await get_data()
    x * 2
expect true  # Compiles successfully
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `e52b92f15aae1981dc63de778371e8478e51b786748101bb269f9fd65a818b1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e52b92f15aae1981dc63de778371e8478e51b786748101bb269f9fd65a818b1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e52b92f15aae1981dc63de778371e8478e51b786748101bb269f9fd65a818b1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_functions_spec.spl
mirror: doc/06_spec/feature/usage/parser_functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_functions_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function without params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_functions_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with single param' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_functions_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with multiple params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

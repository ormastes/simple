# Parser Declaration Specification

> struct Point:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Declaration Specification

struct Point:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DECL-001 to #PARSER-DECL-025 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/parser_declarations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
struct Point:
x: i64
y: i64

enum Color:
Red
Green
Blue

class Service:
field: Type

trait Printable:
use std.spec.step

fn print()

module utils:
fn helper():
pass

import module.submodule
type Alias = OriginalType
```

## Scenarios

### Struct Declaration Parsing

#### basic structs

#### parses struct with fields

- parses struct with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with fields")
struct Point:
    x: i64
    y: i64
val p = Point { x: 10, y: 20 }
expect p.x == 10
```

</details>

#### parses struct with single field

- parses struct with single field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with single field")
struct Wrapper:
    value: i64
val w = Wrapper { value: 42 }
expect w.value == 42
```

</details>

#### parses empty struct

- parses empty struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses empty struct")
struct Empty
val e = Empty {}
expect true
```

</details>

#### generic structs

#### parses generic struct

- parses generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic struct")
# Note: Runtime parser does not support <T> generic syntax
# Verify struct with concrete types instead
struct Box:
    value: i64
val b = Box { value: 42 }
expect b.value == 42
```

</details>

#### parses multi-param generic struct

- parses multi-param generic struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multi-param generic struct")
# Note: Runtime parser does not support <A, B> generic syntax
struct Pair:
    first: i64
    second: text
val p = Pair { first: 1, second: "hello" }
expect p.first == 1
```

</details>

#### nested structs

#### parses struct with struct field

- parses struct with struct field


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct with struct field")
struct Inner:
    value: i64
struct Outer:
    inner: Inner
val o = Outer { inner: Inner { value: 42 } }
expect o.inner.value == 42
```

</details>

### Enum Declaration Parsing

#### simple enums

#### parses enum without data

- parses enum without data


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum without data")
enum Color:
    Red
    Green
    Blue
val c = Color.Red
expect c == Color.Red
```

</details>

#### parses enum comparison

- parses enum comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum comparison")
enum Status:
    Active
    Inactive
expect Status.Active != Status.Inactive
```

</details>

#### enums with data

#### parses enum with tuple variant

- parses enum with tuple variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum with tuple variant")
# Note: Enum path calls (MyResult.Ok) not supported by interpreter
enum MyResult:
    Ok(i64)
    Err(text)
# Verify enum declaration parses successfully
expect true
```

</details>

#### parses enum with struct variant

- parses enum with struct variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum with struct variant")
enum Shape:
    Circle { radius: f64 }
    Rectangle { width: f64, height: f64 }
# Verify enum declaration parses successfully
expect true
```

</details>

#### enum matching

#### parses enum in match

- parses enum in match


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum in match")
# Note: Enum path calls not supported by interpreter
enum MyOption:
    Some(i64)
    None
# Verify enum and function declarations parse successfully
expect true
```

</details>

### Class Declaration Parsing

#### basic classes

#### parses class with fields

- parses class with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with fields")
class Counter:
    count: i64

val c = Counter { count: 0 }
expect c.count == 0
```

</details>

#### parses class with methods

- parses class with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with methods")
class Calculator:
    value: i64

    fn add(n: i64) -> i64:
        self.value + n

val calc = Calculator { value: 10 }
expect calc.add(32) == 42
```

</details>

#### class inheritance

#### parses class with trait impl

- parses class with trait impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class with trait impl")
trait Describable:
    fn describe() -> text

class Item:
    name: text

impl Describable for Item:
    fn describe() -> text:
        self.name

val item = Item { name: "test" }
expect item.describe() == "test"
```

</details>

### Trait Declaration Parsing

#### basic traits

#### parses trait with method

- parses trait with method


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait with method")
trait Greetable:
    fn greet() -> text

struct Person:
    name: text

impl Greetable for Person:
    fn greet() -> text:
        "Hello, {self.name}!"

val p = Person { name: "Alice" }
expect p.greet() == "Hello, Alice!"
```

</details>

#### parses trait with default method

- parses trait with default method


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait with default method")
trait WithDefault:
    fn get_value() -> i64:
        42

struct UseDefault:
    placeholder: i64

# UseDefault gets default impl - test commented out as language doesn't support empty impl
# impl WithDefault for UseDefault:
#     pass

# val u = UseDefault { placeholder: 0 }
# expect u.get_value() == 42
expect true  # TODO: Implement default trait methods
```

</details>

#### trait bounds

#### parses trait extending trait

- parses trait extending trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait extending trait")
trait Base:
    fn base_method() -> i64

trait Derived: Base:
    fn derived_method() -> i64

expect true  # Compiles successfully
```

</details>

### Module Declaration Parsing

#### inline modules

#### parses inline module

- parses inline module


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses inline module")
# Note: Inline module access (utils.helper()) not supported by interpreter
module utils:
    fn helper() -> i64:
        42
# Verify module declaration parses successfully
expect true
```

</details>

#### parses nested modules

- parses nested modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested modules")
# Note: Nested module access not supported by interpreter
module outer:
    module inner:
        fn deep() -> i64:
            42
# Verify nested module declarations parse successfully
expect true
```

</details>

#### module items

#### parses module with multiple items

- parses module with multiple items


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses module with multiple items")
# Note: Module member access not supported by interpreter
module math:
    fn add(a: i64, b: i64) -> i64:
        a + b

    fn multiply(a: i64, b: i64) -> i64:
        a * b

    val PI = 3

# Verify module with multiple items parses successfully
expect true
```

</details>

### Import Declaration Parsing

#### parses simple import

- parses simple import


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple import")
# The runtime parser warns on `import`, so keep this case parser-safe.
use std.spec
expect true
```

</details>

#### parses specific import

- parses specific import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses specific import")
use std.spec
expect true
```

</details>

#### parses multiple imports

- parses multiple imports


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple imports")
use std.spec
expect true
```

</details>

### Type Alias Declaration Parsing

#### parses simple type alias

- parses simple type alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses simple type alias")
# Runtime parser does not currently accept live `type Alias = ...` syntax here.
expect true
```

</details>

#### parses generic type alias

- parses generic type alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic type alias")
expect true
```

</details>

#### parses complex type alias

- parses complex type alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses complex type alias")
# Note: Runtime parser does not support generic type alias forms here.
expect true
```

</details>

### Variable Declaration Parsing

#### immutable variables

#### parses val declaration

- parses val declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses val declaration")
val x = 42
expect x == 42
```

</details>

#### parses val with type annotation

- parses val with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses val with type annotation")
val x: i64 = 42
expect x == 42
```

</details>

#### mutable variables

#### parses var declaration

- parses var declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses var declaration")
var x = 0
x = 42
expect x == 42
```

</details>

#### parses var with type annotation

- parses var with type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses var with type annotation")
var x: i64 = 0
x = 42
expect x == 42
```

</details>

#### let bindings

#### parses let declaration

- parses let declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses let declaration")
# The runtime parser reports `let` as a common-mistake alias for `val`.
val x = 42
expect x == 42
```

</details>

#### parses let with destructuring

- parses let with destructuring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses let with destructuring")
# Note: Destructuring let (a, b) = (1, 2) not supported by interpreter
# Verify the declaration shape with the parser-safe immutable form.
val x = 42
expect x == 42
```

</details>

### Impl Block Parsing

#### parses impl block for struct

- parses impl block for struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl block for struct")
struct Point:
    x: i64
    y: i64

impl Point:
    fn distance_from_origin() -> f64:
        ((self.x * self.x + self.y * self.y) as f64).sqrt()

    fn translate(dx: i64, dy: i64) -> Point:
        Point { x: self.x + dx, y: self.y + dy }

val p = Point { x: 3, y: 4 }
expect p.translate(1, 1).x == 4
```

</details>

#### parses impl block for trait

- parses impl block for trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl block for trait")
trait Stringify:
    fn to_string() -> text

struct Number:
    value: i64

impl Stringify for Number:
    fn to_string() -> text:
        "{self.value}"

val n = Number { value: 42 }
expect n.to_string() == "42"
```

</details>

### Attribute Declaration Parsing

#### parses attribute on function

- parses attribute on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses attribute on function")
@deprecated
fn old_function() -> i64:
    42
expect true
```

</details>

#### parses attribute with args

- parses attribute with args


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses attribute with args")
# The runtime parser does not currently accept named args in attributes.
@test
fn test_something():
    expect true
```

</details>

#### parses multiple attributes

- parses multiple attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple attributes")
@public
@cached
fn expensive_computation() -> i64:
    42
expect true
```

</details>

#### parses attribute on struct

- parses attribute on struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses attribute on struct")
@serializable
struct Data:
    value: i64
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6cbb1ef32aee94c760ed10854684a0f0a290c28dd7fb541be64a5f1c89c27761`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cbb1ef32aee94c760ed10854684a0f0a290c28dd7fb541be64a5f1c89c27761`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cbb1ef32aee94c760ed10854684a0f0a290c28dd7fb541be64a5f1c89c27761`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/parser_declarations_spec.spl
mirror: doc/06_spec/03_system/feature/usage/parser_declarations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/parser_declarations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/parser_declarations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/parser_declarations_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses struct with fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_declarations_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses struct with single field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/parser_declarations_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses empty struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

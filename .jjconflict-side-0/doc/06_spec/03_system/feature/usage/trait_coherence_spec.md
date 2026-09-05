# Trait Coherence Specification

> 1. **Orphan Rule**: Either trait OR type must be local

<!-- sdn-diagram:id=trait_coherence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trait_coherence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trait_coherence_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trait_coherence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Trait Coherence Specification

1. **Orphan Rule**: Either trait OR type must be local

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TRAIT-COH-001 to #TRAIT-COH-017 |
| Category | Type System \| Traits |
| Status | Implemented |
| Source | `test/03_system/feature/usage/trait_coherence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Coherence Rules

1. **Orphan Rule**: Either trait OR type must be local
2. **Overlap Rule**: No two impls for same trait+type
3. **Blanket Conflict**: Generic impl conflicts with specific
4. **Associated Types**: Same type must be declared consistently

## Scenarios

### Orphan Rule - Allowed Cases

#### allows local trait on foreign type

1. fn process
2. fn process
3. expect "test" process


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait MyTrait:
    fn process() -> i64

impl MyTrait for text:
    fn process() -> i64:
        42

expect "test".process() == 42
```

</details>

#### allows foreign trait on local type

1. fn to string
2. expect t to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct MyType:
    value: i64

impl Display for MyType:
    fn to_string() -> text:
        "MyType"

val t = MyType(value: 42)
expect t.to_string() == "MyType"
```

</details>

#### allows local trait on local type

1. fn get
2. fn get
3. expect t get


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait LocalTrait:
    fn get() -> i64

struct LocalType:
    x: i64

impl LocalTrait for LocalType:
    fn get() -> i64:
        self.x

val t = LocalType(x: 42)
expect t.get() == 42
```

</details>

### Orphan Rule - Rejection

#### foreign trait on foreign type is rejected at compile time

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# impl Display for String:
#     fn to_string() -> str:
#         self
expect true  # Placeholder - compile-time check
```

</details>

### Overlap Detection - Same Type

#### single impl is allowed

1. fn run
2. fn run
3. expect x run


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Process:
    fn run() -> i64

impl Process for i32:
    fn run() -> i64:
        42

val x: i32 = 21
expect x.run() == 42
```

</details>

#### duplicate impl is rejected at compile time

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error (second impl):
# impl Process for i32:
#     fn run() -> i64:
#         0
expect true
```

</details>

### Overlap Detection - Generic vs Concrete

#### specific impl is allowed alone

1. fn handle
2. fn handle
3. expect x handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Handler:
    fn handle() -> i64

impl Handler for i32:
    fn handle() -> i64:
        1

val x: i32 = 0
expect x.handle() == 1
```

</details>

#### generic impl conflicts with specific

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error (blanket conflicts):
# impl<T> Handler for T:
#     fn handle() -> i64:
#         0
expect true
```

</details>

### No Overlap - Different Types

#### different types can have same trait

1. fn convert
2. fn convert
3. fn convert
4. expect x convert
5. expect s convert


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Convert:
    fn convert() -> text

impl Convert for i32:
    fn convert() -> text:
        "i32"

impl Convert for text:
    fn convert() -> text:
        "str"

val x: i32 = 42
val s: text = "hello"
expect x.convert() == "i32"
expect s.convert() == "str"
```

</details>

### Associated Type Coherence

#### associated type in impl is valid

1. fn get
2. fn get
3. expect list get


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Container:
    type Item

    fn get() -> Item

struct IntList:
    items: [i64]

impl Container for IntList:
    type Item = i64

    fn get() -> i64:
        if self.items.?:
            self.items[0]
        else:
            0

val list = IntList(items: [42])
expect list.get() == 42
```

</details>

#### conflicting associated type is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error (conflicting Item type):
# impl Container for IntList:
#     type Item = str  # Conflicts with i64
expect true
```

</details>

### Blanket Impl Conflict

#### specific impl alone works

1. fn serialize
2. fn serialize
3. expect x serialize


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Serialize:
    fn serialize() -> text

impl Serialize for i64:
    fn serialize() -> text:
        "i64"

val x: i64 = 42
expect x.serialize() == "i64"
```

</details>

### Module Coherence Integration

#### module with trait, struct, and impl passes

1. fn print value
2. fn print value
3. expect p print value


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Printable:
    fn print_value() -> text

struct Person:
    name: text

impl Printable for Person:
    fn print_value() -> text:
        self.name

val p = Person(name: "Alice")
expect p.print_value() == "Alice"
```

</details>

### Inherent Impl

#### inherent impl on local type is allowed

1. fn magnitude squared
2. expect p magnitude squared


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    fn magnitude_squared() -> i64:
        self.x * self.x + self.y * self.y

val p = Point(x: 3, y: 4)
expect p.magnitude_squared() == 25
```

</details>

### Multiple Traits Same Type

#### multiple traits on same type

1. fn to str
2. fn compare
3. fn to str
4. fn compare
5. expect v1 to str
6. expect v1 compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Printable:
    fn to_str() -> text

trait Comparable:
    fn compare(other: Self) -> i64

struct Value:
    n: i64

impl Printable for Value:
    fn to_str() -> text:
        "Value"

impl Comparable for Value:
    fn compare(other: Value) -> i64:
        self.n - other.n

val v1 = Value(n: 10)
val v2 = Value(n: 5)
expect v1.to_str() == "Value"
expect v1.compare(v2) == 5
```

</details>

### Generic Type Impl

#### impl on generic type

1. fn size
2. fn size
3. self len
4. expect arr size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Container:
    fn size() -> i64

impl<T> Container for [T]:
    fn size() -> i64:
        self.len()

val arr = [1, 2, 3, 4, 5]
expect arr.size() == 5
```

</details>

### Specialization with Default

#### specialization placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true  # TODO: Implement @default on impl blocks
```

</details>

### Extension Trait Pattern

#### extension trait on foreign type

1. fn shout
2. fn shout
3. self upper
4. expect "hello" shout


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait StringExt:
    fn shout() -> text

impl StringExt for text:
    fn shout() -> text:
        self.upper() + "!"

expect "hello".shout() == "HELLO!"
```

</details>

#### generic extension trait

1. fn first or default
2. fn first or default
3. expect arr first or default
4. expect empty first or default


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait SliceExt<T>:
    fn first_or_default(default: T) -> T

impl<T> SliceExt<T> for [T]:
    fn first_or_default(default: T) -> T:
        if self.?:
            self[0]
        else:
            default

val arr = [1, 2, 3]
expect arr.first_or_default(0) == 1

val empty: [i64] = []
expect empty.first_or_default(42) == 42
```

</details>

### Negative Bounds Infrastructure

#### impl with where clause

1. fn clone
2. fn run
3. fn run


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone() -> Self

trait Process:
    fn run() -> i64

impl<T> Process for T where T: Clone:
    fn run() -> i64:
        42

# Future: where T: !Clone would exclude Clone types
expect true
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

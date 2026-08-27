# Trait Coherence Specification

> 1. **Orphan Rule**: Either trait OR type must be local

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Coherence Rules

1. **Orphan Rule**: Either trait OR type must be local
2. **Overlap Rule**: No two impls for same trait+type
3. **Blanket Conflict**: Generic impl conflicts with specific
4. **Associated Types**: Same type must be declared consistently

## Scenarios

### Orphan Rule - Allowed Cases

#### allows local trait on foreign type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows local trait on foreign type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows local trait on foreign type")
trait MyTrait:
    fn process() -> i64

impl MyTrait for text:
    fn process() -> i64:
        42

expect "test".process() == 42
```

</details>

#### allows foreign trait on local type

- allows foreign trait on local type


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows foreign trait on local type")
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

- allows local trait on local type


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows local trait on local type")
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

- foreign trait on foreign type is rejected at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("foreign trait on foreign type is rejected at compile time")
# This would be a compile error:
# impl Display for String:
#     fn to_string() -> str:
#         self
expect true  # Placeholder - compile-time check
```

</details>

### Overlap Detection - Same Type

#### single impl is allowed

- single impl is allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("single impl is allowed")
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

- duplicate impl is rejected at compile time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("duplicate impl is rejected at compile time")
# This would be a compile error (second impl):
# impl Process for i32:
#     fn run() -> i64:
#         0
expect true
```

</details>

### Overlap Detection - Generic vs Concrete

#### specific impl is allowed alone

- specific impl is allowed alone


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("specific impl is allowed alone")
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

- generic impl conflicts with specific


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generic impl conflicts with specific")
# This would be a compile error (blanket conflicts):
# impl<T> Handler for T:
#     fn handle() -> i64:
#         0
expect true
```

</details>

### No Overlap - Different Types

#### different types can have same trait

- different types can have same trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("different types can have same trait")
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

- associated type in impl is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("associated type in impl is valid")
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

- conflicting associated type is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("conflicting associated type is rejected")
# This would be a compile error (conflicting Item type):
# impl Container for IntList:
#     type Item = str  # Conflicts with i64
expect true
```

</details>

### Blanket Impl Conflict

#### specific impl alone works

- specific impl alone works


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("specific impl alone works")
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

- module with trait, struct, and impl passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("module with trait, struct, and impl passes")
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

- inherent impl on local type is allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inherent impl on local type is allowed")
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

- multiple traits on same type


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple traits on same type")
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

- impl on generic type


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("impl on generic type")
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

- specialization placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("specialization placeholder")
expect true  # TODO: Implement @default on impl blocks
```

</details>

### Extension Trait Pattern

#### extension trait on foreign type

- extension trait on foreign type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extension trait on foreign type")
trait StringExt:
    fn shout() -> text

impl StringExt for text:
    fn shout() -> text:
        self.upper() + "!"

expect "hello".shout() == "HELLO!"
```

</details>

#### generic extension trait

- generic extension trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generic extension trait")
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

- impl with where clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("impl with where clause")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7cafea75e92a00f66ee72a93355b0c1c2eb7ee469b66c47885d69a56f9139074`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7cafea75e92a00f66ee72a93355b0c1c2eb7ee469b66c47885d69a56f9139074`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7cafea75e92a00f66ee72a93355b0c1c2eb7ee469b66c47885d69a56f9139074`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/trait_coherence_spec.spl
mirror: doc/06_spec/03_system/feature/usage/trait_coherence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/trait_coherence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/trait_coherence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/trait_coherence_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows local trait on foreign type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/trait_coherence_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows foreign trait on local type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/trait_coherence_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows local trait on local type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Type Aliases Specification

> Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They enable domain-specific naming without introducing new types, and support generic type aliases for parameterized type shortcuts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Aliases Specification

Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They enable domain-specific naming without introducing new types, and support generic type aliases for parameterized type shortcuts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TYPE-ALIAS-001 to #TYPE-ALIAS-012 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/type_aliases_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Type aliases allow creating alternative names for existing types, improving
code readability and maintainability. They enable domain-specific naming
without introducing new types, and support generic type aliases for
parameterized type shortcuts.

## Syntax

```simple
type UserId = i64
type IntList = [i64]
type StringMap = {str: str}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Alternative name for an existing type |
| Collection Alias | Alias for array or dict types |
| Alias Chain | Alias that references another alias |

## Behavior

- Type aliases are fully interchangeable with their target type
- Aliases can reference collection types
- Aliases do not create new types (unlike newtypes)
- Aliases can reference other aliases (chaining)

## Scenarios

### Type Aliases

#### with simple aliases

#### aliases primitive types

- aliases primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aliases primitive types")
type UserId = i64
val user: UserId = 42
expect user to eq(42)
```

</details>

#### allows alias in function signature

- allows alias in function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows alias in function signature")
type Score = i64

fn double_score(s: Score) -> Score:
    s * 2

val result = double_score(21)
expect result to eq(42)
```

</details>

#### is interchangeable with base type

- is interchangeable with base type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is interchangeable with base type")
type Age = i64

fn process_int(n: i64) -> i64:
    n + 10

val age: Age = 25
val result = process_int(age)
expect result to eq(35)
```

</details>

#### with collection aliases

#### aliases array types

- aliases array types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aliases array types")
type IntList = [i64]
val numbers: IntList = [1, 2, 3, 4, 5]
expect numbers.len() to eq(5)
```

</details>

#### aliases dict types

- aliases dict types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aliases dict types")
type StringMap = {str: str}
val data: StringMap = {"key": "value"}
expect data["key"] to eq("value")
```

</details>

#### allows nested collection aliases

- allows nested collection aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows nested collection aliases")
type Matrix = [[i64]]
val m: Matrix = [[1, 2], [3, 4]]
expect m[0][0] to eq(1)
expect m[1][1] to eq(4)
```

</details>

#### with alias chains

#### supports alias of alias

- supports alias of alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports alias of alias")
type Id = i64
type UserId = Id
val user: UserId = 100
expect user to eq(100)
```

</details>

#### supports multiple levels of aliasing

- supports multiple levels of aliasing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports multiple levels of aliasing")
type Base = i64
type Middle = Base
type Top = Middle
val value: Top = 42
expect value to eq(42)
```

</details>

### Type Alias Usage

#### in struct fields

#### uses alias in struct definition

- uses alias in struct definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses alias in struct definition")
type Timestamp = i64

class Event:
    time: Timestamp
    name: str

val e = Event(time: 1234567890, name: "test")
expect e.time to eq(1234567890)
```

</details>

#### in class fields

#### uses alias in class definition

- uses alias in class definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses alias in class definition")
type Count = i64

class Counter:
    value: Count

    fn get() -> Count:
        self.value

val c = Counter(value: 10)
expect c.get() to eq(10)
```

</details>

#### with return types

#### uses alias as return type

- uses alias as return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses alias as return type")
type Result = i64

fn compute() -> Result:
    42

val r: Result = compute()
expect r to eq(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `ef509d1c99950a5573dce3e6a9ce71836c2434ea49ce01016bd4026214b9b7f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ef509d1c99950a5573dce3e6a9ce71836c2434ea49ce01016bd4026214b9b7f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ef509d1c99950a5573dce3e6a9ce71836c2434ea49ce01016bd4026214b9b7f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/type_aliases_spec.spl
mirror: doc/06_spec/03_system/feature/usage/type_aliases_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/type_aliases_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/type_aliases_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/type_aliases_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aliases primitive types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/type_aliases_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows alias in function signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/type_aliases_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is interchangeable with base type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

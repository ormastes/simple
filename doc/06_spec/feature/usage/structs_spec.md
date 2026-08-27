# Structs Specification

> Structs are user-defined data types that group related fields together. They support named fields with type annotations, default values, and can have methods defined via impl blocks. Structs are the primary way to define custom data structures in Simple.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Structs Specification

Structs are user-defined data types that group related fields together. They support named fields with type annotations, default values, and can have methods defined via impl blocks. Structs are the primary way to define custom data structures in Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/structs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Structs are user-defined data types that group related fields together.
They support named fields with type annotations, default values, and can
have methods defined via impl blocks. Structs are the primary way to
define custom data structures in Simple.

## Syntax

```simple
struct Point:
x: i64
y: i64

struct Config:
host: String = "localhost"
port: i64 = 8080

use std.spec.step

val p = Point { x: 3, y: 4 }
val c = Config { port: 9000 }  # host uses default
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Struct | User-defined data type with named fields |
| Field | Named member of a struct with type annotation |
| Default Value | Optional value used when field not provided |
| Construction | Creating struct instance with field values |

## Behavior

- Fields are accessed using dot notation: `point.x`
- Construction requires all fields without defaults
- Fields can have default values
- Structs are value types (copied by default)

## Scenarios

### Structs

#### struct definition and construction

#### defines struct with fields

- defines struct with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines struct with fields")
struct Point:
    x: i64
    y: i64

val p = Point { x: 10, y: 20 }
expect p.x + p.y == 30
```

</details>

#### constructs struct with all fields

- constructs struct with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("constructs struct with all fields")
struct Config:
    host: str
    port: i64

val c = Config { host: "localhost", port: 8080 }
expect c.port == 8080
```

</details>

#### struct field access

#### accesses struct fields

- accesses struct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses struct fields")
struct Rectangle:
    width: i64
    height: i64

val r = Rectangle { width: 10, height: 5 }
expect r.width * r.height == 50
```

</details>

### Impl Blocks

#### adds method to struct

- adds method to struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds method to struct")
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

val p = Point { x: 15, y: 25 }
expect p.sum() == 40
```

</details>

#### adds method with arguments

- adds method with arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds method with arguments")
struct Counter:
    value: i64

impl Counter:
    fn add(self, n):
        return self.value + n

val c = Counter { value: 10 }
expect c.add(5) == 15
```

</details>

### Classes

#### defines class with static method

- defines class with static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines class with static method")
class Calculator:
    static fn add(a, b):
        return a + b

expect Calculator.add(3, 4) == 7
```

</details>

### Context Blocks

#### dispatches methods to context object

- dispatches methods to context object


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dispatches methods to context object")
class Calculator:
    fn double(self, x):
        return x * 2

val calc = Calculator {}
var res = 0
context calc:
    res = double(21)
expect res == 42
```

</details>

#### accesses self fields in context

- accesses self fields in context


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accesses self fields in context")
class Adder:
    base: i64 = 10

    fn add(self, x):
        return self.base + x

val a = Adder { base: 30 }
var res = 0
context a:
    res = add(12)
expect res == 42
```

</details>

### Method Missing

#### calls method_missing for unknown method

- calls method_missing for unknown method


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls method_missing for unknown method")
class DSL:
    fn method_missing(self, name, args, block):
        return 42

val d = DSL {}
expect d.unknown_method() == 42
```

</details>

#### passes arguments to method_missing

- passes arguments to method_missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes arguments to method_missing")
class Multiplier:
    factor: i64 = 10

    fn method_missing(self, name, args, block):
        val x = args[0]
        return self.factor * x

val m = Multiplier { factor: 7 }
expect m.any_method(6) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `a17b6f714e96f0599ff40347379b4c278ad0952f8537497ee60af5f81eaa401b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a17b6f714e96f0599ff40347379b4c278ad0952f8537497ee60af5f81eaa401b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a17b6f714e96f0599ff40347379b4c278ad0952f8537497ee60af5f81eaa401b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/structs_spec.spl
mirror: doc/06_spec/feature/usage/structs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/structs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/structs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/structs_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines struct with fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/structs_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs struct with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/structs_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accesses struct fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

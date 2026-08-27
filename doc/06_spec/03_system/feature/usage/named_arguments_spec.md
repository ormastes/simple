# Named Arguments Specification

> Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enabling flexible argument ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Named Arguments Specification

Tests for named argument support allowing function calls with explicit parameter names, improving code clarity and enabling flexible argument ordering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NAMED-ARGS-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/03_system/feature/usage/named_arguments_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for named argument support allowing function calls with explicit
parameter names, improving code clarity and enabling flexible argument ordering.

## Syntax

```simple
use std.spec.step

fn create_user(name: text, email: text, age: i64) -> User:
User(name: name, email: email, age: age)

# Call with positional arguments
val user1 = create_user("Alice", "alice@example.com", 30)

# Call with named arguments
val user2 = create_user(age=25, name="Bob", email="bob@example.com")

# Mixed positional and named
val user3 = create_user("Charlie", email="charlie@example.com", age=35)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named Argument | Explicitly passing parameter by name |
| Positional Argument | Passing argument by position order |
| Argument Reordering | Non-positional order with named arguments |
| Default Values | Optional parameters with defaults |
| Clarity | Improved code readability with explicit parameter names |

## Behavior

- Named arguments can be passed in any order
- Positional arguments must precede named arguments (if mixed)
- Parameter names are part of the function signature
- Type checking applies to named arguments like positional
- Named arguments cannot be repeated in a single call
- Works with constructors and regular functions

## Scenarios

### Named Arguments Basic Usage

#### calls function with named arguments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls function with named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls function with named arguments")
fn greet(name, greeting):
    return 1
expect greet(name="world", greeting="hello") == 1
```

</details>

#### passes values correctly with named arguments

- passes values correctly with named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes values correctly with named arguments")
fn add(a, b):
    return a + b
expect add(a=10, b=20) == 30
```

</details>

#### works with string values

- works with string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with string values")
fn concat(first, second):
    return first + second
val result = concat(first="Hello", second=" World")
var r = 0
if result == "Hello World":
    r = 1
expect r == 1
```

</details>

### Named Arguments Reordering

#### allows reversed argument order

- allows reversed argument order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reversed argument order")
fn sub(a, b):
    return a - b
expect sub(b=10, a=30) == 20
```

</details>

#### reorders three arguments

- reorders three arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reorders three arguments")
fn calc(x, y, z):
    return x + y * z
expect calc(z=4, x=2, y=3) == 14
```

</details>

#### reorders with different calculation

- reorders with different calculation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reorders with different calculation")
fn compute(first, second, third):
    return first * 100 + second * 10 + third
expect compute(third=3, first=1, second=2) == 123
```

</details>

### Mixed Positional and Named Arguments

#### mixes positional and named arguments

- mixes positional and named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixes positional and named arguments")
fn calc(x, y, z):
    return x + y * z
expect calc(2, z=4, y=3) == 14
```

</details>

#### uses positional first then named

- uses positional first then named


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses positional first then named")
fn process(a, b, c):
    return a * b + c
expect process(5, c=7, b=3) == 22
```

</details>

#### uses single positional with multiple named

- uses single positional with multiple named


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses single positional with multiple named")
fn combine(base, mult, add):
    return base * mult + add
expect combine(10, add=5, mult=2) == 25
```

</details>

### Named Arguments with Defaults

#### uses default when argument not provided

- uses default when argument not provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default when argument not provided")
fn add(a, b=10):
    return a + b
expect add(5) == 15
```

</details>

#### overrides default with named argument

- overrides default with named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides default with named argument")
fn add(a, b=10):
    return a + b
expect add(5, b=20) == 25
```

</details>

#### works with multiple defaults

- works with multiple defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with multiple defaults")
fn calculate(x, y=2, z=3):
    return x + y * z
expect calculate(1) == 7
expect calculate(1, y=5) == 16
expect calculate(1, z=10) == 21
```

</details>

### Named Arguments in Methods

#### uses named arguments with class methods

- uses named arguments with class methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses named arguments with class methods")
class Calculator:
    fn compute(self, a, b):
        return a * b

val calc = Calculator {}
expect calc.compute(a=6, b=7) == 42
```

</details>

#### reorders method arguments

- reorders method arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reorders method arguments")
class Math:
    fn subtract(self, minuend, subtrahend):
        return minuend - subtrahend

val m = Math {}
expect m.subtract(subtrahend=15, minuend=50) == 35
```

</details>

### Named Arguments Edge Cases

#### handles single named argument

- handles single named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single named argument")
fn identity(x):
    return x
expect identity(x=42) == 42
```

</details>

#### handles many named arguments

- handles many named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles many named arguments")
fn sum5(a, b, c, d, e):
    return a + b + c + d + e
expect sum5(e=5, d=4, c=3, b=2, a=1) == 15
```

</details>

#### works with nested function calls

- works with nested function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with nested function calls")
fn double(x):
    return x * 2
fn add(a, b):
    return a + b
expect add(a=double(x=5), b=double(x=3)) == 16
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `a3a53b38391bcd015cc6e5cd3134474525f236d400d22d41a2a61293a35ba123`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3a53b38391bcd015cc6e5cd3134474525f236d400d22d41a2a61293a35ba123`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3a53b38391bcd015cc6e5cd3134474525f236d400d22d41a2a61293a35ba123`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/named_arguments_spec.spl
mirror: doc/06_spec/03_system/feature/usage/named_arguments_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/named_arguments_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/named_arguments_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/named_arguments_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls function with named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_arguments_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes values correctly with named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_arguments_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with string values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

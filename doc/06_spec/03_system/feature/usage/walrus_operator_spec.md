# Walrus Operator

> Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bindings (integer, text, boolean, nil, float), expression evaluation, function call results, string concatenation, arrays, equivalence with val, nested scopes, control flow usage (if, loops, match), complex types (nested arrays, struct literals), and edge cases.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Walrus Operator

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating immutable bindings. Covers basic bindings (integer, text, boolean, nil, float), expression evaluation, function call results, string concatenation, arrays, equivalence with val, nested scopes, control flow usage (if, loops, match), complex types (nested arrays, struct literals), and edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-004 |
| Category | Syntax |
| Status | Active |
| Source | `test/03_system/feature/usage/walrus_operator_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `:=` walrus operator as syntactic sugar for `val` declarations creating
immutable bindings. Covers basic bindings (integer, text, boolean, nil, float),
expression evaluation, function call results, string concatenation, arrays,
equivalence with val, nested scopes, control flow usage (if, loops, match),
complex types (nested arrays, struct literals), and edge cases.

## Syntax

```simple
x := 42
name := "Alice"
result := 10 + 32
numbers := [1, 2, 3]
```
Walrus Operator Specification

Tests the := operator as syntactic sugar for val declarations.
x := value is equivalent to val x = value (immutable binding)

## Scenarios

### Walrus Operator Basics

#### creates binding with integer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates binding with integer
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates binding with integer")
val x = 42
expect(x).to_equal(42)
```

</details>

#### creates binding with text

- creates binding with text
   - Expected: name equals `Alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates binding with text")
val name = "Alice"
expect(name).to_equal("Alice")
```

</details>

#### creates binding with boolean

- creates binding with boolean
   - Expected: flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates binding with boolean")
val flag = true
expect(flag).to_equal(true)
```

</details>

#### creates binding with nil

- creates binding with nil
   - Expected: value equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates binding with nil")
val value = nil
expect(value).to_equal(nil)
```

</details>

#### creates binding with float

- creates binding with float
   - Expected: pi equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates binding with float")
val pi = 3.14
expect(pi).to_equal(3.14)
```

</details>

### Walrus Operator with Expressions

#### evaluates expression on right side

- evaluates expression on right side
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates expression on right side")
val result = 10 + 32
expect(result).to_equal(42)
```

</details>

#### works with function calls

- works with function calls
   - Expected: val_from_fn equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with function calls")
fn get_value() -> i64:
    100
val val_from_fn = get_value()
expect(val_from_fn).to_equal(100)
```

</details>

#### works with string concatenation

- works with string concatenation
   - Expected: greeting equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with string concatenation")
val greeting = "Hello" + " " + "World"
expect(greeting).to_equal("Hello World")
```

</details>

#### works with arrays

- works with arrays
   - Expected: numbers[0] equals `1`
   - Expected: numbers.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with arrays")
val numbers = [1, 2, 3]
expect(numbers[0]).to_equal(1)
expect(numbers.len()).to_equal(3)
```

</details>

### Walrus Operator Semantics

#### creates immutable binding

- creates immutable binding
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates immutable binding")
val count = 5
expect(count).to_equal(5)
```

</details>

#### is equivalent to val declaration

- is equivalent to val declaration
   - Expected: x equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is equivalent to val declaration")
val x = 10
val y = 10
expect(x).to_equal(y)
```

</details>

#### works in nested scopes

- works in nested scopes
   - Expected: outer() equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in nested scopes")
fn outer():
    val x = 100
    fn inner():
        val y = 200
        x + y
    inner()
expect(outer()).to_equal(300)
```

</details>

### Walrus Operator in Functions

#### works in function body

- works in function body
   - Expected: test_walrus() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in function body")
fn test_walrus():
    val local = 42
    local
expect(test_walrus()).to_equal(42)
```

</details>

#### works with multiple bindings

- works with multiple bindings
   - Expected: multi_walrus() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with multiple bindings")
fn multi_walrus():
    val a = 1
    val b = 2
    val c = 3
    a + b + c
expect(multi_walrus()).to_equal(6)
```

</details>

#### works with shadowing in nested scopes

- works with shadowing in nested scopes
   - Expected: inner() equals `20`
   - Expected: outer_x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with shadowing in nested scopes")
val outer_x = 10
fn inner():
    val inner_x = 20
    inner_x
expect(inner()).to_equal(20)
expect(outer_x).to_equal(10)
```

</details>

### Walrus Operator in Control Flow

#### works in if branches

- works in if branches
   - Expected: val_in_if equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in if branches")
if true:
    val val_in_if = 42
    expect(val_in_if).to_equal(42)
```

</details>

<details>
<summary>Advanced: works in loops</summary>

#### works in loops

- works in loops
   - Expected: run_loop() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in loops")
fn run_loop() -> i64:
    var total = 0
    var i = 0
    while i < 3:
        val x = i * 10
        total = total + x
        i = i + 1
    total
expect(run_loop()).to_equal(30)
```

</details>


</details>

#### works in match cases

- works in match cases
   - Expected: run_match() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works in match cases")
fn run_match() -> text:
    val value = 2
    val label = "two"
    label
expect(run_match()).to_equal("two")
```

</details>

### Walrus Operator with Complex Types

#### works with nested arrays

- works with nested arrays
   - Expected: matrix[0][0] equals `1`
   - Expected: matrix.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with nested arrays")
val matrix = [[1, 2], [3, 4]]
expect(matrix[0][0]).to_equal(1)
expect(matrix.len()).to_equal(2)
```

</details>

#### works with struct literals

- works with struct literals
   - Expected: point.x equals `10`
   - Expected: point.y equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with struct literals")
val point = Point(x: 10, y: 20)
expect(point.x).to_equal(10)
expect(point.y).to_equal(20)
```

</details>

### Walrus Operator Edge Cases

#### handles parenthesized expressions

- handles parenthesized expressions
   - Expected: val_paren equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles parenthesized expressions")
val val_paren = (10 + 20)
expect(val_paren).to_equal(30)
```

</details>

#### handles chained operations

- handles chained operations
   - Expected: chained equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles chained operations")
val chained = 1 + 2 + 3 + 4
expect(chained).to_equal(10)
```

</details>

#### handles boolean expressions

- handles boolean expressions
   - Expected: is_true is true
   - Expected: is_false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles boolean expressions")
val is_true = true and true
val is_false = true and false
expect(is_true).to_equal(true)
expect(is_false).to_equal(false)
```

</details>

### Walrus vs Regular Assignment

#### walrus creates new binding

- walrus creates new binding
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("walrus creates new binding")
val x = 10
expect(x).to_equal(10)
```

</details>

#### regular assignment requires val/var

- regular assignment requires val/var
   - Expected: y equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("regular assignment requires val/var")
val y = 20
expect(y).to_equal(20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `babd54f8540d8b17befaeeeb2dd75c5d87964f97877de42c9c6d4a908723e056`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `babd54f8540d8b17befaeeeb2dd75c5d87964f97877de42c9c6d4a908723e056`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `babd54f8540d8b17befaeeeb2dd75c5d87964f97877de42c9c6d4a908723e056`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/walrus_operator_spec.spl
mirror: doc/06_spec/03_system/feature/usage/walrus_operator_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/walrus_operator_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/walrus_operator_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/walrus_operator_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/walrus_operator_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates binding with integer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/walrus_operator_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates binding with text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/walrus_operator_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates binding with boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

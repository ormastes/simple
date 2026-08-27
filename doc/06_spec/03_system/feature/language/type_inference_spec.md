# Type Inference Specification - Test Specification

> Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification - Test Specification

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #13 |
| Category | Other |
| Status | Partial Implementation (Hindley-Milner scaffold working) |
| Type | Extracted Examples (Category B) |
| Reference | type_inference.md |
| Source | `test/03_system/feature/language/type_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple uses a Hindley-Milner-style type inference system that automatically deduces types
for expressions, variables, and functions without requiring explicit type annotations.

This test file covers basic type inference rules that work in the current runtime.

## Syntax

Type annotations are optional when the type can be inferred:

    val x = 42          # inferred: i64
    val y = 3.14        # inferred: f64
    val s = "hello"     # inferred: text
    val b = true        # inferred: bool

Function return types are inferred from the body:

    fn double(x: i64) -> _:   # _ = inferred i64
        x * 2

Generic instantiation inferred from arguments:

    fn identity<T>(x: T) -> T: x

    val a = identity(5)     # T inferred as i64
    val b = identity("hi")  # T inferred as text

Bidirectional inference from expected type:

    val nums: [i64] = [1, 2, 3]  # list element type inferred

## Examples

    val x = 42
    val y = x + 8    # => 50  (i64 propagated through arithmetic)

    val flag = x > 10    # => true  (bool from comparison)

    fn square(n: i64) -> i64: n * n
    square(7)   # => 49  (no annotation needed at call site)

    val words = ["a", "b", "c"]
    words.len()  # => 3  (list type inferred as [text])

## Key Concepts

**Hindley-Milner (HM)** — Simple's inference algorithm is based on HM with
extensions. Every expression has a principal type that is uniquely inferred
without programmer annotations (except at module boundaries for public APIs).

**Unification** — the inference engine collects equality constraints between
type variables and solves them. A conflict (e.g., using an `i64` where
`text` is expected) is caught at unification, not at run time.

**Generalization** — at let-bindings, free type variables are generalised
into universally quantified type schemes, enabling reuse with different
concrete types.

**Bidirectional inference** — expected types (from context) flow inward;
synthesised types (from expressions) flow outward. This reduces annotation
burden on lambda arguments and collection literals.

**Annotation escapes** — public API boundaries require explicit type
annotations so that library consumers get stable, documented types instead
of inferred internals that could change across versions.

**Rank-1 polymorphism** — Simple infers rank-1 (prenex) types by default.
Higher-rank types require explicit annotations and are rare in practice.

## Common Patterns

Let-bound generics (inferred at each use site):

    val id = |x| x         # type: <T> (T) -> T
    id(5)                   # => 5  (T = i64)
    id("hi")                # => "hi" (T = text)

Inference through `match`:

    val result = match flag:
        true  => 1
        false => 0
    # result: i64 (both branches unify)

Collection literal with inferred element type:

    val nums = [1, 2, 3]    # [i64]
    val tags = ["a", "b"]   # [text]

Closure return type inferred from body:

    val square = |x: i64| x * x   # (i64) -> i64 — no annotation needed

## Scenarios

### Type Inference Spec

#### inference rules - literals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- inference rules - literals
   - Expected: x equals `42`
   - Expected: y equals `3.14`
   - Expected: s equals `hello`
   - Expected: b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - literals")
# Integer, float, string, boolean literals infer their types
val x = 42
val y = 3.14
val s = "hello"
val b = true
expect(x).to_equal(42)
expect(y).to_equal(3.14)
expect(s).to_equal("hello")
expect(b).to_equal(true)
```

</details>

#### inference rules - arithmetic

- inference rules - arithmetic
   - Expected: a equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - arithmetic")
# Operators infer types from operands
val a = 1 + 2
val b = 3.0 * 1.5
expect(a).to_equal(3)
```

</details>

#### inference rules - comparison

- inference rules - comparison
   - Expected: cmp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - comparison")
# Comparison operators return bool
val cmp = 1 < 2
expect(cmp).to_equal(true)
```

</details>

#### inference rules - logical

- inference rules - logical
   - Expected: logic is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - logical")
# Logical operators return bool
val logic = true and false
expect(logic).to_equal(false)
```

</details>

#### inference rules - bitwise

- inference rules - bitwise
   - Expected: bits equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - bitwise")
# Bitwise operators work on integers
val bits = 5 << 2
expect(bits).to_equal(20)
```

</details>

#### inference rules - arrays

- inference rules - arrays
   - Expected: arr[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - arrays")
# Arrays infer element type from literals
val arr = [1, 2, 3]
expect(arr[0]).to_equal(1)
```

</details>

#### inference rules - tuples

- inference rules - tuples
   - Expected: t.0 equals `1`
   - Expected: t.1 equals `hi`
   - Expected: t.2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - tuples")
# Tuples can have mixed types
val t = (1, "hi", true)
expect(t.0).to_equal(1)
expect(t.1).to_equal("hi")
expect(t.2).to_equal(true)
```

</details>

#### inference rules - dictionaries

- inference rules - dictionaries
   - Expected: dict["a"] equals `1`
   - Expected: dict["b"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - dictionaries")
# Dictionaries infer key/value types
val dict = {"a": 1, "b": 2}
expect(dict["a"]).to_equal(1)
expect(dict["b"]).to_equal(2)
```

</details>

#### inference rules - functions with explicit types

- inference rules - functions with explicit types
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - functions with explicit types")
# Functions can have explicit return types
fn add(a: i64, b: i64) -> i64:
    a + b
val result = add(3, 4)
expect(result).to_equal(7)
```

</details>

#### inference rules - lambda types

- inference rules - lambda types
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - lambda types")
# Lambda expressions infer from context
val double = _1 * 2
val result = double(5)
expect(result).to_equal(10)
```

</details>

#### inference rules - higher-order functions

- inference rules - higher-order functions
   - Expected: result equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - higher-order functions")
# Functions can take functions as arguments
fn apply(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)

val square = _1 * _1
val result = apply(square, 5)
expect(result).to_equal(25)
```

</details>

#### inference rules - if expressions

- inference rules - if expressions
   - Expected: v equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - if expressions")
# If-else expressions infer unified type
val x = 1
val v = if x > 0:
    1
else:
    2
expect(v).to_equal(1)
```

</details>

<details>
<summary>Advanced: inference rules - loops</summary>

#### inference rules - loops

- inference rules - loops
   - Expected: i equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inference rules - loops")
# Loops with type-stable variables
# Note: Closure variable capture has known limitations
var i = 0
while i < 3:
    i = i + 1
expect(i).to_equal(3)
```

</details>


</details>

#### examples - basic iteration

- examples - basic iteration
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("examples - basic iteration")
# For loop with array inference
val numbers = [1, 2, 3, 4, 5]
var sum = 0
for n in numbers:
    sum = sum + n
expect(sum).to_equal(15)
```

</details>

#### examples - map function

- examples - map function
   - Expected: doubled[0] equals `2`
   - Expected: doubled[1] equals `4`
   - Expected: doubled[2] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("examples - map function")
# Higher-order function with generics
fn map_simple(arr: [i64], f: fn(i64) -> i64) -> [i64]:
    var result = []
    for x in arr:
        result = result + [f(x)]
    result

val numbers = [1, 2, 3]
val doubled = map_simple(numbers, _1 * 2)
expect(doubled[0]).to_equal(2)
expect(doubled[1]).to_equal(4)
expect(doubled[2]).to_equal(6)
```

</details>

#### examples - option type with match

- examples - option type with match
   - Expected: found equals `20`
   - Expected: not_found equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("examples - option type with match")
# Option type with pattern matching
fn find_first(arr: [i64], target: i64) -> i64:
    for x in arr:
        if x == target:
            return x
    return -1

val numbers = [10, 20, 30]
val found = find_first(numbers, 20)
val not_found = find_first(numbers, 99)

expect(found).to_equal(20)
expect(not_found).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `8c8011b94ac533552a204825d1b8efa3d231016077439c3e95a0adb9a5289849`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c8011b94ac533552a204825d1b8efa3d231016077439c3e95a0adb9a5289849`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c8011b94ac533552a204825d1b8efa3d231016077439c3e95a0adb9a5289849`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/language/type_inference_spec.spl
mirror: doc/06_spec/03_system/feature/language/type_inference_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/language/type_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/language/type_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/language/type_inference_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/language/type_inference_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inference rules - literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/type_inference_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inference rules - arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/language/type_inference_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inference rules - comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

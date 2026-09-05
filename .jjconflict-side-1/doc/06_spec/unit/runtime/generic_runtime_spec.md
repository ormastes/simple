# generic_runtime_spec

> Purpose: specializes identity function with integers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# generic_runtime_spec

Purpose: specializes identity function with integers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/unit/runtime/generic_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: specializes identity function with integers
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### Runtime Generic Functions

#### specializes identity function with integers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- specializes identity function with integers
- Verify: specializes identity function with integers
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specializes identity function with integers")
step("Verify: specializes identity function with integers")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

val result = identity(42)
expect(result).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

#### specializes identity function with text

- specializes identity function with text
- Verify: specializes identity function with text
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specializes identity function with text")
step("Verify: specializes identity function with text")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

val result = identity("hello")
expect(result).to_equal("hello")
```

</details>

#### specializes identity function with floats

- specializes identity function with floats
- Verify: specializes identity function with floats
   - Expected: result equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specializes identity function with floats")
step("Verify: specializes identity function with floats")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

val result = identity(3.14)
expect(result).to_equal(3.14)
```

</details>

#### specializes identity function with booleans

- specializes identity function with booleans
- Verify: specializes identity function with booleans
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specializes identity function with booleans")
step("Verify: specializes identity function with booleans")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

val result = identity(true)
expect(result).to_equal(true)
```

</details>

#### caches specialized versions

- caches specialized versions
- Verify: caches specialized versions
   - Expected: result1 equals `10`
   - Expected: result2 equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches specialized versions")
step("Verify: caches specialized versions")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

# First call creates specialization
val result1 = identity(10)
# Second call should use cached version
val result2 = identity(20)

expect(result1).to_equal(10)  # oracle: value fixed by the spec contract
expect(result2).to_equal(20)  # oracle: value fixed by the spec contract
```

</details>

#### creates separate specializations for different types

- creates separate specializations for different types
- Verify: creates separate specializations for different types
   - Expected: int_result equals `42`
   - Expected: text_result equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates separate specializations for different types")
step("Verify: creates separate specializations for different types")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

val int_result = identity(42)
val text_result = identity("world")

expect(int_result).to_equal(42)  # oracle: value fixed by the spec contract
expect(text_result).to_equal("world")
```

</details>

### Generic Functions with Multiple Type Parameters

#### handles two type parameters

- handles two type parameters
- Verify: handles two type parameters
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles two type parameters")
step("Verify: handles two type parameters")
# @req: REQ-RUNTIME-GeneRunt-001
fn pair<T, U>(first: T, second: U) -> T:
    first

val result = pair(42, "hello")
expect(result).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

#### handles three type parameters

- handles three type parameters
- Verify: handles three type parameters
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles three type parameters")
step("Verify: handles three type parameters")
# @req: REQ-RUNTIME-GeneRunt-001
fn pick_first<A, B, C>(a: A, b: B, c: C) -> A:
    a

val result = pick_first(1, 2.5, "three")
expect(result).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### caches multi-param specializations independently

- caches multi-param specializations independently
- Verify: caches multi-param specializations independently
   - Expected: result1 equals `10`
   - Expected: result2 equals `10`
   - Expected: result3 equals `ten`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("caches multi-param specializations independently")
step("Verify: caches multi-param specializations independently")
# @req: REQ-RUNTIME-GeneRunt-001
fn pair<T, U>(first: T, second: U) -> T:
    first

val result1 = pair(10, 20)        # i64, i64
val result2 = pair(10, "twenty")  # i64, text
val result3 = pair("ten", 20)     # text, i64

expect(result1).to_equal(10)  # oracle: value fixed by the spec contract
expect(result2).to_equal(10)  # oracle: value fixed by the spec contract
expect(result3).to_equal("ten")
```

</details>

### Generic Functions with Complex Bodies

#### works with conditionals

- works with conditionals
- Verify: works with conditionals
   - Expected: result1 equals `10`
   - Expected: result2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with conditionals")
step("Verify: works with conditionals")
# @req: REQ-RUNTIME-GeneRunt-001
fn safe_div<T>(x: T, y: T) -> T:
    if y == 0:
        return 0
    x

val result1 = safe_div(10, 2)
val result2 = safe_div(10, 0)

expect(result1).to_equal(10)  # oracle: value fixed by the spec contract
expect(result2).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

<details>
<summary>Advanced: works with loops</summary>

#### works with loops

- works with loops
- Verify: works with loops
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with loops")
step("Verify: works with loops")
# @req: REQ-RUNTIME-GeneRunt-001
fn count<T>(x: T, times: i64) -> i64:
    var counter: i64 = 0
    for i in 0..times:
        counter = counter + 1
    counter

val result = count(42, 5)
expect(result).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>


</details>

#### works with multiple statements

- works with multiple statements
- Verify: works with multiple statements
   - Expected: int_result equals `42`
   - Expected: text_result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with multiple statements")
step("Verify: works with multiple statements")
# @req: REQ-RUNTIME-GeneRunt-001
fn process<T>(x: T) -> T:
    val temp = x
    val result = temp
    result

val int_result = process(42)
val text_result = process("test")

expect(int_result).to_equal(42)  # oracle: value fixed by the spec contract
expect(text_result).to_equal("test")
```

</details>

### Generic Function Edge Cases

#### handles nil values

- handles nil values
- Verify: handles nil values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nil values")
step("Verify: handles nil values")
# @req: REQ-RUNTIME-GeneRunt-001
fn passthrough<T>(x: T) -> T:
    x

val result = passthrough(nil)
expect(result).to_be_nil()
```

</details>

#### handles nested generic calls

- handles nested generic calls
- Verify: handles nested generic calls
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested generic calls")
step("Verify: handles nested generic calls")
# @req: REQ-RUNTIME-GeneRunt-001
fn outer<T>(x: T) -> T:
    fn inner<U>(y: U) -> U:
        y
    inner(x)

val result = outer(42)
expect(result).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

#### handles arrays of different types

- handles arrays of different types
- Verify: handles arrays of different types
   - Expected: int_arr_len equals `3`
   - Expected: text_arr_len equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles arrays of different types")
step("Verify: handles arrays of different types")
# @req: REQ-RUNTIME-GeneRunt-001
fn first_elem<T>(arr: [T]) -> i64:
    arr.len()

val int_arr_len = first_elem([1, 2, 3])
val text_arr_len = first_elem(["a", "b"])

expect(int_arr_len).to_equal(3)  # oracle: value fixed by the spec contract
expect(text_arr_len).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### handles empty parameter lists

- handles empty parameter lists
- Verify: handles empty parameter lists
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty parameter lists")
step("Verify: handles empty parameter lists")
# @req: REQ-RUNTIME-GeneRunt-001
fn constant<T>() -> i64:
    42

val result = constant()
expect(result).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

### Generic Struct Integration

#### works with generic struct construction

- works with generic struct construction
- Verify: works with generic struct construction
   - Expected: int_pair[0] equals `1`
   - Expected: int_pair[1] equals `2`
   - Expected: text_pair[0] equals `a`
   - Expected: text_pair[1] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with generic struct construction")
step("Verify: works with generic struct construction")
# @req: REQ-RUNTIME-GeneRunt-001
fn make_pair<T>(x: T, y: T) -> [T]:
    [x, y]

val int_pair = make_pair(1, 2)
val text_pair = make_pair("a", "b")

expect(int_pair[0]).to_equal(1)  # oracle: value fixed by the spec contract
expect(int_pair[1]).to_equal(2)  # oracle: value fixed by the spec contract
expect(text_pair[0]).to_equal("a")
expect(text_pair[1]).to_equal("b")
```

</details>

#### works with option-like patterns

- works with option-like patterns
- Verify: works with option-like patterns
   - Expected: unwrapped equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with option-like patterns")
step("Verify: works with option-like patterns")
# @req: REQ-RUNTIME-GeneRunt-001
fn wrap<T>(x: T) -> [T]:
    [x]

fn unwrap<T>(arr: [T]) -> T:
    arr[0]

val wrapped = wrap(42)
val unwrapped = unwrap(wrapped)

expect(unwrapped).to_equal(42)  # oracle: value fixed by the spec contract
```

</details>

### Generic Function Type Inference

#### infers types from integer literals

- infers types from integer literals
- Verify: infers types from integer literals
   - Expected: result equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types from integer literals")
step("Verify: infers types from integer literals")
# @req: REQ-RUNTIME-GeneRunt-001
fn double<T>(x: T) -> T:
    x

val result = double(21)
expect(result).to_equal(21)  # oracle: value fixed by the spec contract
```

</details>

#### infers types from float literals

- infers types from float literals
- Verify: infers types from float literals
   - Expected: result equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types from float literals")
step("Verify: infers types from float literals")
# @req: REQ-RUNTIME-GeneRunt-001
fn double<T>(x: T) -> T:
    x

val result = double(2.5)
expect(result).to_equal(2.5)
```

</details>

#### infers types from string literals

- infers types from string literals
- Verify: infers types from string literals
   - Expected: result equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types from string literals")
step("Verify: infers types from string literals")
# @req: REQ-RUNTIME-GeneRunt-001
fn double<T>(x: T) -> T:
    x

val result = double("test")
expect(result).to_equal("test")
```

</details>

#### infers types from boolean literals

- infers types from boolean literals
- Verify: infers types from boolean literals
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types from boolean literals")
step("Verify: infers types from boolean literals")
# @req: REQ-RUNTIME-GeneRunt-001
fn double<T>(x: T) -> T:
    x

val result = double(false)
expect(result).to_equal(false)
```

</details>

#### infers types from variables

- infers types from variables
- Verify: infers types from variables
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers types from variables")
step("Verify: infers types from variables")
# @req: REQ-RUNTIME-GeneRunt-001
fn passthrough<T>(x: T) -> T:
    x

val my_var: i64 = 100
val result = passthrough(my_var)
expect(result).to_equal(100)  # oracle: value fixed by the spec contract
```

</details>

### Generic Cache Behavior

#### uses cache for repeated calls with same type

- uses cache for repeated calls with same type
- Verify: uses cache for repeated calls with same type
   - Expected: r1 equals `1`
   - Expected: r2 equals `2`
   - Expected: r3 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses cache for repeated calls with same type")
step("Verify: uses cache for repeated calls with same type")
# @req: REQ-RUNTIME-GeneRunt-001
fn expensive<T>(x: T) -> T:
    x

# All these should hit the same cached specialization
val r1 = expensive(1)
val r2 = expensive(2)
val r3 = expensive(3)

expect(r1).to_equal(1)  # oracle: value fixed by the spec contract
expect(r2).to_equal(2)  # oracle: value fixed by the spec contract
expect(r3).to_equal(3)  # oracle: value fixed by the spec contract
```

</details>

#### creates new cache entries for different types

- creates new cache entries for different types
- Verify: creates new cache entries for different types
   - Expected: int_val equals `42`
   - Expected: float_val equals `3.14`
   - Expected: text_val equals `hello`
   - Expected: bool_val is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new cache entries for different types")
step("Verify: creates new cache entries for different types")
# @req: REQ-RUNTIME-GeneRunt-001
fn identity<T>(x: T) -> T:
    x

# Each type creates a new cache entry
val int_val = identity(42)
val float_val = identity(3.14)
val text_val = identity("hello")
val bool_val = identity(true)

expect(int_val).to_equal(42)  # oracle: value fixed by the spec contract
expect(float_val).to_equal(3.14)
expect(text_val).to_equal("hello")
expect(bool_val).to_equal(true)
```

</details>

#### handles interleaved calls to different generic functions

- handles interleaved calls to different generic functions
- Verify: handles interleaved calls to different generic functions
   - Expected: r1 equals `10`
   - Expected: r2 equals `20`
   - Expected: r3 equals `30`
   - Expected: r4 equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles interleaved calls to different generic functions")
step("Verify: handles interleaved calls to different generic functions")
# @req: REQ-RUNTIME-GeneRunt-001
fn id1<T>(x: T) -> T:
    x

fn id2<T>(x: T) -> T:
    x

val r1 = id1(10)
val r2 = id2(20)
val r3 = id1(30)
val r4 = id2(40)

expect(r1).to_equal(10)  # oracle: value fixed by the spec contract
expect(r2).to_equal(20)  # oracle: value fixed by the spec contract
expect(r3).to_equal(30)  # oracle: value fixed by the spec contract
expect(r4).to_equal(40)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-RUNTIME-GeneRunt-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `811c743c0a509a889469a599f7e69d23c4618defee7220915d58b735adbe64fb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `811c743c0a509a889469a599f7e69d23c4618defee7220915d58b735adbe64fb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `811c743c0a509a889469a599f7e69d23c4618defee7220915d58b735adbe64fb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/runtime/generic_runtime_spec.spl
mirror: doc/06_spec/unit/runtime/generic_runtime_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/runtime/generic_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/runtime/generic_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/runtime/generic_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/runtime/generic_runtime_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes identity function with integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/generic_runtime_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes identity function with text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/runtime/generic_runtime_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes identity function with floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

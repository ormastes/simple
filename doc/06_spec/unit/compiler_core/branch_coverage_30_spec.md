# Branch Coverage 30 Specification

> Tests covering All Numeric Formats, All String Formats, All Comparison Combinations, All Boolean Combinations, All Loop Combinations, All Match Patterns, All Function Signatures, All Array Operations, All Optional Patterns, All String Methods, All Error Conditions, All Control Flow Exits.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 30 Specification

## Scenarios

### All Numeric Formats

#### hex - uppercase

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hex - uppercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex - uppercase")
check(0XFF == 255)
```

</details>

#### hex - lowercase

- hex - lowercase


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex - lowercase")
check(0xff == 255)
```

</details>

#### hex - mixed case

- hex - mixed case


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hex - mixed case")
check(0XfF == 255)
```

</details>

#### binary - all digits

- binary - all digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binary - all digits")
check(0b11111111 == 255)
```

</details>

#### octal - all digits

- octal - all digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("octal - all digits")
check(0o777 == 511)
```

</details>

#### scientific - positive exp

- scientific - positive exp


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scientific - positive exp")
check(1e2 == 100.0)
```

</details>

#### scientific - negative exp

- scientific - negative exp


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scientific - negative exp")
check(1e-2 == 0.01)
```

</details>

#### scientific - explicit plus

- scientific - explicit plus


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scientific - explicit plus")
check(1e+2 == 100.0)
```

</details>

### All String Formats

#### single quote string

- single quote string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single quote string")
val s = 'hello'
check(s == "hello")
```

</details>

#### triple quote string

- triple quote string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple quote string")
val s = """multi
```

</details>

#### raw string - no interpolation

- raw string - no interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("raw string - no interpolation")
val x = 5
val s = r"{x}"
check(s == r"{x}")
```

</details>

#### interpolation - complex expression

- interpolation - complex expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation - complex expression")
val x = 5
val y = 10
val s = "{x * y + (x - y)}"
check(s.contains("45"))
```

</details>

### All Comparison Combinations

#### chain - all less than

- chain - all less than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chain - all less than")
check(1 < 2 < 3 < 4 < 5)
```

</details>

#### chain - all greater than

- chain - all greater than


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chain - all greater than")
check(5 > 4 > 3 > 2 > 1)
```

</details>

#### chain - mixed

- chain - mixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chain - mixed")
check(1 < 2 <= 2 < 3)
```

</details>

#### chain - not equal in chain

- chain - not equal in chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chain - not equal in chain")
check(1 != 2 != 3)
```

</details>

### All Boolean Combinations

#### triple and - TTT

- triple and - TTT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple and - TTT")
check(true and true and true)
```

</details>

#### triple and - TTF

- triple and - TTF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple and - TTF")
check(not (true and true and false))
```

</details>

#### triple and - TFT

- triple and - TFT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple and - TFT")
check(not (true and false and true))
```

</details>

#### triple and - TFF

- triple and - TFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple and - TFF")
check(not (true and false and false))
```

</details>

#### triple or - FFF

- triple or - FFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple or - FFF")
check(not (false or false or false))
```

</details>

#### triple or - FFT

- triple or - FFT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple or - FFT")
check(false or false or true)
```

</details>

#### triple or - FTF

- triple or - FTF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple or - FTF")
check(false or true or false)
```

</details>

#### triple or - FTT

- triple or - FTT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple or - FTT")
check(false or true or true)
```

</details>

#### complex - (A and B) or (C and D)

- complex - (A and B) or (C and D)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - (A and B) or (C and D)")
check((true and true) or (false and false))
check(not ((false and true) or (true and false)))
```

</details>

#### complex - A and (B or C) and D

- complex - A and (B or C) and D


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - A and (B or C) and D")
check(true and (true or false) and true)
check(not (false and (true or false) and true))
```

</details>

### All Loop Combinations

#### for in for - both execute

- for in for - both execute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for in for - both execute")
var count = 0
for i in 0..3:
    for j in 0..3:
        count = count + 1
check(count == 9)
```

</details>

#### for in for - inner empty

- for in for - inner empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for in for - inner empty")
var count = 0
for i in 0..3:
    for j in 0..0:
        count = count + 1
check(count == 0)
```

</details>

#### for in for - outer empty

- for in for - outer empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for in for - outer empty")
var count = 0
for i in 0..0:
    for j in 0..3:
        count = count + 1
check(count == 0)
```

</details>

#### while in while - nested

- while in while - nested


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while in while - nested")
fn run() -> i64:
    var i = 0
    var count = 0
    while i < 3:
        var j = 0
        while j < 3:
            count = count + 1
            j = j + 1
        i = i + 1
    count
check(run() == 9)
```

</details>

#### for in while

- for in while


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for in while")
fn run() -> i64:
    var i = 0
    var count = 0
    while i < 3:
        for j in 0..3:
            count = count + 1
        i = i + 1
    count
check(run() == 9)
```

</details>

#### while in for

- while in for


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while in for")
fn run() -> i64:
    var count = 0
    for i in 0..3:
        var j = 0
        while j < 3:
            count = count + 1
            j = j + 1
    count
check(run() == 9)
```

</details>

### All Match Patterns

#### match - guard clauses

- match - guard clauses


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - guard clauses")
fn classify(x: i64) -> text:
    match x:
        0: "zero"
        1: "one"
        2: "two"
        3: "three"
        4: "four"
        5: "five"
        6: "six"
        7: "seven"
        8: "eight"
        9: "nine"
        _: "many"
check(classify(0) == "zero")
check(classify(5) == "five")
check(classify(9) == "nine")
check(classify(99) == "many")
```

</details>

#### match - sum via direct values

- match - sum via direct values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - sum via direct values")
check(1 + 2 == 3)
check(1 + 2 + 3 == 6)
check(1 + 2 + 3 + 4 == 10)
```

</details>

### All Function Signatures

#### fn - 0 params 0 return

- fn - 0 params 0 return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - 0 params 0 return")
fn f():
    pass
f()
check(true)
```

</details>

#### fn - 1 param 0 return

- fn - 1 param 0 return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - 1 param 0 return")
fn f(a: i64) -> i64:
    a * 2
check(f(21) == 42)
```

</details>

#### fn - 0 params 1 return

- fn - 0 params 1 return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - 0 params 1 return")
fn f() -> i64:
    42
check(f() == 42)
```

</details>

#### fn - 5 params 1 return

- fn - 5 params 1 return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - 5 params 1 return")
fn f(a: i64, b: i64, c: i64, d: i64, e: i64) -> i64:
    a + b + c + d + e
check(f(1, 2, 3, 4, 5) == 15)
```

</details>

#### fn - nested fn calls

- fn - nested fn calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - nested fn calls")
fn f(x: i64) -> i64: x + 1
check(f(f(f(f(f(0))))) == 5)
```

</details>

#### fn - recursive (limited)

- fn - recursive (limited)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn - recursive (limited)")
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    n * factorial(n - 1)
check(factorial(5) == 120)
```

</details>

### All Array Operations

#### array - all methods

- array - all methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - all methods")
fn run() -> i64:
    var arr = [1, 2, 3]
    arr.push(4)
    val len1 = arr.len()
    val x = arr.pop()
    val len2 = arr.len()
    len1 * 10 + len2
check(run() == 43)
val arr2 = [1, 2, 3]
check(arr2.contains(2))
check(not arr2.contains(99))
```

</details>

#### array - nested arrays

- array - nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - nested arrays")
var arr = [[1, 2], [3, 4], [5, 6]]
check(arr[0][0] == 1)
check(arr[1][1] == 4)
check(arr[2][0] == 5)
```

</details>

#### array - array of optionals

- array - array of optionals


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - array of optionals")
val arr = [Some(1), nil, Some(3)]
check(arr[0].?)
check(not arr[1].?)
check(arr[2].?)
```

</details>

#### array - complex slicing

- array - complex slicing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - complex slicing")
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
check(slice_len(arr, 0, 5) == 5)
check(slice_len(arr, 5, 10) == 5)
check(slice_len(arr, 2, 8) == 6)
check(slice_len(arr, 0, 0) == 0)
check(slice_len(arr, 5, 5) == 0)
```

</details>

### All Optional Patterns

#### optional - deep nesting

- optional - deep nesting


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - deep nesting")
val o1: i64? = Some(42)
val o2 = Some(Some(42))
val o3 = Some(Some(Some(42)))
check(o1.?)
check(o2.?)
check(o3.?)
```

</details>

#### optional - all nil levels

- optional - all nil levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - all nil levels")
val o1: i64? = nil
val o2 = nil
val o3 = Some(nil)
check(not o1.?)
check(not o2.?)
check(o3.?)
```

</details>

### All String Methods

#### string - all operations

- string - all operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - all operations")
val s = "  Hello World  "
check(s.trim() == "Hello World")
check(s.len() > 0)
check(s.contains("Hello"))
check(s.starts_with("  Hello"))
check(s.ends_with("World  "))
```

</details>

#### string - split

- string - split


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - split")
val s = "a,b,c"
val parts = s.split(",")
check(parts.len() == 3)
check(parts[0] == "a")
```

</details>

#### string - replace

- string - replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - replace")
val s = "hello world"
val r = s.replace("world", "universe")
check(r == "hello universe")
```

</details>

#### string - index operations

- string - index operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string - index operations")
val s = "hello"
check((s.index_of("l")) == 2)
check((s.last_index_of("l")) == 3)
```

</details>

### All Error Conditions

#### division edge cases

- division edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division edge cases")
check(10 / 1 == 10)
check(10 / 2 == 5)
check(10 / 3 == 3)
check(10 / 10 == 1)
```

</details>

#### modulo edge cases

- modulo edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("modulo edge cases")
check(10 % 1 == 0)
check(10 % 3 == 1)
check(10 % 10 == 0)
check(1 % 10 == 1)
```

</details>

#### power edge cases

- power edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power edge cases")
check(0 ** 0 == 1)
check(0 ** 1 == 0)
check(1 ** 0 == 1)
check(1 ** 1 == 1)
check(2 ** 0 == 1)
check(2 ** 1 == 2)
```

</details>

### All Control Flow Exits

#### return from nested if

- return from nested if


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return from nested if")
fn test(x: i64) -> i64:
    if x > 10:
        if x > 20:
            if x > 30:
                return 3
            return 2
        return 1
    0
check(test(5) == 0)
check(test(15) == 1)
check(test(25) == 2)
check(test(35) == 3)
```

</details>

<details>
<summary>Advanced: break from nested loop</summary>

#### break from nested loop

- break from nested loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("break from nested loop")
fn run() -> bool:
    var found = false
    for i in 0..10:
        for j in 0..10:
            if i == 5 and j == 5:
                found = true
                break
        if found:
            break
    found
check(run())
```

</details>


</details>

<details>
<summary>Advanced: continue in all loops</summary>

#### continue in all loops

- continue in all loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continue in all loops")
fn run() -> i64:
    var count = 0
    for i in 0..10:
        if i % 2 == 0:
            continue
        count = count + 1
    count
check(run() == 5)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/branch_coverage_30_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering All Numeric Formats, All String Formats, All Comparison Combinations, All Boolean Combinations, All Loop Combinations, All Match Patterns, All Function Signatures, All Array Operations, All Optional Patterns, All String Methods, All Error Conditions, All Control Flow Exits.
- All Numeric Formats
- All String Formats
- All Comparison Combinations
- All Boolean Combinations
- All Loop Combinations
- All Match Patterns
- All Function Signatures
- All Array Operations
- All Optional Patterns
- All String Methods
- All Error Conditions
- All Control Flow Exits

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1285659d31b248db7159d38dfd56ed78ab72022a2fd2ed817f7af46e618d8b5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1285659d31b248db7159d38dfd56ed78ab72022a2fd2ed817f7af46e618d8b5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1285659d31b248db7159d38dfd56ed78ab72022a2fd2ed817f7af46e618d8b5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/branch_coverage_30_spec.spl
mirror: doc/06_spec/unit/compiler_core/branch_coverage_30_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/branch_coverage_30_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/branch_coverage_30_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/branch_coverage_30_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hex - uppercase' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_30_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hex - lowercase' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_30_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hex - mixed case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

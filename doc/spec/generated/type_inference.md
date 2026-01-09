# Type Inference Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/type_inference_spec.spl`
> **Generated:** 2026-01-09 06:15:42
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/type_inference_spec.spl
> ```

**Status:** Partial Implementation (Hindley-Milner scaffold working)
**Feature IDs:** #13
**Keywords:** **Last Updated:** 2026-01-05

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (24 tests)
- [Source Code](#source-code)

## Overview

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations in most cases.

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Add` | [9](#add) |
| `All` | [18](#examples_18) |
| `Apply` | [11](#apply) |
| `Array` | [6](#inference_rules_6), [13](#inference_rules_13), [16](#type_unification_16), [17](#type_unification_17), [18](#examples_18), ... (7 total) |
| `Async` | [21](#fetch_data) |
| `Blue` | [12](#inference_rules_12) |
| `Boolean` | [1](#inference_rules_1) |
| `Branch` | [12](#inference_rules_12), [14](#inference_rules_14) |
| `Branches` | [14](#inference_rules_14) |
| `Cannot` | [24](#error_messages_24) |
| `Color` | [12](#inference_rules_12) |
| `Data` | [21](#fetch_data) |
| `Error` | [16](#type_unification_16), [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `ErrorMessages` | [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `Examples` | [18](#examples_18) |
| `Expected` | [22](#error_messages_22) |
| `Explicit` | [6](#inference_rules_6), [9](#add), [21](#fetch_data) |
| `Explicitly` | [21](#fetch_data) |
| `Fetch` | [21](#fetch_data) |
| `FetchData` | [21](#fetch_data) |
| `Float` | [1](#inference_rules_1), [2](#inference_rules_2) |
| `For` | [15](#inference_rules_15) |
| `Found` | [22](#error_messages_22) |
| `Green` | [12](#inference_rules_12) |
| `Hello` | [9](#add) |
| `Inference` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `InferenceRules` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `Inferred` | [21](#fetch_data) |
| `Infers` | [9](#add) |
| `Integer` | [1](#inference_rules_1) |
| `Map` | [19](#map) |
| `Messages` | [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `Must` | [20](#unwrap_or) |
| `Nil` | [1](#inference_rules_1) |
| `Occurs` | [24](#error_messages_24) |
| `Option` | [20](#unwrap_or) |
| `Point` | [13](#inference_rules_13) |
| `Red` | [12](#inference_rules_12) |
| `Result` | [12](#inference_rules_12), [14](#inference_rules_14) |
| `Return` | [20](#unwrap_or) |
| `Rules` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `String` | [1](#inference_rules_1) |
| `Struct` | [13](#inference_rules_13) |
| `This` | [16](#type_unification_16), [24](#error_messages_24) |
| `Tuple` | [13](#inference_rules_13) |
| `Type` | [16](#type_unification_16), [17](#type_unification_17), [20](#unwrap_or), [22](#error_messages_22) |
| `TypeUnification` | [16](#type_unification_16), [17](#type_unification_17) |
| `Undefined` | [23](#error_messages_23) |
| `Unification` | [16](#type_unification_16), [17](#type_unification_17) |
| `Unify` | [17](#type_unification_17) |
| `Unwrap` | [20](#unwrap_or) |
| `UnwrapOr` | [20](#unwrap_or) |
| `Var` | [24](#error_messages_24) |
| `While` | [15](#inference_rules_15) |
| `add` | [9](#add), [10](#inference_rules_10) |
| `append` | [19](#map) |
| `apply` | [11](#apply) |
| `assert_compiles` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (19 total) |
| `compute` | [21](#fetch_data) |
| `data` | [21](#fetch_data) |
| `double` | [19](#map) |
| `error` | [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `error_messages` | [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `examples` | [18](#examples_18) |
| `fetch` | [21](#fetch_data) |
| `fetch_data` | [21](#fetch_data) |
| `get` | [21](#fetch_data) |
| `greet` | [9](#add) |
| `inc` | [11](#apply) |
| `inference` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `inference_rules` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `json` | [21](#fetch_data) |
| `let` | [13](#inference_rules_13) |
| `map` | [19](#map) |
| `messages` | [22](#error_messages_22), [23](#error_messages_23), [24](#error_messages_24) |
| `print` | [15](#inference_rules_15) |
| `range` | [15](#inference_rules_15) |
| `rules` | [1](#inference_rules_1), [2](#inference_rules_2), [3](#inference_rules_3), [4](#inference_rules_4), [5](#inference_rules_5), ... (13 total) |
| `type` | [16](#type_unification_16), [17](#type_unification_17) |
| `type_unification` | [16](#type_unification_16), [17](#type_unification_17) |
| `unification` | [16](#type_unification_16), [17](#type_unification_17) |
| `unwrap` | [20](#unwrap_or) |
| `unwrap_or` | [20](#unwrap_or) |

---

## Test Cases (24 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [inference_rules_1](#inference_rules_1) | Inference Rules | `rules`, `InferenceRules`, `Inference` +9 |
| 2 | [inference_rules_2](#inference_rules_2) | Inference Rules | `rules`, `InferenceRules`, `Inference` +5 |
| 3 | [inference_rules_3](#inference_rules_3) | Inference Rules | `rules`, `InferenceRules`, `Inference` +4 |
| 4 | [inference_rules_4](#inference_rules_4) | Inference Rules | `rules`, `InferenceRules`, `Inference` +4 |
| 5 | [inference_rules_5](#inference_rules_5) | Inference Rules | `rules`, `InferenceRules`, `Inference` +4 |
| 6 | [inference_rules_6](#inference_rules_6) | Inference Rules | `rules`, `InferenceRules`, `Inference` +6 |
| 7 | [inference_rules_7](#inference_rules_7) | Inference Rules | `rules`, `InferenceRules`, `Inference` +4 |
| 8 | [inference_rules_8](#inference_rules_8) | Inference Rules | `rules`, `InferenceRules`, `Inference` +4 |
| 9 | [add](#add) | Inference Rules | `add`, `Add`, `Explicit` +3 |
| 10 | [inference_rules_10](#inference_rules_10) | Inference Rules | `rules`, `InferenceRules`, `Inference` +5 |
| 11 | [apply](#apply) | Inference Rules | `apply`, `Apply`, `inc` |
| 12 | [inference_rules_12](#inference_rules_12) | Inference Rules | `rules`, `InferenceRules`, `Inference` +10 |
| 13 | [inference_rules_13](#inference_rules_13) | Inference Rules | `rules`, `InferenceRules`, `Inference` +9 |
| 14 | [inference_rules_14](#inference_rules_14) | Inference Rules | `rules`, `InferenceRules`, `Inference` +7 |
| 15 | [inference_rules_15](#inference_rules_15) | Inference Rules | `rules`, `InferenceRules`, `Inference` +8 |
| 16 | [type_unification_16](#type_unification_16) | Type Unification | `Type`, `type`, `Unification` +7 |
| 17 | [type_unification_17](#type_unification_17) | Type Unification | `Type`, `type`, `Unification` +6 |
| 18 | [examples_18](#examples_18) | Examples | `Examples`, `examples`, `assert_compiles` +2 |
| 19 | [map](#map) | Examples | `map`, `Map`, `double` +2 |
| 20 | [unwrap_or](#unwrap_or) | Examples | `Unwrap`, `unwrap_or`, `unwrap` +5 |
| 21 | [fetch_data](#fetch_data) | Examples | `fetch`, `fetch_data`, `data` +10 |
| 22 | [error_messages_22](#error_messages_22) | Error Messages | `Messages`, `ErrorMessages`, `error` +7 |
| 23 | [error_messages_23](#error_messages_23) | Error Messages | `Messages`, `ErrorMessages`, `error` +5 |
| 24 | [error_messages_24](#error_messages_24) | Error Messages | `Messages`, `ErrorMessages`, `error` +9 |

---

### Test 1: Inference Rules {#inference_rules_1}

**Test name:** `inference_rules_1`

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `String`
- `Nil`
- `Float`
- ... and 2 more

**Code:**

```simple
test "inference_rules_1":
    """
    Inference Rules
    """
    # Integer literals
    let x = 42           # x: Int

    # Float literals
    let y = 3.14         # y: Float

    # String literals
    let s = "hello"      # s: Str

    # Boolean literals
    let b = true         # b: Bool

    # Nil literal
    let n = nil          # n: Nil
    assert_compiles()
```

### Test 2: Inference Rules {#inference_rules_2}

**Test name:** `inference_rules_2`

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `Float`

**Code:**

```simple
test "inference_rules_2":
    """
    Inference Rules
    """
    let a = 1 + 2        # a: Int (Int + Int -> Int)
    let b = 3.0 * 1.5    # b: Float (Float * Float -> Float)
    assert_compiles()
```

### Test 3: Inference Rules {#inference_rules_3}

**Test name:** `inference_rules_3`

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`

**Code:**

```simple
test "inference_rules_3":
    """
    Inference Rules
    """
    let cmp = 1 < 2      # cmp: Bool
    assert_compiles()
```

### Test 4: Inference Rules {#inference_rules_4}

**Test name:** `inference_rules_4`

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`

**Code:**

```simple
test "inference_rules_4":
    """
    Inference Rules
    """
    let logic = true and false  # logic: Bool
    assert_compiles()
```

### Test 5: Inference Rules {#inference_rules_5}

**Test name:** `inference_rules_5`

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`

**Code:**

```simple
test "inference_rules_5":
    """
    Inference Rules
    """
    let bits = 5 << 2    # bits: Int
    assert_compiles()
```

### Test 6: Inference Rules {#inference_rules_6}

**Test name:** `inference_rules_6`

**Description:**

### Scenario: Arrays:...

Arrays:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `Explicit`
- `Array`

**Code:**

```simple
test "inference_rules_6":
    """
    Inference Rules
    """
    let arr = [1, 2, 3]           # arr: Array[Int]
    let empty: Array[Int] = []    # Explicit type for empty array
    let nested = [[1, 2], [3, 4]] # nested: Array[Array[Int]]
    assert_compiles()
```

### Test 7: Inference Rules {#inference_rules_7}

**Test name:** `inference_rules_7`

**Description:**

### Scenario: Tuples:...

Tuples:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`

**Code:**

```simple
test "inference_rules_7":
    """
    Inference Rules
    """
    let t = (1, "hi", true)       # t: (Int, Str, Bool)
    let first = t[0]              # first: Int
    assert_compiles()
```

### Test 8: Inference Rules {#inference_rules_8}

**Test name:** `inference_rules_8`

**Description:**

### Scenario: Dictionaries:...

Dictionaries:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`

**Code:**

```simple
test "inference_rules_8":
    """
    Inference Rules
    """
    let dict = {"a": 1, "b": 2}   # dict: {Str: Int}
    let val = dict["a"]           # val: Int
    assert_compiles()
```

### Test 9: Inference Rules {#add}

**Test name:** `add`

**Description:**

### Scenario: Function Definition:...

Function Definition:

**Linked Symbols:**
- `add`
- `Add`
- `Explicit`
- `Hello`
- `greet`
- `Infers`

**Code:**

```simple
fn add(a, b):
    return a + b              # Infers: (Int, Int) -> Int

# Explicit types
fn greet(name: str) -> str:
    return "Hello, " + name
```

### Test 10: Inference Rules {#inference_rules_10}

**Test name:** `inference_rules_10`

**Description:**

### Scenario: Function Calls:...

Function Calls:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `add`

**Code:**

```simple
test "inference_rules_10":
    """
    Inference Rules
    """
    let result = add(1, 2)        # result: Int
    assert_compiles()
```

### Test 11: Inference Rules {#apply}

**Test name:** `apply`

**Description:**

### Scenario: Higher-Order Functions:...

Higher-Order Functions:

**Linked Symbols:**
- `apply`
- `Apply`
- `inc`

**Code:**

```simple
fn apply(f, x):
    return f(x)               # f: (T) -> R, x: T, return: R

fn inc(n):
    return n + 1              # inc: (Int) -> Int

let r = apply(inc, 5)         # r: Int
```

### Test 12: Inference Rules {#inference_rules_12}

**Test name:** `inference_rules_12`

**Description:**

### Scenario: Match Expressions:...

Match Expressions:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `Red`
- `Green`
- `Color`
- ... and 3 more

**Code:**

```simple
test "inference_rules_12":
    """
    Inference Rules
    """
    enum Color:
        Red
        Green
        Blue(i64)

    let c = Color::Blue(42)
    match c:
        Color::Red =>
            0                     # Branch type: Int
        Color::Green =>
            1                     # Branch type: Int
        Color::Blue(val) =>
            val                   # Branch type: Int, val: Int
    # Result type: Int (all branches unify)
    assert_compiles()
```

### Test 13: Inference Rules {#inference_rules_13}

**Test name:** `inference_rules_13`

**Description:**

### Scenario: Destructuring:...

Destructuring:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `let`
- `Point`
- `Tuple`
- ... and 2 more

**Code:**

```simple
test "inference_rules_13":
    """
    Inference Rules
    """
    # Tuple pattern
    let (x, y) = (1, 2)           # x: Int, y: Int

    # Array pattern
    let [a, b, c] = [1, 2, 3]     # a, b, c: Int

    # Struct pattern
    struct Point:
        x: i64
        y: i64

    let Point { x, y } = Point { x: 1, y: 2 }  # x, y: i64
    assert_compiles()
```

### Test 14: Inference Rules {#inference_rules_14}

**Test name:** `inference_rules_14`

**Description:**

### Scenario: If Expressions:...

If Expressions:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `Branches`
- `Branch`
- `Result`

**Code:**

```simple
test "inference_rules_14":
    """
    Inference Rules
    """
    # Branches must unify to same type
    let val = if x > 0:
        1                         # Branch 1: Int
    else:
        2                         # Branch 2: Int
    # Result: Int
    assert_compiles()
```

### Test 15: Inference Rules {#inference_rules_15}

**Test name:** `inference_rules_15`

**Description:**

### Scenario: Loops:...

Loops:

**Linked Symbols:**
- `rules`
- `InferenceRules`
- `Inference`
- `inference_rules`
- `inference`
- `Rules`
- `assert_compiles`
- `range`
- `print`
- `While`
- ... and 1 more

**Code:**

```simple
test "inference_rules_15":
    """
    Inference Rules
    """
    # While loop
    let mut i = 0
    while i < 10:
        i = i + 1

    # For loop
    for x in range(0, 10):        # x: Int (inferred from range)
        print(x)
    assert_compiles()
```

### Test 16: Type Unification {#type_unification_16}

**Test name:** `type_unification_16`

**Description:**

### Scenario: Prevents infinite types:...

Prevents infinite types:

**Linked Symbols:**
- `Type`
- `type`
- `Unification`
- `unification`
- `type_unification`
- `TypeUnification`
- `assert_compiles`
- `This`
- `Array`
- `Error`

**Code:**

```simple
test "type_unification_16":
    """
    Type Unification
    """
    # This would fail: T = Array[T]
    let x = [x]  # Error: occurs check failed
    assert_compiles()
```

### Test 17: Type Unification {#type_unification_17}

**Test name:** `type_unification_17`

**Description:**

### Scenario: Type variables are resolved through substitution:...

Type variables are resolved through substitution:

**Linked Symbols:**
- `Type`
- `type`
- `Unification`
- `unification`
- `type_unification`
- `TypeUnification`
- `assert_compiles`
- `Unify`
- `Array`

**Code:**

```simple
test "type_unification_17":
    """
    Type Unification
    """
    let arr = []           # arr: Array[?T]
    arr[0] = 42            # Unify ?T with Int
    # arr: Array[Int]
    assert_compiles()
```

### Test 18: Examples {#examples_18}

**Test name:** `examples_18`

**Linked Symbols:**
- `Examples`
- `examples`
- `assert_compiles`
- `Array`
- `All`

**Code:**

```simple
test "examples_18":
    """
    Examples
    """
    # All types inferred automatically
    let numbers = [1, 2, 3, 4, 5]      # Array[Int]
    let sum = 0                         # Int
    for n in numbers:                   # n: Int
        sum = sum + n
    # sum: Int
    assert_compiles()
```

### Test 19: Examples {#map}

**Test name:** `map`

**Linked Symbols:**
- `map`
- `Map`
- `double`
- `Array`
- `append`

**Code:**

```simple
fn map(f, arr):
    let result = []
    for x in arr:
        result.append(f(x))
    return result

fn double(x):
    return x * 2

let nums = [1, 2, 3]               # Array[Int]
let doubled = map(double, nums)    # Array[Int]
```

### Test 20: Examples {#unwrap_or}

**Test name:** `unwrap_or`

**Linked Symbols:**
- `Unwrap`
- `unwrap_or`
- `unwrap`
- `UnwrapOr`
- `Type`
- `Return`
- `Option`
- `Must`

**Code:**

```simple
fn unwrap_or(opt, default):
    match opt:
        Option::Some(val) =>
            val                    # Type inferred from T
        Option::None =>
            default                # Must unify with T
# Return type: T
```

### Test 21: Examples {#fetch_data}

**Test name:** `fetch_data`

**Linked Symbols:**
- `fetch`
- `fetch_data`
- `data`
- `Data`
- `Fetch`
- `FetchData`
- `Async`
- `Explicit`
- `Explicitly`
- `get`
- ... and 3 more

**Code:**

```simple
fn fetch_data():
    let response = http.get("https://api.example.com")  # Async call
    return response.json()
# Inferred as async

# Explicit sync
sync fn compute():
    return 2 + 2
# Explicitly sync
```

### Test 22: Error Messages {#error_messages_22}

**Test name:** `error_messages_22`

**Linked Symbols:**
- `Messages`
- `ErrorMessages`
- `error`
- `error_messages`
- `messages`
- `Error`
- `assert_compiles`
- `Type`
- `Expected`
- `Found`

**Code:**

```simple
test "error_messages_22":
    """
    Error Messages
    """
    let x = 1 + "hello"
    # Error: Type mismatch
    #   Expected: Int
    #   Found: Str
    assert_compiles()
```

### Test 23: Error Messages {#error_messages_23}

**Test name:** `error_messages_23`

**Linked Symbols:**
- `Messages`
- `ErrorMessages`
- `error`
- `error_messages`
- `messages`
- `Error`
- `assert_compiles`
- `Undefined`

**Code:**

```simple
test "error_messages_23":
    """
    Error Messages
    """
    let result = unknown_var + 1
    # Error: Undefined identifier: unknown_var
    assert_compiles()
```

### Test 24: Error Messages {#error_messages_24}

**Test name:** `error_messages_24`

**Linked Symbols:**
- `Messages`
- `ErrorMessages`
- `error`
- `error_messages`
- `messages`
- `Error`
- `assert_compiles`
- `Var`
- `Occurs`
- `Cannot`
- ... and 2 more

**Code:**

```simple
test "error_messages_24":
    """
    Error Messages
    """
    let x = [x]
    # Error: Occurs check failed
    #   Cannot unify Var(0) with Array[Var(0)]
    #   This would create an infinite type
    assert_compiles()
```

---

## Source Code

**View full specification:** [type_inference_spec.spl](../../tests/specs/type_inference_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/type_inference_spec.spl`*

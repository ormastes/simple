# Type Inference Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/type_inference_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/type_inference_spec.spl
> ```

**Status:** Partial Implementation (Hindley-Milner scaffold working)
**Feature IDs:** #13
**Keywords:** **Last Updated:** 2026-01-05

## Overview

Simple uses a Hindley-Milner-style type inference system that automatically deduces types for expressions, variables, and functions without requiring explicit type annotations in most cases.

---

## Test Cases (24 total)

| Test | Section | Description |
|------|---------|-------------|
| [inference_rules_1](#test-1) | Inference Rules |  |
| [inference_rules_2](#test-2) | Inference Rules |  |
| [inference_rules_3](#test-3) | Inference Rules |  |
| [inference_rules_4](#test-4) | Inference Rules |  |
| [inference_rules_5](#test-5) | Inference Rules |  |
| [inference_rules_6](#test-6) | Inference Rules | ### Scenario: Arrays:...  Arrays: |
| [inference_rules_7](#test-7) | Inference Rules | ### Scenario: Tuples:...  Tuples: |
| [inference_rules_8](#test-8) | Inference Rules | ### Scenario: Dictionaries:...  Dictionaries: |
| [add](#test-9) | Inference Rules | ### Scenario: Function Definition:...  Function Definition: |
| [inference_rules_10](#test-10) | Inference Rules | ### Scenario: Function Calls:...  Function Calls: |
| [apply](#test-11) | Inference Rules | ### Scenario: Higher-Order Functions:...... |
| [inference_rules_12](#test-12) | Inference Rules | ### Scenario: Match Expressions:...  Match Expressions: |
| [inference_rules_13](#test-13) | Inference Rules | ### Scenario: Destructuring:...  Destructuring: |
| [inference_rules_14](#test-14) | Inference Rules | ### Scenario: If Expressions:...  If Expressions: |
| [inference_rules_15](#test-15) | Inference Rules | ### Scenario: Loops:...  Loops: |
| [type_unification_16](#test-16) | Type Unification | ### Scenario: Prevents infinite types:...... |
| [type_unification_17](#test-17) | Type Unification | ### Scenario: Type variables are resolved through substituti... |
| [examples_18](#test-18) | Examples |  |
| [map](#test-19) | Examples |  |
| [unwrap_or](#test-20) | Examples |  |
| [fetch_data](#test-21) | Examples |  |
| [error_messages_22](#test-22) | Error Messages |  |
| [error_messages_23](#test-23) | Error Messages |  |
| [error_messages_24](#test-24) | Error Messages |  |

---

### Test 1: Inference Rules

**Test name:** `inference_rules_1`

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

### Test 2: Inference Rules

**Test name:** `inference_rules_2`

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

### Test 3: Inference Rules

**Test name:** `inference_rules_3`

**Code:**

```simple
test "inference_rules_3":
    """
    Inference Rules
    """
    let cmp = 1 < 2      # cmp: Bool
    assert_compiles()
```

### Test 4: Inference Rules

**Test name:** `inference_rules_4`

**Code:**

```simple
test "inference_rules_4":
    """
    Inference Rules
    """
    let logic = true and false  # logic: Bool
    assert_compiles()
```

### Test 5: Inference Rules

**Test name:** `inference_rules_5`

**Code:**

```simple
test "inference_rules_5":
    """
    Inference Rules
    """
    let bits = 5 << 2    # bits: Int
    assert_compiles()
```

### Test 6: Inference Rules

**Test name:** `inference_rules_6`

**Description:**

### Scenario: Arrays:...

Arrays:

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

### Test 7: Inference Rules

**Test name:** `inference_rules_7`

**Description:**

### Scenario: Tuples:...

Tuples:

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

### Test 8: Inference Rules

**Test name:** `inference_rules_8`

**Description:**

### Scenario: Dictionaries:...

Dictionaries:

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

### Test 9: Inference Rules

**Test name:** `add`

**Description:**

### Scenario: Function Definition:...

Function Definition:

**Code:**

```simple
fn add(a, b):
    return a + b              # Infers: (Int, Int) -> Int

# Explicit types
fn greet(name: str) -> str:
    return "Hello, " + name
```

### Test 10: Inference Rules

**Test name:** `inference_rules_10`

**Description:**

### Scenario: Function Calls:...

Function Calls:

**Code:**

```simple
test "inference_rules_10":
    """
    Inference Rules
    """
    let result = add(1, 2)        # result: Int
    assert_compiles()
```

### Test 11: Inference Rules

**Test name:** `apply`

**Description:**

### Scenario: Higher-Order Functions:...

Higher-Order Functions:

**Code:**

```simple
fn apply(f, x):
    return f(x)               # f: (T) -> R, x: T, return: R

fn inc(n):
    return n + 1              # inc: (Int) -> Int

let r = apply(inc, 5)         # r: Int
```

### Test 12: Inference Rules

**Test name:** `inference_rules_12`

**Description:**

### Scenario: Match Expressions:...

Match Expressions:

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

### Test 13: Inference Rules

**Test name:** `inference_rules_13`

**Description:**

### Scenario: Destructuring:...

Destructuring:

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

### Test 14: Inference Rules

**Test name:** `inference_rules_14`

**Description:**

### Scenario: If Expressions:...

If Expressions:

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

### Test 15: Inference Rules

**Test name:** `inference_rules_15`

**Description:**

### Scenario: Loops:...

Loops:

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

### Test 16: Type Unification

**Test name:** `type_unification_16`

**Description:**

### Scenario: Prevents infinite types:...

Prevents infinite types:

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

### Test 17: Type Unification

**Test name:** `type_unification_17`

**Description:**

### Scenario: Type variables are resolved through substitution:...

Type variables are resolved through substitution:

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

### Test 18: Examples

**Test name:** `examples_18`

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

### Test 19: Examples

**Test name:** `map`

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

### Test 20: Examples

**Test name:** `unwrap_or`

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

### Test 21: Examples

**Test name:** `fetch_data`

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

### Test 22: Error Messages

**Test name:** `error_messages_22`

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

### Test 23: Error Messages

**Test name:** `error_messages_23`

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

### Test 24: Error Messages

**Test name:** `error_messages_24`

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

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/type_inference_spec.spl`*

# Simple Language Functions and Pattern Matching - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/functions_spec.spl`
> **Generated:** 2026-01-10 04:47:40
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/functions_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** functions.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (24 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from functions.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/functions.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `API` | [24](#semantic_types_in_function_signatures_24) |
| `ASYNC` | [2](#functions_2) |
| `Add` | [1](#add) |
| `And` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `Application` | [22](#constructor_polymorphism_22) |
| `Bare` | [24](#semantic_types_in_function_signatures_24) |
| `Base` | [18](#constructor_polymorphism_18) |
| `Blue` | [15](#pattern_matching_15) |
| `Button` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20) |
| `Cancel` | [19](#constructor_polymorphism_19) |
| `Click` | [17](#constructor_polymorphism_17) |
| `Closures` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `Color` | [15](#pattern_matching_15) |
| `Compile` | [18](#constructor_polymorphism_18) |
| `Config` | [22](#constructor_polymorphism_22) |
| `Constructor` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `ConstructorPolymorphism` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `Creatable` | [23](#constructor_polymorphism_23) |
| `Created` | [20](#constructor_polymorphism_20) |
| `Creates` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17) |
| `Data` | [2](#functions_2), [22](#constructor_polymorphism_22) |
| `Dynamic` | [19](#constructor_polymorphism_19) |
| `EOF` | [8](#pattern_matching_8) |
| `ERROR` | [18](#constructor_polymorphism_18) |
| `End` | [8](#pattern_matching_8) |
| `Enums` | [24](#semantic_types_in_function_signatures_24) |
| `Error` | [15](#pattern_matching_15) |
| `Explicit` | [2](#functions_2) |
| `Factory` | [19](#constructor_polymorphism_19) |
| `Filtering` | [7](#lambdas_and_closures_7) |
| `Function` | [24](#semantic_types_in_function_signatures_24) |
| `Functions` | [2](#functions_2), [3](#functions_3) |
| `GOOD` | [24](#semantic_types_in_function_signatures_24) |
| `Generic` | [19](#constructor_polymorphism_19) |
| `Green` | [15](#pattern_matching_15) |
| `Hello` | [17](#constructor_polymorphism_17) |
| `Help` | [19](#constructor_polymorphism_19) |
| `Inferred` | [2](#functions_2) |
| `InvalidChild` | [18](#constructor_polymorphism_18) |
| `Item` | [7](#lambdas_and_closures_7) |
| `Label` | [17](#constructor_polymorphism_17), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20) |
| `Lambdas` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `LambdasAndClosures` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `Large` | [11](#pattern_matching_11) |
| `Mapping` | [7](#lambdas_and_closures_7) |
| `Matching` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `Minus` | [8](#pattern_matching_8) |
| `MockService` | [22](#constructor_polymorphism_22) |
| `Negative` | [11](#pattern_matching_11) |
| `Non` | [12](#pattern_matching_12) |
| `Normal` | [11](#pattern_matching_11) |
| `Number` | [8](#pattern_matching_8), [14](#pattern_matching_14) |
| `One` | [9](#pattern_matching_9) |
| `Option` | [24](#semantic_types_in_function_signatures_24) |
| `Origin` | [13](#pattern_matching_13) |
| `Pass` | [17](#constructor_polymorphism_17) |
| `Pattern` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `PatternMatching` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `Plus` | [8](#pattern_matching_8) |
| `Point` | [13](#pattern_matching_13) |
| `Polymorphism` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `Production` | [22](#constructor_polymorphism_22) |
| `ProductionService` | [22](#constructor_polymorphism_22) |
| `Red` | [15](#pattern_matching_15) |
| `SYNC` | [2](#functions_2) |
| `Self` | [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [22](#constructor_polymorphism_22), [23](#constructor_polymorphism_23) |
| `Semantic` | [24](#semantic_types_in_function_signatures_24) |
| `SemanticTypesInFunctionSignatures` | [24](#semantic_types_in_function_signatures_24) |
| `Service` | [22](#constructor_polymorphism_22) |
| `Signatures` | [24](#semantic_types_in_function_signatures_24) |
| `Slider` | [20](#constructor_polymorphism_20) |
| `Small` | [10](#pattern_matching_10) |
| `Somewhere` | [13](#pattern_matching_13) |
| `Starts` | [14](#pattern_matching_14) |
| `String` | [8](#pattern_matching_8) |
| `Testing` | [22](#constructor_polymorphism_22) |
| `Token` | [8](#pattern_matching_8) |
| `Types` | [24](#semantic_types_in_function_signatures_24) |
| `User` | [2](#functions_2), [24](#semantic_types_in_function_signatures_24) |
| `UserId` | [2](#functions_2), [24](#semantic_types_in_function_signatures_24) |
| `UserStatus` | [24](#semantic_types_in_function_signatures_24) |
| `ValidChild` | [18](#constructor_polymorphism_18) |
| `WARNING` | [24](#semantic_types_in_function_signatures_24) |
| `Warning` | [24](#semantic_types_in_function_signatures_24) |
| `Widget` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), [21](#constructor_polymorphism_21), ... (6 total) |
| `With` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5) |
| `Zero` | [9](#pattern_matching_9), [12](#pattern_matching_12) |
| `add` | [1](#add), [5](#lambdas_and_closures_5) |
| `and` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `apply` | [3](#functions_3) |
| `assert_compiles` | [2](#functions_2), [3](#functions_3), [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), ... (23 total) |
| `case` | [14](#pattern_matching_14) |
| `closures` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `compute` | [2](#functions_2) |
| `constructor` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `constructor_polymorphism` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `create` | [23](#constructor_polymorphism_23) |
| `create_many` | [19](#constructor_polymorphism_19) |
| `create_widget` | [17](#constructor_polymorphism_17) |
| `ctor` | [17](#constructor_polymorphism_17), [19](#constructor_polymorphism_19), [21](#constructor_polymorphism_21) |
| `describe_token` | [8](#pattern_matching_8) |
| `double` | [2](#functions_2) |
| `empty` | [22](#constructor_polymorphism_22) |
| `exact_factory` | [21](#constructor_polymorphism_21) |
| `exactly` | [21](#constructor_polymorphism_21) |
| `factory` | [16](#constructor_polymorphism_16), [19](#constructor_polymorphism_19) |
| `fetch_user` | [2](#functions_2) |
| `find_user` | [24](#semantic_types_in_function_signatures_24) |
| `function` | [24](#semantic_types_in_function_signatures_24) |
| `functions` | [2](#functions_2), [3](#functions_3) |
| `get` | [2](#functions_2) |
| `get_user_id` | [24](#semantic_types_in_function_signatures_24) |
| `get_widget_factory` | [19](#constructor_polymorphism_19) |
| `lambdas` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `lambdas_and_closures` | [4](#lambdas_and_closures_4), [5](#lambdas_and_closures_5), [6](#lambdas_and_closures_6), [7](#lambdas_and_closures_7) |
| `load_data` | [2](#functions_2) |
| `matching` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `math_op` | [3](#functions_3) |
| `name` | [15](#pattern_matching_15) |
| `new` | [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [22](#constructor_polymorphism_22), [23](#constructor_polymorphism_23) |
| `pattern` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `pattern_matching` | [8](#pattern_matching_8), [9](#pattern_matching_9), [10](#pattern_matching_10), [11](#pattern_matching_11), [12](#pattern_matching_12), ... (8 total) |
| `polymorphism` | [16](#constructor_polymorphism_16), [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [19](#constructor_polymorphism_19), [20](#constructor_polymorphism_20), ... (8 total) |
| `read_file` | [2](#functions_2) |
| `scale` | [6](#lambdas_and_closures_6) |
| `semantic` | [24](#semantic_types_in_function_signatures_24) |
| `semantic_types_in_function_signatures` | [24](#semantic_types_in_function_signatures_24) |
| `service_ctor` | [22](#constructor_polymorphism_22) |
| `set_status` | [24](#semantic_types_in_function_signatures_24) |
| `signatures` | [24](#semantic_types_in_function_signatures_24) |
| `super` | [17](#constructor_polymorphism_17), [18](#constructor_polymorphism_18), [22](#constructor_polymorphism_22) |
| `types` | [24](#semantic_types_in_function_signatures_24) |

---

## Test Cases (24 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [add](#add) | Functions | `Add`, `add` |
| 2 | [functions_2](#functions_2) | Functions | `functions`, `Functions`, `compute` +13 |
| 3 | [functions_3](#functions_3) | Functions | `functions`, `Functions`, `assert_compiles` +2 |
| 4 | [lambdas_and_closures_4](#lambdas_and_closures_4) | Lambdas and Closures | `closures`, `and`, `lambdas_and_closures` +7 |
| 5 | [lambdas_and_closures_5](#lambdas_and_closures_5) | Lambdas and Closures | `closures`, `and`, `lambdas_and_closures` +8 |
| 6 | [lambdas_and_closures_6](#lambdas_and_closures_6) | Lambdas and Closures | `closures`, `and`, `lambdas_and_closures` +7 |
| 7 | [lambdas_and_closures_7](#lambdas_and_closures_7) | Lambdas and Closures | `closures`, `and`, `lambdas_and_closures` +9 |
| 8 | [pattern_matching_8](#pattern_matching_8) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +12 |
| 9 | [pattern_matching_9](#pattern_matching_9) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +6 |
| 10 | [pattern_matching_10](#pattern_matching_10) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +5 |
| 11 | [pattern_matching_11](#pattern_matching_11) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +7 |
| 12 | [pattern_matching_12](#pattern_matching_12) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +6 |
| 13 | [pattern_matching_13](#pattern_matching_13) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +7 |
| 14 | [pattern_matching_14](#pattern_matching_14) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +7 |
| 15 | [pattern_matching_15](#pattern_matching_15) | Pattern Matching | `PatternMatching`, `Pattern`, `matching` +10 |
| 16 | [constructor_polymorphism_16](#constructor_polymorphism_16) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +8 |
| 17 | [constructor_polymorphism_17](#constructor_polymorphism_17) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +16 |
| 18 | [constructor_polymorphism_18](#constructor_polymorphism_18) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +12 |
| 19 | [constructor_polymorphism_19](#constructor_polymorphism_19) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +16 |
| 20 | [constructor_polymorphism_20](#constructor_polymorphism_20) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +9 |
| 21 | [constructor_polymorphism_21](#constructor_polymorphism_21) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +8 |
| 22 | [constructor_polymorphism_22](#constructor_polymorphism_22) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +17 |
| 23 | [constructor_polymorphism_23](#constructor_polymorphism_23) | Constructor Polymorphism | `ConstructorPolymorphism`, `Polymorphism`, `constructor_polymorphism` +9 |
| 24 | [semantic_types_in_function_signatures_24](#semantic_types_in_function_signatures_24) | Semantic Types in Function Signatures | `types`, `Types`, `function` +21 |

---

### Test 1: Functions {#add}

*Source line: ~7*

**Test name:** `add`

**Description:**

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

**Linked Symbols:**
- `Add`
- `add`

**Code:**

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b
```

### Test 2: Functions {#functions_2}

*Source line: ~18*

**Test name:** `functions_2`

**Description:**

Functions have an inferred async/sync effect based on their body:

**Linked Symbols:**
- `functions`
- `Functions`
- `compute`
- `get`
- `double`
- `assert_compiles`
- `read_file`
- `UserId`
- `fetch_user`
- `load_data`
- ... and 6 more

**Code:**

```simple
test "functions_2":
    # Inferred as SYNC: only pure computation
    fn double(x: i64) -> i64:
        return x * 2

    # Inferred as ASYNC: uses suspension operator
    fn fetch_user(id: UserId) -> User:
        let user ~= http.get("/users/{id}")
        return user

    # Explicit SYNC: compiler verifies no suspension
    sync fn compute(x: i64) -> i64:
        return x * x

    # Explicit ASYNC: documentation, no behavioral change
    async fn load_data() -> Data:
        let d ~= read_file(path)
        return d
    assert_compiles()
```

### Test 3: Functions {#functions_3}

*Source line: ~52*

**Test name:** `functions_3`

**Description:**

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

**Linked Symbols:**
- `functions`
- `Functions`
- `assert_compiles`
- `apply`
- `math_op`

**Code:**

```simple
test "functions_3":
    let math_op = add
    let result = math_op(2, 3)  # 5

    fn apply(f: fn(i64, i64) -> i64, x: i64, y: i64) -> i64:
        return f(x, y)

    apply(add, 10, 20)  # 30
    assert_compiles()
```

### Test 4: Lambdas and Closures {#lambdas_and_closures_4}

*Source line: ~7*

**Test name:** `lambdas_and_closures_4`

**Description:**

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

**Linked Symbols:**
- `closures`
- `and`
- `lambdas_and_closures`
- `Closures`
- `LambdasAndClosures`
- `Lambdas`
- `lambdas`
- `And`
- `assert_compiles`
- `With`

**Code:**

```simple
test "lambdas_and_closures_4":
    let square = \x: x * x
    let double = \x: x * 2

    # With explicit type annotations
    let typed_square = \(x: i64) -> i64: x * x
    assert_compiles()
```

### Test 5: Lambdas and Closures {#lambdas_and_closures_5}

*Source line: ~19*

**Test name:** `lambdas_and_closures_5`

**Description:**

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

**Linked Symbols:**
- `closures`
- `and`
- `lambdas_and_closures`
- `Closures`
- `LambdasAndClosures`
- `Lambdas`
- `lambdas`
- `And`
- `assert_compiles`
- `With`
- ... and 1 more

**Code:**

```simple
test "lambdas_and_closures_5":
    let add = \a, b: a + b
    let sum = add(3, 4)  # 7

    # With types
    let typed_add = \(a: i64, b: i64) -> i64: a + b
    assert_compiles()
```

### Test 6: Lambdas and Closures {#lambdas_and_closures_6}

*Source line: ~31*

**Test name:** `lambdas_and_closures_6`

**Description:**

Lambdas capture variables from their enclosing scope:

**Linked Symbols:**
- `closures`
- `and`
- `lambdas_and_closures`
- `Closures`
- `LambdasAndClosures`
- `Lambdas`
- `lambdas`
- `And`
- `scale`
- `assert_compiles`

**Code:**

```simple
test "lambdas_and_closures_6":
    let multiplier = 3
    let scale = \x: x * multiplier

    scale(10)  # 30
    assert_compiles()
```

### Test 7: Lambdas and Closures {#lambdas_and_closures_7}

*Source line: ~42*

**Test name:** `lambdas_and_closures_7`

**Description:**

Methods can accept trailing blocks for iteration or DSL constructs:

**Linked Symbols:**
- `closures`
- `and`
- `lambdas_and_closures`
- `Closures`
- `LambdasAndClosures`
- `Lambdas`
- `lambdas`
- `And`
- `assert_compiles`
- `Filtering`
- ... and 2 more

**Code:**

```simple
test "lambdas_and_closures_7":
    list.each \item:
        print "Item: {item}"

    map.each \key, value:
        print "{key}: {value}"

    # Filtering
    let positives = numbers.filter \x: x > 0

    # Mapping
    let doubled = numbers.map \x: x * 2
    assert_compiles()
```

### Test 8: Pattern Matching {#pattern_matching_8}

*Source line: ~7*

**Test name:** `pattern_matching_8`

**Description:**

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expr...

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `Token`
- `assert_compiles`
- `EOF`
- `End`
- ... and 5 more

**Code:**

```simple
test "pattern_matching_8":
    enum Token:
        Number(value: i64)
        Plus
        Minus
        EOF

    fn describe_token(tok: Token) -> String:
        match tok:
            case Number(val):
                return "Number({val})"
            case Plus:
                return "Plus sign"
            case Minus:
                return "Minus sign"
            case EOF:
                return "End of input"
    assert_compiles()
```

### Test 9: Pattern Matching {#pattern_matching_9}

*Source line: ~30*

**Test name:** `pattern_matching_9`

**Description:**

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `assert_compiles`
- `Zero`
- `One`

**Code:**

```simple
test "pattern_matching_9":
    match x:
        case 0:
            print "Zero"
        case 1:
            print "One"
    assert_compiles()
```

### Test 10: Pattern Matching {#pattern_matching_10}

*Source line: ~40*

**Test name:** `pattern_matching_10`

**Description:**

```simple
match x:
    case 0:
        print "Zero"
    case 1:
        print "One"
```

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `assert_compiles`
- `Small`

**Code:**

```simple
test "pattern_matching_10":
    match x:
        case 1 | 2 | 3:
            print "Small number"
    assert_compiles()
```

### Test 11: Pattern Matching {#pattern_matching_11}

*Source line: ~48*

**Test name:** `pattern_matching_11`

**Description:**

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `Negative`
- `assert_compiles`
- `Large`
- `Normal`

**Code:**

```simple
test "pattern_matching_11":
    match x:
        case n if n < 0:
            print "Negative number: {n}"
        case n if n > 100:
            print "Large number: {n}"
        case n:
            print "Normal number: {n}"
    assert_compiles()
```

### Test 12: Pattern Matching {#pattern_matching_12}

*Source line: ~60*

**Test name:** `pattern_matching_12`

**Description:**

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
...

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `assert_compiles`
- `Non`
- `Zero`

**Code:**

```simple
test "pattern_matching_12":
    match x:
        case 0:
            print "Zero"
        case _:
            print "Non-zero"
    assert_compiles()
```

### Test 13: Pattern Matching {#pattern_matching_13}

*Source line: ~70*

**Test name:** `pattern_matching_13`

**Description:**

```simple
match x:
    case 0:
        print "Zero"
    case _:
        print "Non-zero"
```

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `assert_compiles`
- `Point`
- `Origin`
- `Somewhere`

**Code:**

```simple
test "pattern_matching_13":
    struct Point:
        x: f64
        y: f64

    let p = Point(x: 5, y: 0)
    match p:
        case Point(x: 0, y: 0):
            print "Origin"
        case Point(x: x_val, y: 0):
            print "On X axis at {x_val}"
        case Point(x: 0, y: y_val):
            print "On Y axis at {y_val}"
        case Point(x: _, y: _):
            print "Somewhere else"
    assert_compiles()
```

### Test 14: Pattern Matching {#pattern_matching_14}

*Source line: ~89*

**Test name:** `pattern_matching_14`

**Description:**

let p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point...

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `case`
- `assert_compiles`
- `Starts`
- `Number`

**Code:**

```simple
test "pattern_matching_14":
    let pair = (1, "hello")
    match pair:
        case (0, _):
            print "Starts with zero"
        case (n, s):
            print "Number {n} with string '{s}'"
    assert_compiles()
```

### Test 15: Pattern Matching {#pattern_matching_15}

*Source line: ~102*

**Test name:** `pattern_matching_15`

**Description:**

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

**Linked Symbols:**
- `PatternMatching`
- `Pattern`
- `matching`
- `pattern`
- `pattern_matching`
- `Matching`
- `Color`
- `Error`
- `assert_compiles`
- `Green`
- ... and 3 more

**Code:**

```simple
test "pattern_matching_15":
    enum Color:
        Red
        Green
        Blue

    fn name(c: Color) -> str:
        match c:
            case Red: "red"
            case Green: "green"
            # Error: missing case Blue
    assert_compiles()
```

### Test 16: Constructor Polymorphism {#constructor_polymorphism_16}

*Source line: ~9*

**Test name:** `constructor_polymorphism_16`

**Description:**

The `Constructor[T]` type represents any constructor that produces an instance of `T` or a subtype:

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `assert_compiles`
- `Button`
- `Creates`
- `factory`
- ... and 1 more

**Code:**

```simple
test "constructor_polymorphism_16":
    # Constructor[T] - type for constructors producing T or subtypes
    let factory: Constructor[Widget] = Button    # Button extends Widget
    let widget = factory("OK")                   # Creates a Button
    assert_compiles()
```

### Test 17: Constructor Polymorphism {#constructor_polymorphism_17}

*Source line: ~17*

**Test name:** `constructor_polymorphism_17`

**Description:**

```simple
# Constructor[T] - type for constructors producing T or subtypes
let factory: Constructor[...

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `new`
- `super`
- `Pass`
- `ctor`
- ... and 9 more

**Code:**

```simple
test "constructor_polymorphism_17":
    class Widget:
        name: str

        fn new(name: str) -> Self:
            return Widget(name: name)

    class Button(Widget):
        enabled: bool

        fn new(name: str, enabled: bool = true) -> Self:
            super(name)
            self.enabled = enabled

    # Pass constructor as parameter
    fn create_widget(ctor: Constructor[Widget], name: str) -> Widget:
        return ctor(name)

    let b = create_widget(Button, "Click")    # Creates Button
    let l = create_widget(Label, "Hello")     # Creates Label
    assert_compiles()
```

### Test 18: Constructor Polymorphism {#constructor_polymorphism_18}

*Source line: ~47*

**Test name:** `constructor_polymorphism_18`

**Description:**

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `new`
- `super`
- `assert_compiles`
- `Compile`
- ... and 5 more

**Code:**

```simple
test "constructor_polymorphism_18":
    class Base:
        fn new(name: str, value: i32) -> Self:
            ...

    class ValidChild(Base):
        # OK: has parent params + extra with default
        fn new(name: str, value: i32, extra: bool = false) -> Self:
            super(name, value)
            ...

    class InvalidChild(Base):
        # ERROR: extra param without default
        fn new(name: str, value: i32, extra: bool) -> Self:  # Compile error!
            ...
    assert_compiles()
```

### Test 19: Constructor Polymorphism {#constructor_polymorphism_19}

*Source line: ~76*

**Test name:** `constructor_polymorphism_19`

**Description:**

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `get_widget_factory`
- `Generic`
- `ctor`
- `assert_compiles`
- ... and 9 more

**Code:**

```simple
test "constructor_polymorphism_19":
    # Generic factory function
    fn create_many[T](ctor: Constructor[T], names: [str]) -> [T]:
        return [ctor(name) for name in names]

    let buttons = create_many(Button, ["OK", "Cancel", "Help"])

    # Factory selector
    fn get_widget_factory(kind: str) -> Constructor[Widget]:
        match kind:
            case "button": return Button
            case "label": return Label
            case _: return Widget

    let factory = get_widget_factory("button")
    let w = factory("Dynamic Button")
    assert_compiles()
```

### Test 20: Constructor Polymorphism {#constructor_polymorphism_20}

*Source line: ~96*

**Test name:** `constructor_polymorphism_20`

**Description:**

let factory = get_widget_factory("button")
let w = factory("Dynamic Button")
```

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `assert_compiles`
- `Button`
- `Slider`
- `Label`
- ... and 2 more

**Code:**

```simple
test "constructor_polymorphism_20":
    # In variables
    let ctor: Constructor[Widget] = Button

    # In collections
    let factories: [Constructor[Widget]] = [Button, Label, Slider]

    # In dictionaries
    let registry: {str: Constructor[Widget]} = {
        "button": Button,
        "label": Label,
    }

    let widget = registry["button"]("Created from registry")
    assert_compiles()
```

### Test 21: Constructor Polymorphism {#constructor_polymorphism_21}

*Source line: ~116*

**Test name:** `constructor_polymorphism_21`

**Description:**

Specify exact constructor signatures:

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `exactly`
- `ctor`
- `assert_compiles`
- `exact_factory`
- ... and 1 more

**Code:**

```simple
test "constructor_polymorphism_21":
    # Constructor that takes exactly (str, i32)
    fn exact_factory(ctor: Constructor[Widget, (str, i32)]) -> Widget:
        return ctor("default", 42)

    # Constructor that takes no parameters
    fn no_arg_factory[T](ctor: Constructor[T, ()]) -> T:
        return ctor()
    assert_compiles()
```

### Test 22: Constructor Polymorphism {#constructor_polymorphism_22}

*Source line: ~130*

**Test name:** `constructor_polymorphism_22`

**Description:**

Constructor polymorphism enables clean dependency injection:

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `new`
- `super`
- `Production`
- `assert_compiles`
- ... and 10 more

**Code:**

```simple
test "constructor_polymorphism_22":
    class Service:
        fn new(config: Config) -> Self:
            ...

    class MockService(Service):
        fn new(config: Config, mock_data: Data = Data.empty()) -> Self:
            super(config)
            ...

    class ProductionService(Service):
        fn new(config: Config, pool_size: i32 = 10) -> Self:
            super(config)
            ...

    class Application:
        service: Service

        fn new(service_ctor: Constructor[Service], config: Config) -> Self:
            self.service = service_ctor(config)

    # Production
    let app = Application(ProductionService, prod_config)

    # Testing
    let test_app = Application(MockService, test_config)
    assert_compiles()
```

### Test 23: Constructor Polymorphism {#constructor_polymorphism_23}

*Source line: ~162*

**Test name:** `constructor_polymorphism_23`

**Description:**

Use traits to define abstract constructor requirements:

**Linked Symbols:**
- `ConstructorPolymorphism`
- `Polymorphism`
- `constructor_polymorphism`
- `polymorphism`
- `constructor`
- `Constructor`
- `new`
- `assert_compiles`
- `Creatable`
- `create`
- ... and 2 more

**Code:**

```simple
test "constructor_polymorphism_23":
    trait Creatable:
        fn create(name: str) -> Self

    impl Creatable for Widget:
        fn create(name: str) -> Widget:
            return Widget.new(name)

    fn make[T: Creatable](name: str) -> T:
        return T.create(name)
    assert_compiles()
```

### Test 24: Semantic Types in Function Signatures {#semantic_types_in_function_signatures_24}

*Source line: ~5*

**Test name:** `semantic_types_in_function_signatures_24`

**Description:**

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

**Linked Symbols:**
- `types`
- `Types`
- `function`
- `Signatures`
- `signatures`
- `SemanticTypesInFunctionSignatures`
- `Semantic`
- `Function`
- `semantic_types_in_function_signatures`
- `semantic`
- ... and 14 more

**Code:**

```simple
test "semantic_types_in_function_signatures_24":
    # WARNING: Bare primitives in public API
    pub fn get_user_id() -> i64:        # Warning: use unit type
        return 42

    # GOOD: Semantic types (no warning)
    pub fn get_user_id() -> UserId:     # OK
        return 42_uid

    # GOOD: Enums instead of bool
    pub fn set_status(status: UserStatus):  # OK
        ...

    # GOOD: Option for nullable returns
    pub fn find_user(id: UserId) -> Option[User]:  # OK
        ...
    assert_compiles()
```

---

## Source Code

**View full specification:** [functions_spec.spl](../../tests/specs/functions_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/functions_spec.spl`*

# Simple Language Type System

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/types_spec.spl`
> **Generated:** 2026-01-09 06:23:37
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/types_spec.spl
> ```

**Status:** Stable
**Feature IDs:** #20-29
**Keywords:** types, mutability, generics, type-inference
**Last Updated:** 2025-12-28
**Topics:** type-system
**Symbols:** Type, TypeVar, Mutability, Generic
**Module:** simple_type

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (13 tests)
- [Source Code](#source-code)

## Overview

Complete specification of Simple's type system, including primitives, composites, generics, and mutability rules.

The type system provides:
- Strong static typing with inference
- Immutable-by-default data structures
- Generic types with constraints
- Unit types for dimensional analysis
- Semantic type checking

## Related Specifications

- **Syntax** - Type annotation syntax
- **Type Inference** - Hindley-Milner inference algorithm
- **Data Structures** - Composite types
- **Memory** - Ownership and reference types

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `APIs` | [12](#primitive_type_warnings_public_apis_16) |
| `Access` | [6](#unit_types_and_literal_suffixes_6) |
| `Actual` | [1](#fetch_user) |
| `And` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `Apis` | [12](#primitive_type_warnings_public_apis_16) |
| `Async` | [1](#fetch_user) |
| `BaseType` | [5](#unit_types_and_literal_suffixes_5), [9](#unit_types_and_literal_suffixes_9) |
| `Calc` | [11](#internal_calc) |
| `Celsius` | [9](#unit_types_and_literal_suffixes_9) |
| `Class` | [3](#mutability_rules_3) |
| `Color` | [3](#mutability_rules_3) |
| `Comparisons` | [6](#unit_types_and_literal_suffixes_6) |
| `Compile` | [10](#unit_types_and_literal_suffixes_10) |
| `Compiler` | [8](#unit_types_and_literal_suffixes_8) |
| `Cursor` | [2](#mutability_rules_2), [13](#type_inference_17) |
| `Declared` | [1](#fetch_user) |
| `ERROR` | [10](#unit_types_and_literal_suffixes_10) |
| `Error` | [13](#type_inference_17) |
| `Fahrenheit` | [9](#unit_types_and_literal_suffixes_9) |
| `Fetch` | [1](#fetch_user) |
| `FetchUser` | [1](#fetch_user) |
| `Function` | [1](#fetch_user) |
| `Immutable` | [2](#mutability_rules_2) |
| `Inference` | [13](#type_inference_17) |
| `Internal` | [11](#internal_calc) |
| `InternalCalc` | [11](#internal_calc) |
| `Links` | [1](#fetch_user), [2](#mutability_rules_2), [3](#mutability_rules_3) |
| `Literal` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `MAX` | [4](#mutability_rules_4) |
| `Mutability` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `MutabilityRules` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `Name` | [9](#unit_types_and_literal_suffixes_9) |
| `Newton` | [7](#unit_types_and_literal_suffixes_7) |
| `Operations` | [6](#unit_types_and_literal_suffixes_6) |
| `Percentage` | [9](#unit_types_and_literal_suffixes_9) |
| `Person` | [3](#mutability_rules_3) |
| `Point` | [2](#mutability_rules_2), [13](#type_inference_17) |
| `Price` | [11](#internal_calc) |
| `Primitive` | [12](#primitive_type_warnings_public_apis_16) |
| `PrimitiveTypeWarningsPublicApis` | [12](#primitive_type_warnings_public_apis_16) |
| `Promise` | [1](#fetch_user) |
| `Public` | [11](#internal_calc), [12](#primitive_type_warnings_public_apis_16) |
| `Quantity` | [11](#internal_calc) |
| `Related` | [1](#fetch_user), [3](#mutability_rules_3) |
| `Rules` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `String` | [3](#mutability_rules_3) |
| `Struct` | [2](#mutability_rules_2) |
| `Suffixes` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `Syntax` | [5](#unit_types_and_literal_suffixes_5), [9](#unit_types_and_literal_suffixes_9) |
| `Total` | [11](#internal_calc) |
| `Type` | [1](#fetch_user), [12](#primitive_type_warnings_public_apis_16), [13](#type_inference_17) |
| `TypeInference` | [13](#type_inference_17) |
| `Types` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `Unit` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `UnitTypesAndLiteralSuffixes` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `Usage` | [9](#unit_types_and_literal_suffixes_9) |
| `User` | [1](#fetch_user) |
| `UserId` | [1](#fetch_user), [9](#unit_types_and_literal_suffixes_9) |
| `Using` | [1](#fetch_user) |
| `Warnings` | [12](#primitive_type_warnings_public_apis_16) |
| `and` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `apis` | [12](#primitive_type_warnings_public_apis_16) |
| `area` | [7](#unit_types_and_literal_suffixes_7) |
| `as_km` | [6](#unit_types_and_literal_suffixes_6) |
| `as_m` | [6](#unit_types_and_literal_suffixes_6) |
| `as_mile` | [6](#unit_types_and_literal_suffixes_6) |
| `assert_compiles` | [1](#fetch_user), [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4), [5](#unit_types_and_literal_suffixes_5), ... (12 total) |
| `calc` | [11](#internal_calc) |
| `calculate_total` | [11](#internal_calc) |
| `deny` | [12](#primitive_type_warnings_public_apis_16) |
| `family` | [6](#unit_types_and_literal_suffixes_6) |
| `fetch` | [1](#fetch_user) |
| `fetch_user` | [1](#fetch_user) |
| `force` | [7](#unit_types_and_literal_suffixes_7) |
| `from_raw` | [11](#internal_calc) |
| `get` | [1](#fetch_user) |
| `inference` | [13](#type_inference_17) |
| `internal` | [11](#internal_calc) |
| `internal_calc` | [11](#internal_calc) |
| `length` | [5](#unit_types_and_literal_suffixes_5) |
| `literal` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `mass` | [5](#unit_types_and_literal_suffixes_5) |
| `mutability` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `mutability_rules` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `mutable` | [4](#mutability_rules_4) |
| `name` | [5](#unit_types_and_literal_suffixes_5) |
| `parse` | [1](#fetch_user) |
| `primitive` | [12](#primitive_type_warnings_public_apis_16) |
| `primitive_type_warnings_public_apis` | [12](#primitive_type_warnings_public_apis_16) |
| `public` | [12](#primitive_type_warnings_public_apis_16) |
| `raw` | [11](#internal_calc) |
| `rules` | [2](#mutability_rules_2), [3](#mutability_rules_3), [4](#mutability_rules_4) |
| `second` | [7](#unit_types_and_literal_suffixes_7) |
| `suffixes` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `time` | [5](#unit_types_and_literal_suffixes_5) |
| `type` | [12](#primitive_type_warnings_public_apis_16), [13](#type_inference_17) |
| `type_inference` | [13](#type_inference_17) |
| `types` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `unit` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `unit_types_and_literal_suffixes` | [5](#unit_types_and_literal_suffixes_5), [6](#unit_types_and_literal_suffixes_6), [7](#unit_types_and_literal_suffixes_7), [8](#unit_types_and_literal_suffixes_8), [9](#unit_types_and_literal_suffixes_9), ... (6 total) |
| `user` | [1](#fetch_user) |
| `variable` | [4](#mutability_rules_4) |
| `velocity` | [7](#unit_types_and_literal_suffixes_7) |
| `warnings` | [12](#primitive_type_warnings_public_apis_16) |

---

## Test Cases (13 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [fetch_user](#fetch_user) | Built-in Types | `fetch`, `Fetch`, `user` +16 |
| 2 | [mutability_rules_2](#mutability_rules_2) | Mutability Rules | `rules`, `mutability`, `Mutability` +9 |
| 3 | [mutability_rules_3](#mutability_rules_3) | Mutability Rules | `rules`, `mutability`, `Mutability` +10 |
| 4 | [mutability_rules_4](#mutability_rules_4) | Mutability Rules | `rules`, `mutability`, `Mutability` +7 |
| 5 | [unit_types_and_literal_suffixes_5](#unit_types_and_literal_suffixes_5) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +16 |
| 6 | [unit_types_and_literal_suffixes_6](#unit_types_and_literal_suffixes_6) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +17 |
| 7 | [unit_types_and_literal_suffixes_7](#unit_types_and_literal_suffixes_7) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +15 |
| 8 | [unit_types_and_literal_suffixes_8](#unit_types_and_literal_suffixes_8) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +11 |
| 9 | [unit_types_and_literal_suffixes_9](#unit_types_and_literal_suffixes_9) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +18 |
| 10 | [unit_types_and_literal_suffixes_10](#unit_types_and_literal_suffixes_10) | Unit Types and Literal Suffixes | `literal`, `and`, `UnitTypesAndLiteralSuffixes` +12 |
| 11 | [internal_calc](#internal_calc) | Primitive Type Warnings (Public APIs) | `internal_calc`, `internal`, `Internal` +10 |
| 12 | [primitive_type_warnings_public_apis_16](#primitive_type_warnings_public_apis_16) | Primitive Type Warnings (Public APIs) | `type`, `primitive_type_warnings_public_apis`, `Type` +12 |
| 13 | [type_inference_17](#type_inference_17) | Type Inference | `type`, `TypeInference`, `Type` +7 |

---

### Test 1: Built-in Types {#fetch_user}

**Test name:** `fetch_user`

**Linked Symbols:**
- `fetch`
- `Fetch`
- `user`
- `User`
- `fetch_user`
- `FetchUser`
- `Using`
- `Related`
- `UserId`
- `Links`
- ... and 9 more

**Code:**

```simple
test "fetch_user":
    """
    Async functions return Promise types automatically.
    
    **Links:** Promise, Type::Function
    **Related:** mutability_rules_2
    """
    # Declared return type: User
    # Actual return type: Promise[User]
    fn fetch_user(id: UserId) -> User:
        let resp ~= http.get("/users/{id}")
        return parse(resp)

    # Using the promise
    let user ~= fetch_user(1_uid)      # user: User (awaited)
    let promise = fetch_user(1_uid)     # promise: Promise[User]
    assert_compiles()
```

### Test 2: Mutability Rules {#mutability_rules_2}

**Test name:** `mutability_rules_2`

**Linked Symbols:**
- `rules`
- `mutability`
- `Mutability`
- `Rules`
- `mutability_rules`
- `MutabilityRules`
- `Point`
- `Links`
- `assert_compiles`
- `Immutable`
- ... and 2 more

**Code:**

```simple
test "mutability_rules_2":
    """
    Immutable vs mutable struct declarations.
    
    **Links:** Mutability, Struct
    """
    struct Point:
        x: f64
        y: f64

    mut struct Cursor:
        x: f64
        y: f64
    assert_compiles()
```

### Test 3: Mutability Rules {#mutability_rules_3}

**Test name:** `mutability_rules_3`

**Linked Symbols:**
- `rules`
- `mutability`
- `Mutability`
- `Rules`
- `mutability_rules`
- `MutabilityRules`
- `Related`
- `Person`
- `Links`
- `Class`
- ... and 3 more

**Code:**

```simple
test "mutability_rules_3":
    """
    Mutability applies to fields and behavior.
    
    **Links:** Mutability, Class
    **Related:** mutability_rules_2
    """
    class Person:
        name: String
        age: i32

    immut class Color:
        red: u8
        green: u8
        blue: u8
    assert_compiles()
```

### Test 4: Mutability Rules {#mutability_rules_4}

**Test name:** `mutability_rules_4`

**Linked Symbols:**
- `rules`
- `mutability`
- `Mutability`
- `Rules`
- `mutability_rules`
- `MutabilityRules`
- `mutable`
- `assert_compiles`
- `variable`
- `MAX`

**Code:**

```simple
test "mutability_rules_4":
    """
    Mutability Rules
    """
    x = 10            # mutable variable (let is optional)
    let y = 20        # also mutable (let is explicit but optional)
    x = 30            # ok, x is mutable
    y = 40            # ok, y is mutable

    const MAX = 100   # immutable constant
    MAX = 200         # compile error, const cannot be reassigned
    assert_compiles()
```

### Test 5: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_5}

**Test name:** `unit_types_and_literal_suffixes_5`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 9 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_5":
    """
    Unit Types and Literal Suffixes
    """
    # Syntax: unit name(base: BaseType): suffix = factor, ...
    unit length(base: f64):
        mm = 0.001        # 1 mm = 0.001 meters
        cm = 0.01         # 1 cm = 0.01 meters
        m = 1.0           # base unit
        km = 1000.0       # 1 km = 1000 meters
        inch = 0.0254
        ft = 0.3048
        mile = 1609.34

    unit time(base: f64):
        ns = 0.000000001
        us = 0.000001
        ms = 0.001
        s = 1.0           # base unit
        min = 60.0
        hr = 3600.0

    unit mass(base: f64):
        mg = 0.000001
        g = 0.001
        kg = 1.0          # base unit
        lb = 0.453592
    assert_compiles()
```

### Test 6: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_6}

**Test name:** `unit_types_and_literal_suffixes_6`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 10 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_6":
    """
    Unit Types and Literal Suffixes
    """
    let distance = 100_km         # length type, stored as 100000.0 (meters)
    let duration = 2_hr           # time type, stored as 7200.0 (seconds)
    let weight = 5_kg             # mass type, stored as 5.0 (kg)

    # Access value in specific unit
    distance.as_km()              # 100.0
    distance.as_m()               # 100000.0
    distance.as_mile()            # 62.137...

    # Operations within same family (auto-converts)
    let total = 1_km + 500_m      # 1500_m (stored as 1500.0)

    # Comparisons work across units
    1_km == 1000_m                # true
    assert_compiles()
```

### Test 7: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_7}

**Test name:** `unit_types_and_literal_suffixes_7`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 8 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_7":
    """
    Unit Types and Literal Suffixes
    """
    unit velocity(base: f64) = length / time:
        mps = 1.0         # meters per second (base)
        kmph = 0.277778   # km/hr in m/s
        mph = 0.44704     # miles/hr in m/s

    unit area(base: f64) = length * length:
        sqmm = 0.000001
        sqcm = 0.0001
        sqm = 1.0         # base
        sqkm = 1000000.0

    unit force(base: f64) = mass * acceleration:
        N = 1.0           # Newton (base)
        kN = 1000.0
    assert_compiles()
```

### Test 8: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_8}

**Test name:** `unit_types_and_literal_suffixes_8`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 4 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_8":
    """
    Unit Types and Literal Suffixes
    """
    let distance = 100_km
    let duration = 2_hr

    # Compiler infers: length / time = velocity
    let speed = distance / duration    # velocity type, 50_kmph

    # Compiler infers: velocity * time = length
    let new_dist = speed * 3_hr        # length type, 150_km
    assert_compiles()
```

### Test 9: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_9}

**Test name:** `unit_types_and_literal_suffixes_9`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 11 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_9":
    """
    Unit Types and Literal Suffixes
    """
    # Syntax: unit Name: BaseType as suffix [= factor]
    unit UserId: i64 as uid
    unit Percentage: f64 as pct = 0.01        # 50_pct = 0.5 internally
    unit Celsius: f64 as c
    unit Fahrenheit: f64 as f

    # Usage
    let user = 42_uid
    let discount = 20_pct                      # stored as 0.2
    let temp = 25_c
    assert_compiles()
```

### Test 10: Unit Types and Literal Suffixes {#unit_types_and_literal_suffixes_10}

**Test name:** `unit_types_and_literal_suffixes_10`

**Linked Symbols:**
- `literal`
- `and`
- `UnitTypesAndLiteralSuffixes`
- `unit_types_and_literal_suffixes`
- `And`
- `suffixes`
- `Suffixes`
- `Unit`
- `Types`
- `types`
- ... and 5 more

**Code:**

```simple
test "unit_types_and_literal_suffixes_10":
    """
    Unit Types and Literal Suffixes
    """
    let distance = 100_km
    let duration = 2_hr

    # ERROR: different unit families
    let bad = distance + duration    # Compile error: length + time

    # OK: same family
    let ok = 1_km + 500_m            # OK: both length
    assert_compiles()
```

### Test 11: Primitive Type Warnings (Public APIs) {#internal_calc}

**Test name:** `internal_calc`

**Linked Symbols:**
- `internal_calc`
- `internal`
- `Internal`
- `calc`
- `InternalCalc`
- `Calc`
- `raw`
- `from_raw`
- `calculate_total`
- `Total`
- ... and 3 more

**Code:**

```simple
fn internal_calc(a: i64, b: i64) -> i64:
    return a + b

# Public wrapper uses semantic types
pub fn calculate_total(price: Price, quantity: Quantity) -> Total:
    let raw = internal_calc(price.raw(), quantity.raw())
    return Total.from_raw(raw)
```

### Test 12: Primitive Type Warnings (Public APIs) {#primitive_type_warnings_public_apis_16}

**Test name:** `primitive_type_warnings_public_apis_16`

**Linked Symbols:**
- `type`
- `primitive_type_warnings_public_apis`
- `Type`
- `apis`
- `public`
- `Apis`
- `Primitive`
- `warnings`
- `PrimitiveTypeWarningsPublicApis`
- `Public`
- ... and 5 more

**Code:**

```simple
test "primitive_type_warnings_public_apis_16":
    """
    Primitive Type Warnings (Public APIs)
    """
    # std/__init__.spl
    #[deny(primitive_api)]
    mod std

    pub mod core
    pub mod collections
    # ... all child modules inherit the deny setting
    assert_compiles()
```

### Test 13: Type Inference {#type_inference_17}

**Test name:** `type_inference_17`

**Linked Symbols:**
- `type`
- `TypeInference`
- `Type`
- `inference`
- `Inference`
- `type_inference`
- `Point`
- `assert_compiles`
- `Error`
- `Cursor`

**Code:**

```simple
test "type_inference_17":
    """
    Type Inference
    """
    # Type inferred as Point (immutable)
    let p = Point(3, 4)
    # p.x = 5          # Error: Point is immutable

    # Type inferred as Cursor (mutable)
    let cur = Cursor(0, 0)
    cur.x = 5           # OK: Cursor is mutable
    assert_compiles()
```

---

## Source Code

**View full specification:** [types_spec.spl](../../tests/specs/types_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/types_spec.spl`*

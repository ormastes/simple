# Simple Language Type System

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/types_spec.spl`
> **Generated:** 2026-01-09 04:37:07
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

## Overview

Complete specification of Simple's type system, including primitives, composites, generics, and mutability rules.

## Related Specifications

- **Syntax** - Type annotation syntax
- **Units** - Semantic unit types
- **Data Structures** - Composite types
- **Memory** - Ownership and reference types

---

## Test Cases (13 total)

| Test | Section | Description |
|------|---------|-------------|
| [fetch_user](#test-1) | Built-in Types |  |
| [mutability_rules_2](#test-2) | Mutability Rules |  |
| [mutability_rules_3](#test-3) | Mutability Rules |  |
| [mutability_rules_4](#test-4) | Mutability Rules |  |
| [unit_types_and_literal_suffixes_5](#test-5) | Unit Types and Literal Suffixes |  |
| [unit_types_and_literal_suffixes_6](#test-6) | Unit Types and Literal Suffixes |  |
| [unit_types_and_literal_suffixes_7](#test-7) | Unit Types and Literal Suffixes |  |
| [unit_types_and_literal_suffixes_8](#test-8) | Unit Types and Literal Suffixes |  |
| [unit_types_and_literal_suffixes_9](#test-9) | Unit Types and Literal Suffixes |  |
| [unit_types_and_literal_suffixes_10](#test-10) | Unit Types and Literal Suffixes |  |
| [internal_calc](#test-11) | Primitive Type Warnings (Public APIs) |  |
| [primitive_type_warnings_public_apis_16](#test-12) | Primitive Type Warnings (Public APIs) |  |
| [type_inference_17](#test-13) | Type Inference |  |

---

### Test 1: Built-in Types

**Test name:** `fetch_user`

**Code:**

```simple
fn fetch_user(id: UserId) -> User:
    let resp ~= http.get("/users/{id}")
    return parse(resp)

# Using the promise
let user ~= fetch_user(1_uid)      # user: User (awaited)
let promise = fetch_user(1_uid)     # promise: Promise[User]
```

### Test 2: Mutability Rules

**Test name:** `mutability_rules_2`

**Code:**

```simple
test "mutability_rules_2":
    """
    Mutability Rules
    """
    struct Point:
        x: f64
        y: f64

    mut struct Cursor:
        x: f64
        y: f64
    assert_compiles()
```

### Test 3: Mutability Rules

**Test name:** `mutability_rules_3`

**Code:**

```simple
test "mutability_rules_3":
    """
    Mutability Rules
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

### Test 4: Mutability Rules

**Test name:** `mutability_rules_4`

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

### Test 5: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_5`

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

### Test 6: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_6`

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

### Test 7: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_7`

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

### Test 8: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_8`

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

### Test 9: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_9`

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

### Test 10: Unit Types and Literal Suffixes

**Test name:** `unit_types_and_literal_suffixes_10`

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

### Test 11: Primitive Type Warnings (Public APIs)

**Test name:** `internal_calc`

**Code:**

```simple
fn internal_calc(a: i64, b: i64) -> i64:
    return a + b

# Public wrapper uses semantic types
pub fn calculate_total(price: Price, quantity: Quantity) -> Total:
    let raw = internal_calc(price.raw(), quantity.raw())
    return Total.from_raw(raw)
```

### Test 12: Primitive Type Warnings (Public APIs)

**Test name:** `primitive_type_warnings_public_apis_16`

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

### Test 13: Type Inference

**Test name:** `type_inference_17`

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

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/types_spec.spl`*

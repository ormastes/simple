# Simple Language Functions and Pattern Matching - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/functions_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/functions_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** functions.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from functions.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/functions.md

---

## Test Cases (24 total)

| Test | Section | Description |
|------|---------|-------------|
| [add](#test-1) | Functions | Functions in Simple are defined with the `fn` keyword. The s... |
| [functions_2](#test-2) | Functions | Functions have an inferred async/sync effect based on their ... |
| [functions_3](#test-3) | Functions | Simple supports first-class functions - you can assign funct... |
| [lambdas_and_closures_4](#test-4) | Lambdas and Closures | An inline lambda uses a backslash to introduce parameters (i... |
| [lambdas_and_closures_5](#test-5) | Lambdas and Closures | The backslash syntax was chosen for one-pass parsing - seein... |
| [lambdas_and_closures_6](#test-6) | Lambdas and Closures | Lambdas capture variables from their enclosing scope: |
| [lambdas_and_closures_7](#test-7) | Lambdas and Closures | Methods can accept trailing blocks for iteration or DSL cons... |
| [pattern_matching_8](#test-8) | Pattern Matching | Pattern matching is a powerful feature enabling branching on... |
| [pattern_matching_9](#test-9) | Pattern Matching | fn describe_token(tok: Token) -> String:... |
| [pattern_matching_10](#test-10) | Pattern Matching | ```simple... |
| [pattern_matching_11](#test-11) | Pattern Matching | ```simple... |
| [pattern_matching_12](#test-12) | Pattern Matching | ```simple... |
| [pattern_matching_13](#test-13) | Pattern Matching | ```simple... |
| [pattern_matching_14](#test-14) | Pattern Matching | let p = Point(x: 5, y: 0)... |
| [pattern_matching_15](#test-15) | Pattern Matching | All possibilities must be covered (exhaustive matching), oth... |
| [constructor_polymorphism_16](#test-16) | Constructor Polymorphism | The `Constructor[T]` type represents any constructor that pr... |
| [constructor_polymorphism_17](#test-17) | Constructor Polymorphism | ```simple... |
| [constructor_polymorphism_18](#test-18) | Constructor Polymorphism | 1. Must accept all required parameters of parent constructor... |
| [constructor_polymorphism_19](#test-19) | Constructor Polymorphism | \| Parent Constructor \| Child Constructor \| Valid? \| Reason \|... |
| [constructor_polymorphism_20](#test-20) | Constructor Polymorphism | let factory = get_widget_factory("button")... |
| [constructor_polymorphism_21](#test-21) | Constructor Polymorphism | Specify exact constructor signatures: |
| [constructor_polymorphism_22](#test-22) | Constructor Polymorphism | Constructor polymorphism enables clean dependency injection: |
| [constructor_polymorphism_23](#test-23) | Constructor Polymorphism | Use traits to define abstract constructor requirements: |
| [semantic_types_in_function_signatures_24](#test-24) | Semantic Types in Function Signatures | Public functions should use semantic types (unit types, enum... |

---

### Test 1: Functions

*Source line: ~7*

**Test name:** `add`

**Description:**

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

**Code:**

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b
```

### Test 2: Functions

*Source line: ~18*

**Test name:** `functions_2`

**Description:**

Functions have an inferred async/sync effect based on their body:

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

### Test 3: Functions

*Source line: ~52*

**Test name:** `functions_3`

**Description:**

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

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

### Test 4: Lambdas and Closures

*Source line: ~7*

**Test name:** `lambdas_and_closures_4`

**Description:**

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

**Code:**

```simple
test "lambdas_and_closures_4":
    let square = \x: x * x
    let double = \x: x * 2

    # With explicit type annotations
    let typed_square = \(x: i64) -> i64: x * x
    assert_compiles()
```

### Test 5: Lambdas and Closures

*Source line: ~19*

**Test name:** `lambdas_and_closures_5`

**Description:**

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

**Code:**

```simple
test "lambdas_and_closures_5":
    let add = \a, b: a + b
    let sum = add(3, 4)  # 7

    # With types
    let typed_add = \(a: i64, b: i64) -> i64: a + b
    assert_compiles()
```

### Test 6: Lambdas and Closures

*Source line: ~31*

**Test name:** `lambdas_and_closures_6`

**Description:**

Lambdas capture variables from their enclosing scope:

**Code:**

```simple
test "lambdas_and_closures_6":
    let multiplier = 3
    let scale = \x: x * multiplier

    scale(10)  # 30
    assert_compiles()
```

### Test 7: Lambdas and Closures

*Source line: ~42*

**Test name:** `lambdas_and_closures_7`

**Description:**

Methods can accept trailing blocks for iteration or DSL constructs:

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

### Test 8: Pattern Matching

*Source line: ~7*

**Test name:** `pattern_matching_8`

**Description:**

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expr...

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

### Test 9: Pattern Matching

*Source line: ~30*

**Test name:** `pattern_matching_9`

**Description:**

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

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

### Test 10: Pattern Matching

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

**Code:**

```simple
test "pattern_matching_10":
    match x:
        case 1 | 2 | 3:
            print "Small number"
    assert_compiles()
```

### Test 11: Pattern Matching

*Source line: ~48*

**Test name:** `pattern_matching_11`

**Description:**

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

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

### Test 12: Pattern Matching

*Source line: ~60*

**Test name:** `pattern_matching_12`

**Description:**

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
...

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

### Test 13: Pattern Matching

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

### Test 14: Pattern Matching

*Source line: ~89*

**Test name:** `pattern_matching_14`

**Description:**

let p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point...

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

### Test 15: Pattern Matching

*Source line: ~102*

**Test name:** `pattern_matching_15`

**Description:**

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

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

### Test 16: Constructor Polymorphism

*Source line: ~9*

**Test name:** `constructor_polymorphism_16`

**Description:**

The `Constructor[T]` type represents any constructor that produces an instance of `T` or a subtype:

**Code:**

```simple
test "constructor_polymorphism_16":
    # Constructor[T] - type for constructors producing T or subtypes
    let factory: Constructor[Widget] = Button    # Button extends Widget
    let widget = factory("OK")                   # Creates a Button
    assert_compiles()
```

### Test 17: Constructor Polymorphism

*Source line: ~17*

**Test name:** `constructor_polymorphism_17`

**Description:**

```simple
# Constructor[T] - type for constructors producing T or subtypes
let factory: Constructor[...

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

### Test 18: Constructor Polymorphism

*Source line: ~47*

**Test name:** `constructor_polymorphism_18`

**Description:**

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

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

### Test 19: Constructor Polymorphism

*Source line: ~76*

**Test name:** `constructor_polymorphism_19`

**Description:**

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

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

### Test 20: Constructor Polymorphism

*Source line: ~96*

**Test name:** `constructor_polymorphism_20`

**Description:**

let factory = get_widget_factory("button")
let w = factory("Dynamic Button")
```

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

### Test 21: Constructor Polymorphism

*Source line: ~116*

**Test name:** `constructor_polymorphism_21`

**Description:**

Specify exact constructor signatures:

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

### Test 22: Constructor Polymorphism

*Source line: ~130*

**Test name:** `constructor_polymorphism_22`

**Description:**

Constructor polymorphism enables clean dependency injection:

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

### Test 23: Constructor Polymorphism

*Source line: ~162*

**Test name:** `constructor_polymorphism_23`

**Description:**

Use traits to define abstract constructor requirements:

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

### Test 24: Semantic Types in Function Signatures

*Source line: ~5*

**Test name:** `semantic_types_in_function_signatures_24`

**Description:**

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

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

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/functions_spec.spl`*

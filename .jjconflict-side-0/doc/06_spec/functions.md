# Simple Language Functions and Pattern Matching - Test Specification

This file contains executable test cases extracted from functions.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | functions.md |
| Source | `test/specs/functions_spec.spl` |
| Updated | 2026-03-30 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This file contains executable test cases extracted from functions.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/functions.md

## Extracted Test Cases

24 test cases extracted covering:
- Core functionality examples
- Edge cases and validation
- Integration patterns

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

Functions have an inferred async/sync effect based on their body:

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

Lambdas capture variables from their enclosing scope:

Methods can accept trailing blocks for iteration or DSL constructs:

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expr...

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

```simple
match x:
    case 0:
        print "Zero"
    case 1:
        print "One"
```

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
...

```simple
match x:
    case 0:
        print "Zero"
    case _:
        print "Non-zero"
```

val p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point...

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

The `Constructor<T>` type represents any constructor that produces an instance of `T` or a subtype:

```simple
# Constructor<T> - type for constructors producing T or subtypes
val factory: Constructor[...

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

val factory = get_widget_factory("button")
val w = factory("Dynamic Button")
```

Specify exact constructor signatures:

Constructor polymorphism enables clean dependency injection:

Use traits to define abstract constructor requirements:

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

## Example Details

| Example | Kind | Reference |
|---------|------|-----------|
| 1 | Function example | Line ~7 |
| 2 | Scenario | Line ~18 |
| 3 | Scenario | Line ~52 |
| 4 | Scenario | Line ~7 |
| 5 | Scenario | Line ~19 |
| 6 | Scenario | Line ~31 |
| 7 | Scenario | Line ~42 |
| 8 | Scenario | Line ~7 |
| 9 | Scenario | Line ~30 |
| 10 | Scenario | Line ~40 |
| 11 | Scenario | Line ~48 |
| 12 | Scenario | Line ~60 |
| 13 | Scenario | Line ~70 |
| 14 | Scenario | Line ~89 |
| 15 | Scenario | Line ~102 |
| 16 | Scenario | Line ~9 |
| 17 | Scenario | Line ~17 |
| 18 | Scenario | Line ~47 |
| 19 | Scenario | Line ~76 |
| 20 | Scenario | Line ~96 |
| 21 | Code example | Line ~116 |
| 22 | Scenario | Line ~130 |
| 23 | Scenario | Line ~162 |
| 24 | Scenario | Line ~5 |

### 1. Functions

*Kind: Function example | Reference: Line ~7 | Scenario: `add`*

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

```simple
fn add(a: i64, b: i64) -> i64:
    return a + b
```

### 2. Functions

*Kind: Scenario | Reference: Line ~18 | Scenario: `functions_2`*

Functions have an inferred async/sync effect based on their body:

```simple
it "functions_2":
    # Inferred as SYNC: only pure computation
    fn double(x: i64) -> i64:
        return x * 2

    # Inferred as ASYNC: uses suspension operator
    fn fetch_user(id: UserId) -> User:
        val user ~= http.get("/users/{id}")
        return user

    # Explicit SYNC: compiler verifies no suspension
    sync fn compute(x: i64) -> i64:
        return x * x

    # Explicit ASYNC: documentation, no behavioral change
    async fn load_data() -> Data:
        val d ~= read_file(path)
        return d
    pass
```

### 3. Functions

*Kind: Scenario | Reference: Line ~52 | Scenario: `functions_3`*

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

```simple
it "functions_3":
    val math_op = add
    val result = math_op(2, 3)  # 5

    fn apply(f: fn(i64, i64) -> i64, x: i64, y: i64) -> i64:
        return f(x, y)

    apply(add, 10, 20)  # 30
    pass
```

### 4. Lambdas and Closures

*Kind: Scenario | Reference: Line ~7 | Scenario: `lambdas_and_closures_4`*

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

```simple
it "lambdas_and_closures_4":
    val square = \x: x * x
    val double = \x: x * 2

    # With explicit type annotations (TODO: not yet supported)
    # val typed_square = \(x: i64) -> i64: x * x
    pass
```

### 5. Lambdas and Closures

*Kind: Scenario | Reference: Line ~19 | Scenario: `lambdas_and_closures_5`*

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

```simple
it "lambdas_and_closures_5":
    val add = \a, b: a + b
    val sum = add(3, 4)  # 7

    # With types (TODO: not yet supported)
    # val typed_add = \(a: i64, b: i64) -> i64: a + b
    pass
```

### 6. Lambdas and Closures

*Kind: Scenario | Reference: Line ~31 | Scenario: `lambdas_and_closures_6`*

Lambdas capture variables from their enclosing scope:

```simple
it "lambdas_and_closures_6":
    val multiplier = 3
    val scale = \x: x * multiplier

    scale(10)  # 30
    pass
```

### 7. Lambdas and Closures

*Kind: Scenario | Reference: Line ~42 | Scenario: `lambdas_and_closures_7`*

Methods can accept trailing blocks for iteration or DSL constructs:

```simple
it "lambdas_and_closures_7":
    # Requires list, map, numbers variables - pseudocode example
    pass_todo
```

### 8. Pattern Matching

*Kind: Scenario | Reference: Line ~7 | Scenario: `pattern_matching_8`*

Pattern matching is a powerful feature enabling branching on the structure of data. The `match` expr...

```simple
it "pattern_matching_8":
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
    pass
```

### 9. Pattern Matching

*Kind: Scenario | Reference: Line ~30 | Scenario: `pattern_matching_9`*

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

```simple
it "pattern_matching_9":
    # Requires x variable - pseudocode example
    val x = 1
    match x:
        0:
            print "Zero"
        1:
            print "One"
    pass
```

### 10. Pattern Matching

*Kind: Scenario | Reference: Line ~40 | Scenario: `pattern_matching_10`*

```simple
match x:
    case 0:
        print "Zero"
    case 1:
        print "One"
```

```simple
it "pattern_matching_10":
    # Requires or-pattern (|) - pseudocode example
    pass_todo
```

### 11. Pattern Matching

*Kind: Scenario | Reference: Line ~48 | Scenario: `pattern_matching_11`*

```simple
match x:
    case 1 | 2 | 3:
        print "Small number"
```

```simple
it "pattern_matching_11":
    # Requires guard patterns - pseudocode example
    pass_todo
```

### 12. Pattern Matching

*Kind: Scenario | Reference: Line ~60 | Scenario: `pattern_matching_12`*

```simple
match x:
    case n if n < 0:
        print "Negative number: {n}"
    case n if n > 100:
...

```simple
it "pattern_matching_12":
    val x = 1
    match x:
        0:
            print "Zero"
        _:
            print "Non-zero"
    pass
```

### 13. Pattern Matching

*Kind: Scenario | Reference: Line ~70 | Scenario: `pattern_matching_13`*

```simple
match x:
    case 0:
        print "Zero"
    case _:
        print "Non-zero"
```

```simple
it "pattern_matching_13":
    struct Point:
        x: f64
        y: f64

    val p = Point(x: 5, y: 0)
    match p:
        case Point(0, 0):
            print "Origin"
        case Point(x_val, 0):
            print "On X axis at {x_val}"
        case Point(0, y_val):
            print "On Y axis at {y_val}"
        case Point(_, _):
            print "Somewhere else"
    pass
```

### 14. Pattern Matching

*Kind: Scenario | Reference: Line ~89 | Scenario: `pattern_matching_14`*

val p = Point(x: 5, y: 0)
match p:
    case Point(x: 0, y: 0):
        print "Origin"
    case Point...

```simple
it "pattern_matching_14":
    val pair = (1, "hello")
    match pair:
        case (0, _):
            print "Starts with zero"
        case (n, s):
            print "Number {n} with string '{s}'"
    pass
```

### 15. Pattern Matching

*Kind: Scenario | Reference: Line ~102 | Scenario: `pattern_matching_15`*

All possibilities must be covered (exhaustive matching), otherwise the code will not compile:

```simple
it "pattern_matching_15":
    enum Color:
        Red
        Green
        Blue

    fn name(c: Color) -> str:
        match c:
            case Red: "red"
            case Green: "green"
            # Error: missing case Blue
    pass
```

### 16. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~9 | Scenario: `constructor_polymorphism_16`*

The `Constructor<T>` type represents any constructor that produces an instance of `T` or a subtype:

```simple
it "constructor_polymorphism_16":
    # Requires Constructor<T> feature - not yet implemented
    pass_todo
```

### 17. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~17 | Scenario: `constructor_polymorphism_17`*

```simple
# Constructor<T> - type for constructors producing T or subtypes
val factory: Constructor[...

```simple
it "constructor_polymorphism_17":
    # Requires inheritance and Constructor<T> - not yet implemented
    pass_todo
```

### 18. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~47 | Scenario: `constructor_polymorphism_18`*

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

```simple
it "constructor_polymorphism_18":
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
    pass
```

### 19. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~76 | Scenario: `constructor_polymorphism_19`*

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

```simple
it "constructor_polymorphism_19":
    # Generic factory function
    fn create_many<T>(ctor: Constructor<T>, names: [str]) -> [T]:
        return [ctor(name) for name in names]

    val buttons = create_many(Button, ["OK", "Cancel", "Help"])

    # Factory selector
    fn get_widget_factory(kind: str) -> Constructor<Widget>:
        match kind:
            case "button": return Button
            case "label": return Label
            case _: return Widget

    val factory = get_widget_factory("button")
    val w = factory("Dynamic Button")
    pass
```

### 20. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~96 | Scenario: `constructor_polymorphism_20`*

val factory = get_widget_factory("button")
val w = factory("Dynamic Button")
```

```simple
it "constructor_polymorphism_20":
    # Requires Constructor<T> collections - not yet implemented
    pass_todo
```

### 21. Constructor Polymorphism

*Kind: Code example | Reference: Line ~116*

Specify exact constructor signatures:

```simple
## TODO: Tuple syntax in generic type parameters not yet supported
# it "constructor_polymorphism_21":
#     # Constructor that takes exactly (str, i32)
#     fn exact_factory(ctor: Constructor<Widget, (str, i32)>) -> Widget:
#         return ctor("default", 42)
#
#     # Constructor that takes no parameters
#     fn no_arg_factory<T>(ctor: Constructor<T, ()>) -> T:
#         return ctor()
#     pass
```

### 22. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~130 | Scenario: `constructor_polymorphism_22`*

Constructor polymorphism enables clean dependency injection:

```simple
it "constructor_polymorphism_22":
    # Requires inheritance and Constructor<T> DI - not yet implemented
    pass_todo
```

### 23. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~162 | Scenario: `constructor_polymorphism_23`*

Use traits to define abstract constructor requirements:

```simple
it "constructor_polymorphism_23":
    trait Creatable:
        fn create(name: str) -> Self

    impl Creatable for Widget:
        fn create(name: str) -> Widget:
            return Widget.new(name)

    fn make<T: Creatable>(name: str) -> T:
        return T.create(name)
    pass
```

### 24. Semantic Types in Function Signatures

*Kind: Scenario | Reference: Line ~5 | Scenario: `semantic_types_in_function_signatures_24`*

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

```simple
it "semantic_types_in_function_signatures_24":
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
    pub fn find_user(id: UserId) -> Option<User>:  # OK
        ...
    pass
```

## Scenarios

- functions_2
- functions_3
- lambdas_and_closures_4
- lambdas_and_closures_5
- lambdas_and_closures_6
- lambdas_and_closures_7
- pattern_matching_8
- pattern_matching_9
- pattern_matching_10
- pattern_matching_11
- pattern_matching_12
- pattern_matching_13
- pattern_matching_14
- pattern_matching_15
- constructor_polymorphism_16
- constructor_polymorphism_17
- constructor_polymorphism_18
- constructor_polymorphism_19
- constructor_polymorphism_20
- constructor_polymorphism_22
- constructor_polymorphism_23
- semantic_types_in_function_signatures_24

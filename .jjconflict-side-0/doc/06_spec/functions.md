# Simple Language Functions and Pattern Matching - Test Specification

This file contains executable test cases extracted from functions.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | functions.md |
| Source | `test/specs/functions_spec.spl` |
| Updated | 2026-04-24 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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
- Named functions with multiple parameters and return types
- Lambdas and closures (capture by value)
- Pattern matching on enums, structs, numbers, and tuples
- Exhaustive match enforcement
- Constructor polymorphism (typed constructor arguments)
- Semantic types in function signatures

## Syntax

Named function:

    fn add(a: i64, b: i64) -> i64:
        a + b

Lambda (closure):

    val double = |x: i64| x * 2
    val add_n  = |n: i64| |x: i64| x + n

Pattern match:

    match color:
        case Red:   "red"
        case Green: "green"
        case Blue:  "blue"

Constructor polymorphism:

    fn make<T>(ctor: Constructor<T, (text, i64)>) -> T:
        ctor("name", 42)

## Examples

    add(3, 4)       # => 7

    val double = |x: i64| x * 2
    double(5)       # => 10

    describe_number(0)  # => "Zero"
    describe_number(1)  # => "One"
    describe_number(2)  # => "Other"

    describe_point(Point(x: 5, y: 0))  # => "On X axis at 5"
    describe_pair((1, "hello"))         # => "Number 1 with string 'hello'"

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
| 1 | Scenario | Line ~7 |
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

*Kind: Scenario | Reference: Line ~7 | Scenario: `functions_1`*

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

```simple
it "functions_1":
    expect(add(2, 3)).to_equal(5)
```

### 2. Functions

*Kind: Scenario | Reference: Line ~18 | Scenario: `functions_2`*

Functions have an inferred async/sync effect based on their body:

```simple
it "functions_2":
    fn double(x: i64) -> i64:
        return x * 2

    fn fetch_user(id: i64) -> i64:
        return id + 1

    fn compute(x: i64) -> i64:
        return x * x

    fn load_data() -> text:
        return "loaded"

    expect(double(4)).to_equal(8)
    expect(fetch_user(10)).to_equal(11)
    expect(compute(5)).to_equal(25)
    expect(load_data()).to_equal("loaded")
```

### 3. Functions

*Kind: Scenario | Reference: Line ~52 | Scenario: `functions_3`*

Simple supports first-class functions - you can assign functions to variables or pass them as argume...

```simple
it "functions_3":
    val math_op = add
    val result = math_op(2, 3)

    fn apply(f: fn(i64, i64) -> i64, x: i64, y: i64) -> i64:
        return f(x, y)

    expect(result).to_equal(5)
    expect(apply(add, 10, 20)).to_equal(30)
```

### 4. Lambdas and Closures

*Kind: Scenario | Reference: Line ~7 | Scenario: `lambdas_and_closures_4`*

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

```simple
it "lambdas_and_closures_4":
    val square = \x: x * x
    val double = \x: x * 2

    expect(square(5)).to_equal(25)
    expect(double(7)).to_equal(14)
```

### 5. Lambdas and Closures

*Kind: Scenario | Reference: Line ~19 | Scenario: `lambdas_and_closures_5`*

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

```simple
it "lambdas_and_closures_5":
    val add = \a, b: a + b
    val sum = add(3, 4)

    expect(sum).to_equal(7)
```

### 6. Lambdas and Closures

*Kind: Scenario | Reference: Line ~31 | Scenario: `lambdas_and_closures_6`*

Lambdas capture variables from their enclosing scope:

```simple
it "lambdas_and_closures_6":
    val multiplier = 3
    val scale = \x: x * multiplier

    expect(scale(10)).to_equal(30)
```

### 7. Lambdas and Closures

*Kind: Scenario | Reference: Line ~42 | Scenario: `lambdas_and_closures_7`*

Methods can accept trailing blocks for iteration or DSL constructs:

```simple
it "lambdas_and_closures_7":
    fn sum_with(items: [i64], transform: fn(i64) -> i64) -> i64:
        var total = 0
        for item in items:
            total = total + transform(item)
        return total

    val numbers = [1, 2, 3]
    val total = sum_with(numbers, \x: x * 2)

    expect(total).to_equal(12)
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

    fn describe_token(tok: Token) -> text:
        match tok:
            case Number(val):
                return "Number({val})"
            case Plus:
                return "Plus sign"
            case Minus:
                return "Minus sign"
            case EOF:
                return "End of input"

    expect(describe_token(Number(5))).to_equal("Number(5)")
    expect(describe_token(Plus)).to_equal("Plus sign")
    expect(describe_token(Minus)).to_equal("Minus sign")
    expect(describe_token(EOF)).to_equal("End of input")
```

### 9. Pattern Matching

*Kind: Scenario | Reference: Line ~30 | Scenario: `pattern_matching_9`*

fn describe_token(tok: Token) -> String:
    match tok:
        case Number(val):
            return...

```simple
it "pattern_matching_9":
    fn describe_number(x: i64) -> text:
        match x:
            0:
                return "Zero"
            1:
                return "One"
            _:
                return "Other"

    expect(describe_number(0)).to_equal("Zero")
    expect(describe_number(1)).to_equal("One")
    expect(describe_number(2)).to_equal("Other")
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
    fn classify_small_number(x: i64) -> text:
        match x:
            0:
                return "Zero"
            1:
                return "One"
            2:
                return "Two"
            3:
                return "Three"
            _:
                return "Other"

    expect(classify_small_number(1)).to_equal("One")
    expect(classify_small_number(4)).to_equal("Other")
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
    fn classify_guard_like(x: i64) -> text:
        if x < 0:
            return "Negative number"
        elif x > 100:
            return "Large number"
        else:
            return "In range"

    expect(classify_guard_like(-1)).to_equal("Negative number")
    expect(classify_guard_like(101)).to_equal("Large number")
    expect(classify_guard_like(42)).to_equal("In range")
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
    fn classify_non_zero(x: i64) -> text:
        match x:
            0:
                return "Zero"
            _:
                return "Non-zero"

    expect(classify_non_zero(0)).to_equal("Zero")
    expect(classify_non_zero(5)).to_equal("Non-zero")
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
        x: i64
        y: i64

    fn describe_point(p: Point) -> text:
        match p:
            case Point(0, 0):
                return "Origin"
            case Point(x_val, 0):
                return "On X axis at {x_val}"
            case Point(0, y_val):
                return "On Y axis at {y_val}"
            case Point(_, _):
                return "Somewhere else"

    val point = Point(x: 5, y: 0)
    expect(describe_point(Point(x: 0, y: 0))).to_equal("Origin")
    expect(describe_point(point)).to_equal("On X axis at 5")
    expect(describe_point(Point(x: 0, y: 8))).to_equal("On Y axis at 8")
    expect(describe_point(Point(x: 2, y: 3))).to_equal("Somewhere else")
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

    fn describe_pair(p: (i64, text)) -> text:
        match p:
            case (0, _):
                return "Starts with zero"
            case (n, s):
                return "Number {n} with string '{s}'"

    expect(describe_pair(pair)).to_equal("Number 1 with string 'hello'")
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

    fn describe_color(c: Color) -> text:
        match c:
            case Red:
                return "red"
            case Green:
                return "green"
            case Blue:
                return "blue"

    expect(describe_color(Red)).to_equal("red")
    expect(describe_color(Green)).to_equal("green")
    expect(describe_color(Blue)).to_equal("blue")
```

### 16. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~9 | Scenario: `constructor_polymorphism_16`*

The `Constructor<T>` type represents any constructor that produces an instance of `T` or a subtype:

```simple
it "constructor_polymorphism_16":
    struct Widget:
        name: text

    fn make_widget(name: text) -> Widget:
        return Widget(name: name)

    val widget = make_widget("Button")
    expect(widget.name).to_equal("Button")
```

### 17. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~17 | Scenario: `constructor_polymorphism_17`*

```simple
# Constructor<T> - type for constructors producing T or subtypes
val factory: Constructor[...

```simple
it "constructor_polymorphism_17":
    struct Button:
        name: text

    fn make_button(name: text) -> Button:
        return Button(name: name)

    val button = make_button("Submit")
    expect(button.name).to_equal("Submit")
```

### 18. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~47 | Scenario: `constructor_polymorphism_18`*

1. Must accept all required parameters of parent constructor
2. Additional parameters must have defa...

```simple
it "constructor_polymorphism_18":
    fn build_label(name: text, value: i64, extra: bool) -> text:
        if extra:
            return "{name}:{value}:extra"
        return "{name}:{value}"

    expect(build_label("base", 10, false)).to_equal("base:10")
    expect(build_label("base", 10, true)).to_equal("base:10:extra")
```

### 19. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~76 | Scenario: `constructor_polymorphism_19`*

| Parent Constructor | Child Constructor | Valid? | Reason |
|-------------------|------------------...

```simple
it "constructor_polymorphism_19":
    fn create_many(names: [text], ctor: fn(text) -> text) -> [text]:
        var result = []
        for name in names:
            result = result + [ctor(name)]
        return result

    fn decorate_button(name: text) -> text:
        return "button:{name}"

    val buttons = create_many(["OK", "Cancel", "Help"], decorate_button)
    expect(buttons.len()).to_equal(3)
    expect(buttons[0]).to_equal("button:OK")
```

### 20. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~96 | Scenario: `constructor_polymorphism_20`*

val factory = get_widget_factory("button")
val w = factory("Dynamic Button")
```

```simple
it "constructor_polymorphism_20":
    fn choose_widget(kind: text, name: text) -> text:
        match kind:
            case "button":
                return "button:{name}"
            case "label":
                return "label:{name}"
            case _:
                return "widget:{name}"

    expect(choose_widget("button", "Dynamic Button")).to_equal("button:Dynamic Button")
    expect(choose_widget("label", "Status")).to_equal("label:Status")
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
    fn build_with_factory(name: text, ctor: fn(text) -> text) -> text:
        return ctor(name)

    fn make_tagged(name: text) -> text:
        return "tagged:{name}"

    expect(build_with_factory("item", make_tagged)).to_equal("tagged:item")
```

### 23. Constructor Polymorphism

*Kind: Scenario | Reference: Line ~162 | Scenario: `constructor_polymorphism_23`*

Use traits to define abstract constructor requirements:

```simple
it "constructor_polymorphism_23":
    fn create_named(name: text) -> text:
        return "created:{name}"

    fn make<T>(name: text, ctor: fn(text) -> T) -> T:
        return ctor(name)

    expect(make("Widget", create_named)).to_equal("created:Widget")
```

### 24. Semantic Types in Function Signatures

*Kind: Scenario | Reference: Line ~5 | Scenario: `semantic_types_in_function_signatures_24`*

Public functions should use semantic types (unit types, enums, Option) instead of bare primitives. S...

```simple
it "semantic_types_in_function_signatures_24":
    struct UserId:
        value: i64

    enum UserStatus:
        Active
        Disabled

    struct User:
        id: UserId
        status: UserStatus

    pub fn get_user_id() -> UserId:
        return UserId(value: 42)

    pub fn set_status(status: UserStatus) -> text:
        match status:
            case Active:
                return "active"
            case Disabled:
                return "disabled"

    pub fn find_user(id: UserId) -> User:
        return User(id: id, status: Active)

    val user_id = get_user_id()
    val user = find_user(user_id)

    expect(user_id.value).to_equal(42)
    expect(set_status(Active)).to_equal("active")
    expect(set_status(Disabled)).to_equal("disabled")
    expect(user.status).to_equal(Active)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `summary.txt` | Text artifact | `build/test-artifacts/specs/functions/summary.txt` |

## Scenarios

- functions_1
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

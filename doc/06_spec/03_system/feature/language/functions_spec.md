# Simple Language Functions and Pattern Matching - Test Specification

> This file contains executable test cases extracted from functions.md. The original specification file remains as architectural reference documentation.

<!-- sdn-diagram:id=functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Functions and Pattern Matching - Test Specification

This file contains executable test cases extracted from functions.md. The original specification file remains as architectural reference documentation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Reference |
| Type | Extracted Examples (Category B) |
| Reference | functions.md |
| Source | `test/03_system/feature/language/functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This file contains executable test cases extracted from functions.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/06_spec/feature/language/functions_spec.md

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

## Example Details

### Functions (Line ~7)

Functions in Simple are defined with the `fn` keyword. The syntax is inspired by Python's definition...

```simple
it "functions_1":
    expect(add(2, 3)).to_equal(5)
```

### Functions (Line ~18)

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

### Functions (Line ~52)

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

### Lambdas and Closures (Line ~7)

An inline lambda uses a backslash to introduce parameters (inspired by ML-family languages):

```simple
it "lambdas_and_closures_4":
    val square = _1 * _1
    val double = _1 * 2

    expect(square(5)).to_equal(25)
    expect(double(7)).to_equal(14)
```

### Lambdas and Closures (Line ~19)

The backslash syntax was chosen for one-pass parsing - seeing `\` immediately signals a lambda, requ...

```simple
it "lambdas_and_closures_5":
    val add = \a, b: a + b
    val sum = add(3, 4)

    expect(sum).to_equal(7)
```

### Lambdas and Closures (Line ~31)

Lambdas capture variables from their enclosing scope:

```simple
it "lambdas_and_closures_6":
    val multiplier = 3
    val scale = _1 * multiplier

    expect(scale(10)).to_equal(30)
```

### Lambdas and Closures (Line ~42)

Methods can accept trailing blocks for iteration or DSL constructs:

```simple
it "lambdas_and_closures_7":
    fn sum_with(items: [i64], transform: fn(i64) -> i64) -> i64:
        var total = 0
        for item in items:
            total = total + transform(item)
        return total

    val numbers = [1, 2, 3]
    val total = sum_with(numbers, _1 * 2)

    expect(total).to_equal(12)
```

### Pattern Matching (Line ~7)

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
            case Number(n):
                return "Number({n})"
            case Plus:
                return "Plus sign"
            case Minus:
                return "Minus sign"
            case EOF:
                return "End of input"

    expect(describe_token(Token.Number(5))).to_equal("Number(5)")
    expect(describe_token(Token.Plus)).to_equal("Plus sign")
    expect(describe_token(Token.Minus)).to_equal("Minus sign")
    expect(describe_token(Token.EOF)).to_equal("End of input")
```

### Pattern Matching (Line ~30)

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

### Pattern Matching (Line ~40)

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

### Pattern Matching (Line ~48)

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

### Pattern Matching (Line ~60)

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

### Pattern Matching (Line ~70)

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

### Pattern Matching (Line ~89)

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

### Pattern Matching (Line ~102)

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

    expect(describe_color(Color.Red)).to_equal("red")
    expect(describe_color(Color.Green)).to_equal("green")
    expect(describe_color(Color.Blue)).to_equal("blue")
```

### Constructor Polymorphism (Line ~9)

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

### Constructor Polymorphism (Line ~17)

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

### Constructor Polymorphism (Line ~47)

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

### Constructor Polymorphism (Line ~76)

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

### Constructor Polymorphism (Line ~96)

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

### Constructor Polymorphism (Line ~116)

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

### Constructor Polymorphism (Line ~130)

Constructor polymorphism enables clean dependency injection:

```simple
it "constructor_polymorphism_22":
    fn build_with_factory(name: text, ctor: fn(text) -> text) -> text:
        return ctor(name)

    fn make_tagged(name: text) -> text:
        return "tagged:{name}"

    expect(build_with_factory("item", make_tagged)).to_equal("tagged:item")
```

### Constructor Polymorphism (Line ~162)

Use traits to define abstract constructor requirements:

```simple
it "constructor_polymorphism_23":
    fn create_named(name: text) -> text:
        return "created:{name}"

    fn make<T>(name: text, ctor: fn(text) -> T) -> T:
        return ctor(name)

    expect(make("Widget", create_named)).to_equal("created:Widget")
```

### Semantic Types in Function Signatures (Line ~5)

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

## Scenarios

#### functions_1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(add(2, 3)).to_equal(5)
```

</details>

#### functions_2

1. fn double
2. fn fetch user
3. fn compute
4. fn load data
   - Expected: double(4) equals `8`
   - Expected: fetch_user(10) equals `11`
   - Expected: compute(5) equals `25`
   - Expected: load_data() equals `loaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### functions_3

1. fn apply
   - Expected: result equals `5`
   - Expected: apply(add, 10, 20) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val math_op = add
val result = math_op(2, 3)

fn apply(f: fn(i64, i64) -> i64, x: i64, y: i64) -> i64:
    return f(x, y)

expect(result).to_equal(5)
expect(apply(add, 10, 20)).to_equal(30)
```

</details>

#### lambdas_and_closures_4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val square = _1 * _1
val double = _1 * 2

expect(square(5)).to_equal(25)
expect(double(7)).to_equal(14)
```

</details>

#### lambdas_and_closures_5

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \a, b: a + b
val sum = add(3, 4)

expect(sum).to_equal(7)
```

</details>

#### lambdas_and_closures_6

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiplier = 3
val scale = _1 * multiplier

expect(scale(10)).to_equal(30)
```

</details>

#### lambdas_and_closures_7

1. fn sum with
2. total = total + transform
   - Expected: total equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_with(items: [i64], transform: fn(i64) -> i64) -> i64:
    var total = 0
    for item in items:
        total = total + transform(item)
    return total

val numbers = [1, 2, 3]
val total = sum_with(numbers, _1 * 2)

expect(total).to_equal(12)
```

</details>

#### pattern_matching_8

1. Number
2. fn describe token
   - Expected: describe_token(Token.Number(5)) equals `Number(5)`
   - Expected: describe_token(Token.Plus) equals `Plus sign`
   - Expected: describe_token(Token.Minus) equals `Minus sign`
   - Expected: describe_token(Token.EOF) equals `End of input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Token:
    Number(value: i64)
    Plus
    Minus
    EOF

fn describe_token(tok: Token) -> text:
    match tok:
        case Number(n):
            return "Number({n})"
        case Plus:
            return "Plus sign"
        case Minus:
            return "Minus sign"
        case EOF:
            return "End of input"

expect(describe_token(Token.Number(5))).to_equal("Number(5)")
expect(describe_token(Token.Plus)).to_equal("Plus sign")
expect(describe_token(Token.Minus)).to_equal("Minus sign")
expect(describe_token(Token.EOF)).to_equal("End of input")
```

</details>

#### pattern_matching_9

1. fn describe number
   - Expected: describe_number(0) equals `Zero`
   - Expected: describe_number(1) equals `One`
   - Expected: describe_number(2) equals `Other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### pattern_matching_10

1. fn classify small number
   - Expected: classify_small_number(1) equals `One`
   - Expected: classify_small_number(4) equals `Other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### pattern_matching_11

1. fn classify guard like
   - Expected: classify_guard_like(-1) equals `Negative number`
   - Expected: classify_guard_like(101) equals `Large number`
   - Expected: classify_guard_like(42) equals `In range`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### pattern_matching_12

1. fn classify non zero
   - Expected: classify_non_zero(0) equals `Zero`
   - Expected: classify_non_zero(5) equals `Non-zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify_non_zero(x: i64) -> text:
    match x:
        0:
            return "Zero"
        _:
            return "Non-zero"

expect(classify_non_zero(0)).to_equal("Zero")
expect(classify_non_zero(5)).to_equal("Non-zero")
```

</details>

#### pattern_matching_13

1. fn describe point
   - Expected: describe_point(Point(x: 0, y: 0)) equals `Origin`
   - Expected: describe_point(point) equals `On X axis at 5`
   - Expected: describe_point(Point(x: 0, y: 8)) equals `On Y axis at 8`
   - Expected: describe_point(Point(x: 2, y: 3)) equals `Somewhere else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### pattern_matching_14

1. fn describe pair
   - Expected: describe_pair(pair) equals `Number 1 with string 'hello'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (1, "hello")

fn describe_pair(p: (i64, text)) -> text:
    match p:
        case (0, _):
            return "Starts with zero"
        case (n, s):
            return "Number {n} with string '{s}'"

expect(describe_pair(pair)).to_equal("Number 1 with string 'hello'")
```

</details>

#### pattern_matching_15

1. fn describe color
   - Expected: describe_color(Color.Red) equals `red`
   - Expected: describe_color(Color.Green) equals `green`
   - Expected: describe_color(Color.Blue) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

expect(describe_color(Color.Red)).to_equal("red")
expect(describe_color(Color.Green)).to_equal("green")
expect(describe_color(Color.Blue)).to_equal("blue")
```

</details>

#### constructor_polymorphism_16

1. fn make widget
   - Expected: widget.name equals `Button`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Widget:
    name: text

fn make_widget(name: text) -> Widget:
    return Widget(name: name)

val widget = make_widget("Button")
expect(widget.name).to_equal("Button")
```

</details>

#### constructor_polymorphism_17

1. fn make button
   - Expected: button.name equals `Submit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Button:
    name: text

fn make_button(name: text) -> Button:
    return Button(name: name)

val button = make_button("Submit")
expect(button.name).to_equal("Submit")
```

</details>

#### constructor_polymorphism_18

1. fn build label
   - Expected: build_label("base", 10, false) equals `base:10`
   - Expected: build_label("base", 10, true) equals `base:10:extra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn build_label(name: text, value: i64, extra: bool) -> text:
    if extra:
        return "{name}:{value}:extra"
    return "{name}:{value}"

expect(build_label("base", 10, false)).to_equal("base:10")
expect(build_label("base", 10, true)).to_equal("base:10:extra")
```

</details>

#### constructor_polymorphism_19

1. fn create many
2. result = result + [ctor
3. fn decorate button
   - Expected: buttons.len() equals `3`
   - Expected: buttons[0] equals `button:OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### constructor_polymorphism_20

1. fn choose widget
   - Expected: choose_widget("button", "Dynamic Button") equals `button:Dynamic Button`
   - Expected: choose_widget("label", "Status") equals `label:Status`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

#### constructor_polymorphism_22

1. fn build with factory
2. fn make tagged
   - Expected: build_with_factory("item", make_tagged) equals `tagged:item`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn build_with_factory(name: text, ctor: fn(text) -> text) -> text:
    return ctor(name)

fn make_tagged(name: text) -> text:
    return "tagged:{name}"

expect(build_with_factory("item", make_tagged)).to_equal("tagged:item")
```

</details>

#### constructor_polymorphism_23

1. fn create named
2. fn make<T>
   - Expected: make("Widget", create_named) equals `created:Widget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_named(name: text) -> text:
    return "created:{name}"

fn make<T>(name: text, ctor: fn(text) -> T) -> T:
    return ctor(name)

expect(make("Widget", create_named)).to_equal("created:Widget")
```

</details>

#### semantic_types_in_function_signatures_24

1. pub fn get user id
2. pub fn set status
3. pub fn find user
   - Expected: user_id.value equals `42`
   - Expected: set_status(Active) equals `active`
   - Expected: set_status(Disabled) equals `disabled`
   - Expected: user.status equals `Active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

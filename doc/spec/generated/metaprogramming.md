# Simple Language Metaprogramming - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/metaprogramming_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/metaprogramming_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** metaprogramming.md
**Note:** This is a test extraction file. For complete specification text,

## Overview

This file contains executable test cases extracted from metaprogramming.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/metaprogramming.md

---

## Test Cases (24 total)

| Test | Section | Description |
|------|---------|-------------|
| [dsl_features_1](#test-1) | DSL Features | A context block changes the method lookup context for a sect... |
| [dsl_features_2](#test-2) | DSL Features | If an object receives a call for a method it doesn't have, i... |
| [decorators_and_attributes_3](#test-3) | Decorators and Attributes | Decorators are functions that transform other functions at c... |
| [decorators_and_attributes_4](#test-4) | Decorators and Attributes | Attributes are passive metadata: |
| [decorators_and_attributes_5](#test-5) | Decorators and Attributes | The `#[allow(...)]` and `#[deny(...)]` attributes control co... |
| [comprehensions_6](#test-6) | Comprehensions | Simple supports Python-style comprehensions for concise coll... |
| [comprehensions_7](#test-7) | Comprehensions | ```simple # Basic let squares = [x * x for x in 0..10] |
| [slicing_and_indexing_8](#test-8) | Slicing and Indexing |  |
| [slicing_and_indexing_9](#test-9) | Slicing and Indexing | ```simple... |
| [slicing_and_indexing_10](#test-10) | Slicing and Indexing | items[2:5]      # [2, 3, 4]... |
| [slicing_and_indexing_11](#test-11) | Slicing and Indexing | let first, *rest = [1, 2, 3, 4, 5]... |
| [enhanced_pattern_matching_12](#test-12) | Enhanced Pattern Matching | Enhanced Pattern Matching |
| [enhanced_pattern_matching_13](#test-13) | Enhanced Pattern Matching | ```simple... |
| [enhanced_pattern_matching_14](#test-14) | Enhanced Pattern Matching | ```simple... |
| [enhanced_pattern_matching_15](#test-15) | Enhanced Pattern Matching | ```simple... |
| [enhanced_pattern_matching_16](#test-16) | Enhanced Pattern Matching | The `while with` construct combines a `while` loop condition... |
| [enhanced_pattern_matching_17](#test-17) | Enhanced Pattern Matching | Comparison with nested `while`/`with`: |
| [enhanced_pattern_matching_18](#test-18) | Enhanced Pattern Matching | Implementation Note: The context manager must implement `Con... |
| [context_managers_19](#test-19) | Context Managers | Context managers ensure proper resource cleanup: |
| [context_managers_20](#test-20) | Context Managers | with open("in.txt") as input, open("out.txt", "w") as output... |
| [create_counter](#test-21) | Move Closures | By default, closures capture variables by reference. Use `mo... |
| [move_closures_22](#test-22) | Move Closures | Move closures are essential for:... |
| [error_handling_23](#test-23) | Error Handling | Simple uses explicit error handling with Result types and th... |
| [process_file](#test-24) | Error Handling | fn divide(a: i64, b: i64) -> Result[i64, str]:... |

---

### Test 1: DSL Features

*Source line: ~9*

**Test name:** `dsl_features_1`

**Description:**

A context block changes the method lookup context for a section of code:

**Code:**

```simple
test "dsl_features_1":
    class HTMLBuilder:
        fn tag(name: String, content: String):
            print "<{name}>{content}</{name}>"

        fn method_missing(meth: Symbol, args: [Any], block: Fn):
            let tag_name = meth.name
            if block != nil:
                print "<{tag_name}>"
                block()
                print "</{tag_name}>"
            else:
                let content = args.size > 0 ? args[0] : ""
                print "<{tag_name}>{content}</{tag_name}>"

    let html = HTMLBuilder()
    context html:
        tag("h1", "Welcome")
        p "This is a DSL example."
        div:
            p "Inside a div."
            span "Nice!"
    assert_compiles()
```

### Test 2: DSL Features

*Source line: ~39*

**Test name:** `dsl_features_2`

**Description:**

If an object receives a call for a method it doesn't have, it can override `method_missing`:

**Code:**

```simple
test "dsl_features_2":
    class ConfigDSL:
        data: Map[String, String] = {}

        fn method_missing(key: Symbol, args: [Any], block: Fn):
            if args.size == 1:
                data[key.name] = toString(args[0])
            elif args.size == 0 and block != nil:
                block()

    let config = ConfigDSL()
    context config:
        database "postgres"
        host "localhost"
        port 5432
    assert_compiles()
```

### Test 3: Decorators and Attributes

*Source line: ~7*

**Test name:** `decorators_and_attributes_3`

**Description:**

Decorators are functions that transform other functions at compile time:

**Code:**

```simple
test "decorators_and_attributes_3":
    @cached
    fn expensive_calculation(x: i64) -> i64:
        return result

    @logged
    @retry(attempts: 3)
    fn fetch_data(url: str) -> Data:
        return http_get(url)

    @timeout(seconds: 30)
    fn slow_operation():
        # ...
    assert_compiles()
```

### Test 4: Decorators and Attributes

*Source line: ~35*

**Test name:** `decorators_and_attributes_4`

**Description:**

Attributes are passive metadata:

**Code:**

```simple
test "decorators_and_attributes_4":
    #[inline]
    fn hot_path(x: i64) -> i64:
        return x * 2

    #[deprecated(since: "0.2", reason: "Use new_api instead")]
    fn old_api():
        # ...

    #[derive(Debug, Clone, Eq)]
    struct Point:
        x: f64
        y: f64

    #[test]
    fn test_addition():
        assert_eq(1 + 1, 2)
    assert_compiles()
```

### Test 5: Decorators and Attributes

*Source line: ~69*

**Test name:** `decorators_and_attributes_5`

**Description:**

The `#[allow(...)]` and `#[deny(...)]` attributes control compiler lint behavior:

**Code:**

```simple
test "decorators_and_attributes_5":
    # Directory-level (in __init__.spl, inherits to all children)
    #[deny(primitive_api)]
    mod my_strict_module

    # Item-level
    #[allow(primitive_api)]
    pub fn low_level_function(x: i64) -> i64:   # No warning
        ...

    #[deny(primitive_api)]
    pub fn strict_function(x: i64) -> i64:      # Error
        ...
    assert_compiles()
```

### Test 6: Comprehensions

*Source line: ~7*

**Test name:** `comprehensions_6`

**Description:**

Simple supports Python-style comprehensions for concise collection construction.

**Code:**

```simple
test "comprehensions_6":
    # Basic
    let squares = [x * x for x in 0..10]

    # With filter
    let evens = [x for x in 0..20 if x % 2 == 0]

    # Nested
    let pairs = [(x, y) for x in 0..3 for y in 0..3]

    # Complex
    let names = [user.name.upper() for user in users if user.active]
    assert_compiles()
```

### Test 7: Comprehensions

*Source line: ~23*

**Test name:** `comprehensions_7`

**Description:**

```simple
# Basic
let squares = [x * x for x in 0..10]

**Code:**

```simple
test "comprehensions_7":
    let squares = {x: x * x for x in 0..10}
    let active_users = {u.id: u for u in users if u.active}
    let inverted = {v: k for k, v in original}
    assert_compiles()
```

### Test 8: Slicing and Indexing

*Source line: ~5*

**Test name:** `slicing_and_indexing_8`

**Code:**

```simple
test "slicing_and_indexing_8":
    let items = [1, 2, 3, 4, 5]
    items[-1]     # 5 (last element)
    items[-2]     # 4 (second to last)
    assert_compiles()
```

### Test 9: Slicing and Indexing

*Source line: ~13*

**Test name:** `slicing_and_indexing_9`

**Description:**

```simple
let items = [1, 2, 3, 4, 5]
items[-1]     # 5 (last element)
items[-2]     # 4 (second to ...

**Code:**

```simple
test "slicing_and_indexing_9":
    let items = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

    items[2:5]      # [2, 3, 4]
    items[:3]       # [0, 1, 2]
    items[7:]       # [7, 8, 9]
    items[::2]      # [0, 2, 4, 6, 8]
    items[::-1]     # [9, 8, ..., 0] (reversed)
    items[-3:]      # [7, 8, 9] (last 3)
    assert_compiles()
```

### Test 10: Slicing and Indexing

*Source line: ~26*

**Test name:** `slicing_and_indexing_10`

**Description:**

items[2:5]      # [2, 3, 4]
items[:3]       # [0, 1, 2]
items[7:]       # [7, 8, 9]
items[::2]      ...

**Code:**

```simple
test "slicing_and_indexing_10":
    let a, b = (1, 2)
    a, b = b, a           # Swap

    let first, *rest = [1, 2, 3, 4, 5]
    # first = 1, rest = [2, 3, 4, 5]
    assert_compiles()
```

### Test 11: Slicing and Indexing

*Source line: ~36*

**Test name:** `slicing_and_indexing_11`

**Description:**

let first, *rest = [1, 2, 3, 4, 5]
# first = 1, rest = [2, 3, 4, 5]
```

**Code:**

```simple
test "slicing_and_indexing_11":
    let a = [1, 2, 3]
    let b = [4, 5, 6]
    let combined = [*a, *b]        # [1, 2, 3, 4, 5, 6]

    let d1 = {"a": 1}
    let d2 = {"b": 2}
    let merged = {**d1, **d2}      # {"a": 1, "b": 2}
    assert_compiles()
```

### Test 12: Enhanced Pattern Matching

*Source line: ~5*

**Test name:** `enhanced_pattern_matching_12`

**Description:**

Enhanced Pattern Matching

**Code:**

```simple
test "enhanced_pattern_matching_12":
    match value:
        case x if x > 0:
            print "positive"
        case x if x < 0:
            print "negative"
        case 0:
            print "zero"
    assert_compiles()
```

### Test 13: Enhanced Pattern Matching

*Source line: ~17*

**Test name:** `enhanced_pattern_matching_13`

**Description:**

```simple
match value:
    case x if x > 0:
        print "positive"
    case x if x < 0:
        pr...

**Code:**

```simple
test "enhanced_pattern_matching_13":
    match command:
        case "quit" | "exit" | "q":
            shutdown()
        case "help" | "h" | "?":
            show_help()
    assert_compiles()
```

### Test 14: Enhanced Pattern Matching

*Source line: ~27*

**Test name:** `enhanced_pattern_matching_14`

**Description:**

```simple
match command:
    case "quit" | "exit" | "q":
        shutdown()
    case "help" | "h" | ...

**Code:**

```simple
test "enhanced_pattern_matching_14":
    match score:
        case 90..100: "A"
        case 80..90: "B"
        case 70..80: "C"
        case _: "F"
    assert_compiles()
```

### Test 15: Enhanced Pattern Matching

*Source line: ~37*

**Test name:** `enhanced_pattern_matching_15`

**Description:**

```simple
match score:
    case 90..100: "A"
    case 80..90: "B"
    case 70..80: "C"
    case _: "...

**Code:**

```simple
test "enhanced_pattern_matching_15":
    if let Some(value) = optional:
        print "got {value}"

    while let Some(item) = iterator.next():
        process(item)
    assert_compiles()
```

### Test 16: Enhanced Pattern Matching

*Source line: ~49*

**Test name:** `enhanced_pattern_matching_16`

**Description:**

The `while with` construct combines a `while` loop condition with a context manager, useful for rend...

**Code:**

```simple
test "enhanced_pattern_matching_16":
    # Render loop: continues while window is open, frame context managed per iteration
    while with window.frame() as frame:
        frame.clear([0.0, 0.0, 0.0, 1.0])
        frame.draw(pipeline, vertices)
    # Window closed, loop exits

    # Streaming: continues while data available
    while with stream.next_chunk() as chunk:
        process(chunk)
    # Stream exhausted
    assert_compiles()
```

### Test 17: Enhanced Pattern Matching

*Source line: ~78*

**Test name:** `enhanced_pattern_matching_17`

**Description:**

Comparison with nested `while`/`with`:

**Code:**

```simple
test "enhanced_pattern_matching_17":
    # Traditional nested approach
    while !window.should_close():
        with window.frame() as frame:
            frame.draw(...)

    # Unified while-with approach (condition implied by context manager)
    while with window.frame() as frame:
        frame.draw(...)
    assert_compiles()
```

### Test 18: Enhanced Pattern Matching

*Source line: ~98*

**Test name:** `enhanced_pattern_matching_18`

**Description:**

Implementation Note: The context manager must implement `ContextManager` trait and optionally return...

**Code:**

```simple
test "enhanced_pattern_matching_18":
    if 0 < x < 10:
        print "single digit"
    assert_compiles()
```

### Test 19: Context Managers

*Source line: ~5*

**Test name:** `context_managers_19`

**Description:**

Context managers ensure proper resource cleanup:

**Code:**

```simple
test "context_managers_19":
    with open("file.txt") as file:
        let content = file.read()
    # file is automatically closed

    with open("in.txt") as input, open("out.txt", "w") as output:
        output.write(transform(input.read()))
    assert_compiles()
```

### Test 20: Context Managers

*Source line: ~16*

**Test name:** `context_managers_20`

**Description:**

with open("in.txt") as input, open("out.txt", "w") as output:
    output.write(transform(input.read(...

**Code:**

```simple
test "context_managers_20":
    trait ContextManager:
        fn enter(self) -> Self
        fn exit(self, error: Error?)

    impl ContextManager for File:
        fn enter(self) -> File:
            return self

        fn exit(self, error: Error?):
            self.close()
    assert_compiles()
```

### Test 21: Move Closures

*Source line: ~5*

**Test name:** `create_counter`

**Description:**

By default, closures capture variables by reference. Use `move` to capture by value:

**Code:**

```simple
fn create_counter(start: i64) -> Fn() -> i64:
    let count = start
    return move \:
        count = count + 1
        count

let counter = create_counter(0)
counter()  # 1
counter()  # 2
```

### Test 22: Move Closures

*Source line: ~22*

**Test name:** `move_closures_22`

**Description:**

Move closures are essential for:
- Sending closures to other actors
- Storing closures that outlive ...

**Code:**

```simple
test "move_closures_22":
    actor.send(move \: process(captured_data))
    items.par_map(move \x: expensive_compute(x, config))
    assert_compiles()
```

### Test 23: Error Handling

*Source line: ~7*

**Test name:** `error_handling_23`

**Description:**

Simple uses explicit error handling with Result types and the `?` operator.

**Code:**

```simple
test "error_handling_23":
    enum Result[T, E]:
        Ok(value: T)
        Err(error: E)

    fn divide(a: i64, b: i64) -> Result[i64, str]:
        if b == 0:
            return Err("division by zero")
        return Ok(a / b)
    assert_compiles()
```

### Test 24: Error Handling

*Source line: ~20*

**Test name:** `process_file`

**Description:**

fn divide(a: i64, b: i64) -> Result[i64, str]:
    if b == 0:
        return Err("division by zero")...

**Code:**

```simple
fn process_file(path: str) -> Result[Data, Error]:
    let file = open(path)?           # Returns Err if open fails
    let content = file.read_all()?   # Returns Err if read fails
    let data = parse(content)?       # Returns Err if parse fails
    return Ok(data)
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/metaprogramming_spec.spl`*

# Simple Language Metaprogramming - Test Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/metaprogramming_spec.spl`
> **Generated:** 2026-01-09 06:15:42
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/metaprogramming_spec.spl
> ```

**Status:** Reference
**Feature IDs:** **Source:** metaprogramming.md
**Note:** This is a test extraction file. For complete specification text,

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (24 tests)
- [Source Code](#source-code)

## Overview

This file contains executable test cases extracted from metaprogramming.md.
The original specification file remains as architectural reference documentation.

**Note:** This is a test extraction file. For complete specification text,
design rationale, and architecture, see doc/spec/metaprogramming.md

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `And` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5), [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), ... (7 total) |
| `Any` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `Attributes` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `Basic` | [6](#comprehensions_6) |
| `Clone` | [4](#decorators_and_attributes_4) |
| `Closures` | [22](#move_closures_22) |
| `Complex` | [6](#comprehensions_6) |
| `Comprehensions` | [6](#comprehensions_6), [7](#comprehensions_7) |
| `ConfigDSL` | [2](#dsl_features_2) |
| `Context` | [19](#context_managers_19), [20](#context_managers_20) |
| `ContextManager` | [20](#context_managers_20) |
| `ContextManagers` | [19](#context_managers_19), [20](#context_managers_20) |
| `Counter` | [21](#create_counter) |
| `Create` | [21](#create_counter) |
| `CreateCounter` | [21](#create_counter) |
| `DSL` | [1](#dsl_features_1) |
| `Data` | [3](#decorators_and_attributes_3), [24](#process_file) |
| `Debug` | [4](#decorators_and_attributes_4) |
| `Decorators` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `DecoratorsAndAttributes` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `Directory` | [5](#decorators_and_attributes_5) |
| `Dsl` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `DslFeatures` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `Enhanced` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `EnhancedPatternMatching` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `Err` | [23](#error_handling_23), [24](#process_file) |
| `Error` | [5](#decorators_and_attributes_5), [20](#context_managers_20), [23](#error_handling_23), [24](#process_file) |
| `ErrorHandling` | [23](#error_handling_23) |
| `Features` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `File` | [20](#context_managers_20), [24](#process_file) |
| `HTMLBuilder` | [1](#dsl_features_1) |
| `Handling` | [23](#error_handling_23) |
| `Indexing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `Inside` | [1](#dsl_features_1) |
| `Item` | [5](#decorators_and_attributes_5) |
| `Managers` | [19](#context_managers_19), [20](#context_managers_20) |
| `Map` | [2](#dsl_features_2) |
| `Matching` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `Move` | [22](#move_closures_22) |
| `MoveClosures` | [22](#move_closures_22) |
| `Nested` | [6](#comprehensions_6) |
| `Nice` | [1](#dsl_features_1) |
| `Pattern` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `Point` | [4](#decorators_and_attributes_4) |
| `Process` | [24](#process_file) |
| `ProcessFile` | [24](#process_file) |
| `Render` | [16](#enhanced_pattern_matching_16) |
| `Result` | [23](#error_handling_23), [24](#process_file) |
| `Returns` | [24](#process_file) |
| `Self` | [20](#context_managers_20) |
| `Slicing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `SlicingAndIndexing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `Stream` | [16](#enhanced_pattern_matching_16) |
| `Streaming` | [16](#enhanced_pattern_matching_16) |
| `String` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `Swap` | [10](#slicing_and_indexing_10) |
| `Symbol` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `This` | [1](#dsl_features_1) |
| `Traditional` | [17](#enhanced_pattern_matching_17) |
| `Unified` | [17](#enhanced_pattern_matching_17) |
| `Use` | [4](#decorators_and_attributes_4) |
| `Welcome` | [1](#dsl_features_1) |
| `Window` | [16](#enhanced_pattern_matching_16) |
| `With` | [6](#comprehensions_6) |
| `allow` | [5](#decorators_and_attributes_5) |
| `and` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5), [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), ... (7 total) |
| `approach` | [17](#enhanced_pattern_matching_17) |
| `assert_compiles` | [1](#dsl_features_1), [2](#dsl_features_2), [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5), ... (22 total) |
| `assert_eq` | [4](#decorators_and_attributes_4) |
| `attributes` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `block` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `clear` | [16](#enhanced_pattern_matching_16) |
| `close` | [20](#context_managers_20) |
| `closures` | [22](#move_closures_22) |
| `comprehensions` | [6](#comprehensions_6), [7](#comprehensions_7) |
| `context` | [19](#context_managers_19), [20](#context_managers_20) |
| `context_managers` | [19](#context_managers_19), [20](#context_managers_20) |
| `counter` | [21](#create_counter) |
| `create` | [21](#create_counter) |
| `create_counter` | [21](#create_counter) |
| `decorators` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `decorators_and_attributes` | [3](#decorators_and_attributes_3), [4](#decorators_and_attributes_4), [5](#decorators_and_attributes_5) |
| `deny` | [5](#decorators_and_attributes_5) |
| `deprecated` | [4](#decorators_and_attributes_4) |
| `derive` | [4](#decorators_and_attributes_4) |
| `divide` | [23](#error_handling_23) |
| `draw` | [16](#enhanced_pattern_matching_16), [17](#enhanced_pattern_matching_17) |
| `dsl` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `dsl_features` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `enhanced` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `enhanced_pattern_matching` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `enter` | [20](#context_managers_20) |
| `error` | [23](#error_handling_23) |
| `error_handling` | [23](#error_handling_23) |
| `exit` | [20](#context_managers_20) |
| `expensive_calculation` | [3](#decorators_and_attributes_3) |
| `expensive_compute` | [22](#move_closures_22) |
| `features` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `fetch_data` | [3](#decorators_and_attributes_3) |
| `file` | [24](#process_file) |
| `frame` | [16](#enhanced_pattern_matching_16), [17](#enhanced_pattern_matching_17) |
| `handling` | [23](#error_handling_23) |
| `hot_path` | [4](#decorators_and_attributes_4) |
| `http_get` | [3](#decorators_and_attributes_3) |
| `indexing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `level` | [5](#decorators_and_attributes_5) |
| `low_level_function` | [5](#decorators_and_attributes_5) |
| `managers` | [19](#context_managers_19), [20](#context_managers_20) |
| `matching` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `method_missing` | [1](#dsl_features_1), [2](#dsl_features_2) |
| `move` | [22](#move_closures_22) |
| `move_closures` | [22](#move_closures_22) |
| `next` | [15](#enhanced_pattern_matching_15) |
| `next_chunk` | [16](#enhanced_pattern_matching_16) |
| `old_api` | [4](#decorators_and_attributes_4) |
| `open` | [19](#context_managers_19), [24](#process_file) |
| `par_map` | [22](#move_closures_22) |
| `parse` | [24](#process_file) |
| `pattern` | [12](#enhanced_pattern_matching_12), [13](#enhanced_pattern_matching_13), [14](#enhanced_pattern_matching_14), [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), ... (7 total) |
| `process` | [15](#enhanced_pattern_matching_15), [16](#enhanced_pattern_matching_16), [22](#move_closures_22), [24](#process_file) |
| `process_file` | [24](#process_file) |
| `read` | [19](#context_managers_19) |
| `read_all` | [24](#process_file) |
| `retry` | [3](#decorators_and_attributes_3) |
| `send` | [22](#move_closures_22) |
| `should_close` | [17](#enhanced_pattern_matching_17) |
| `show_help` | [13](#enhanced_pattern_matching_13) |
| `shutdown` | [13](#enhanced_pattern_matching_13) |
| `slicing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `slicing_and_indexing` | [8](#slicing_and_indexing_8), [9](#slicing_and_indexing_9), [10](#slicing_and_indexing_10), [11](#slicing_and_indexing_11) |
| `slow_operation` | [3](#decorators_and_attributes_3) |
| `strict_function` | [5](#decorators_and_attributes_5) |
| `tag` | [1](#dsl_features_1) |
| `test_addition` | [4](#decorators_and_attributes_4) |
| `timeout` | [3](#decorators_and_attributes_3) |
| `transform` | [19](#context_managers_19) |
| `upper` | [6](#comprehensions_6) |
| `write` | [19](#context_managers_19) |

---

## Test Cases (24 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [dsl_features_1](#dsl_features_1) | DSL Features | `features`, `dsl_features`, `DslFeatures` +16 |
| 2 | [dsl_features_2](#dsl_features_2) | DSL Features | `features`, `dsl_features`, `DslFeatures` +11 |
| 3 | [decorators_and_attributes_3](#decorators_and_attributes_3) | Decorators and Attributes | `decorators`, `DecoratorsAndAttributes`, `attributes` +13 |
| 4 | [decorators_and_attributes_4](#decorators_and_attributes_4) | Decorators and Attributes | `decorators`, `DecoratorsAndAttributes`, `attributes` +16 |
| 5 | [decorators_and_attributes_5](#decorators_and_attributes_5) | Decorators and Attributes | `decorators`, `DecoratorsAndAttributes`, `attributes` +14 |
| 6 | [comprehensions_6](#comprehensions_6) | Comprehensions | `comprehensions`, `Comprehensions`, `assert_compiles` +5 |
| 7 | [comprehensions_7](#comprehensions_7) | Comprehensions | `comprehensions`, `Comprehensions`, `assert_compiles` |
| 8 | [slicing_and_indexing_8](#slicing_and_indexing_8) | Slicing and Indexing | `slicing_and_indexing`, `slicing`, `Slicing` +6 |
| 9 | [slicing_and_indexing_9](#slicing_and_indexing_9) | Slicing and Indexing | `slicing_and_indexing`, `slicing`, `Slicing` +6 |
| 10 | [slicing_and_indexing_10](#slicing_and_indexing_10) | Slicing and Indexing | `slicing_and_indexing`, `slicing`, `Slicing` +7 |
| 11 | [slicing_and_indexing_11](#slicing_and_indexing_11) | Slicing and Indexing | `slicing_and_indexing`, `slicing`, `Slicing` +6 |
| 12 | [enhanced_pattern_matching_12](#enhanced_pattern_matching_12) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +6 |
| 13 | [enhanced_pattern_matching_13](#enhanced_pattern_matching_13) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +8 |
| 14 | [enhanced_pattern_matching_14](#enhanced_pattern_matching_14) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +6 |
| 15 | [enhanced_pattern_matching_15](#enhanced_pattern_matching_15) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +8 |
| 16 | [enhanced_pattern_matching_16](#enhanced_pattern_matching_16) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +15 |
| 17 | [enhanced_pattern_matching_17](#enhanced_pattern_matching_17) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +12 |
| 18 | [enhanced_pattern_matching_18](#enhanced_pattern_matching_18) | Enhanced Pattern Matching | `enhanced_pattern_matching`, `pattern`, `Enhanced` +6 |
| 19 | [context_managers_19](#context_managers_19) | Context Managers | `context`, `context_managers`, `Managers` +8 |
| 20 | [context_managers_20](#context_managers_20) | Context Managers | `context`, `context_managers`, `Managers` +11 |
| 21 | [create_counter](#create_counter) | Move Closures | `create`, `Create`, `counter` +3 |
| 22 | [move_closures_22](#move_closures_22) | Move Closures | `move`, `Closures`, `move_closures` +8 |
| 23 | [error_handling_23](#error_handling_23) | Error Handling | `error`, `ErrorHandling`, `Handling` +7 |
| 24 | [process_file](#process_file) | Error Handling | `file`, `File`, `process` +11 |

---

### Test 1: DSL Features {#dsl_features_1}

*Source line: ~9*

**Test name:** `dsl_features_1`

**Description:**

A context block changes the method lookup context for a section of code:

**Linked Symbols:**
- `features`
- `dsl_features`
- `DslFeatures`
- `Features`
- `Dsl`
- `dsl`
- `assert_compiles`
- `String`
- `method_missing`
- `Welcome`
- ... and 9 more

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

### Test 2: DSL Features {#dsl_features_2}

*Source line: ~39*

**Test name:** `dsl_features_2`

**Description:**

If an object receives a call for a method it doesn't have, it can override `method_missing`:

**Linked Symbols:**
- `features`
- `dsl_features`
- `DslFeatures`
- `Features`
- `Dsl`
- `dsl`
- `assert_compiles`
- `String`
- `method_missing`
- `Map`
- ... and 4 more

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

### Test 3: Decorators and Attributes {#decorators_and_attributes_3}

*Source line: ~7*

**Test name:** `decorators_and_attributes_3`

**Description:**

Decorators are functions that transform other functions at compile time:

**Linked Symbols:**
- `decorators`
- `DecoratorsAndAttributes`
- `attributes`
- `and`
- `decorators_and_attributes`
- `Decorators`
- `Attributes`
- `And`
- `assert_compiles`
- `slow_operation`
- ... and 6 more

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

### Test 4: Decorators and Attributes {#decorators_and_attributes_4}

*Source line: ~35*

**Test name:** `decorators_and_attributes_4`

**Description:**

Attributes are passive metadata:

**Linked Symbols:**
- `decorators`
- `DecoratorsAndAttributes`
- `attributes`
- `and`
- `decorators_and_attributes`
- `Decorators`
- `Attributes`
- `And`
- `old_api`
- `assert_compiles`
- ... and 9 more

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

### Test 5: Decorators and Attributes {#decorators_and_attributes_5}

*Source line: ~69*

**Test name:** `decorators_and_attributes_5`

**Description:**

The `#[allow(...)]` and `#[deny(...)]` attributes control compiler lint behavior:

**Linked Symbols:**
- `decorators`
- `DecoratorsAndAttributes`
- `attributes`
- `and`
- `decorators_and_attributes`
- `Decorators`
- `Attributes`
- `And`
- `assert_compiles`
- `low_level_function`
- ... and 7 more

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

### Test 6: Comprehensions {#comprehensions_6}

*Source line: ~7*

**Test name:** `comprehensions_6`

**Description:**

Simple supports Python-style comprehensions for concise collection construction.

**Linked Symbols:**
- `comprehensions`
- `Comprehensions`
- `assert_compiles`
- `Nested`
- `upper`
- `Complex`
- `With`
- `Basic`

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

### Test 7: Comprehensions {#comprehensions_7}

*Source line: ~23*

**Test name:** `comprehensions_7`

**Description:**

```simple
# Basic
let squares = [x * x for x in 0..10]

**Linked Symbols:**
- `comprehensions`
- `Comprehensions`
- `assert_compiles`

**Code:**

```simple
test "comprehensions_7":
    let squares = {x: x * x for x in 0..10}
    let active_users = {u.id: u for u in users if u.active}
    let inverted = {v: k for k, v in original}
    assert_compiles()
```

### Test 8: Slicing and Indexing {#slicing_and_indexing_8}

*Source line: ~5*

**Test name:** `slicing_and_indexing_8`

**Linked Symbols:**
- `slicing_and_indexing`
- `slicing`
- `Slicing`
- `Indexing`
- `indexing`
- `and`
- `SlicingAndIndexing`
- `And`
- `assert_compiles`

**Code:**

```simple
test "slicing_and_indexing_8":
    let items = [1, 2, 3, 4, 5]
    items[-1]     # 5 (last element)
    items[-2]     # 4 (second to last)
    assert_compiles()
```

### Test 9: Slicing and Indexing {#slicing_and_indexing_9}

*Source line: ~13*

**Test name:** `slicing_and_indexing_9`

**Description:**

```simple
let items = [1, 2, 3, 4, 5]
items[-1]     # 5 (last element)
items[-2]     # 4 (second to ...

**Linked Symbols:**
- `slicing_and_indexing`
- `slicing`
- `Slicing`
- `Indexing`
- `indexing`
- `and`
- `SlicingAndIndexing`
- `And`
- `assert_compiles`

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

### Test 10: Slicing and Indexing {#slicing_and_indexing_10}

*Source line: ~26*

**Test name:** `slicing_and_indexing_10`

**Description:**

items[2:5]      # [2, 3, 4]
items[:3]       # [0, 1, 2]
items[7:]       # [7, 8, 9]
items[::2]      ...

**Linked Symbols:**
- `slicing_and_indexing`
- `slicing`
- `Slicing`
- `Indexing`
- `indexing`
- `and`
- `SlicingAndIndexing`
- `And`
- `assert_compiles`
- `Swap`

**Code:**

```simple
test "slicing_and_indexing_10":
    let a, b = (1, 2)
    a, b = b, a           # Swap

    let first, *rest = [1, 2, 3, 4, 5]
    # first = 1, rest = [2, 3, 4, 5]
    assert_compiles()
```

### Test 11: Slicing and Indexing {#slicing_and_indexing_11}

*Source line: ~36*

**Test name:** `slicing_and_indexing_11`

**Description:**

let first, *rest = [1, 2, 3, 4, 5]
# first = 1, rest = [2, 3, 4, 5]
```

**Linked Symbols:**
- `slicing_and_indexing`
- `slicing`
- `Slicing`
- `Indexing`
- `indexing`
- `and`
- `SlicingAndIndexing`
- `And`
- `assert_compiles`

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

### Test 12: Enhanced Pattern Matching {#enhanced_pattern_matching_12}

*Source line: ~5*

**Test name:** `enhanced_pattern_matching_12`

**Description:**

Enhanced Pattern Matching

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`

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

### Test 13: Enhanced Pattern Matching {#enhanced_pattern_matching_13}

*Source line: ~17*

**Test name:** `enhanced_pattern_matching_13`

**Description:**

```simple
match value:
    case x if x > 0:
        print "positive"
    case x if x < 0:
        pr...

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`
- `shutdown`
- ... and 1 more

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

### Test 14: Enhanced Pattern Matching {#enhanced_pattern_matching_14}

*Source line: ~27*

**Test name:** `enhanced_pattern_matching_14`

**Description:**

```simple
match command:
    case "quit" | "exit" | "q":
        shutdown()
    case "help" | "h" | ...

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`

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

### Test 15: Enhanced Pattern Matching {#enhanced_pattern_matching_15}

*Source line: ~37*

**Test name:** `enhanced_pattern_matching_15`

**Description:**

```simple
match score:
    case 90..100: "A"
    case 80..90: "B"
    case 70..80: "C"
    case _: "...

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `next`
- `assert_compiles`
- ... and 1 more

**Code:**

```simple
test "enhanced_pattern_matching_15":
    if let Some(value) = optional:
        print "got {value}"

    while let Some(item) = iterator.next():
        process(item)
    assert_compiles()
```

### Test 16: Enhanced Pattern Matching {#enhanced_pattern_matching_16}

*Source line: ~49*

**Test name:** `enhanced_pattern_matching_16`

**Description:**

The `while with` construct combines a `while` loop condition with a context manager, useful for rend...

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`
- `process`
- ... and 8 more

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

### Test 17: Enhanced Pattern Matching {#enhanced_pattern_matching_17}

*Source line: ~78*

**Test name:** `enhanced_pattern_matching_17`

**Description:**

Comparison with nested `while`/`with`:

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`
- `should_close`
- ... and 5 more

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

### Test 18: Enhanced Pattern Matching {#enhanced_pattern_matching_18}

*Source line: ~98*

**Test name:** `enhanced_pattern_matching_18`

**Description:**

Implementation Note: The context manager must implement `ContextManager` trait and optionally return...

**Linked Symbols:**
- `enhanced_pattern_matching`
- `pattern`
- `Enhanced`
- `Pattern`
- `matching`
- `EnhancedPatternMatching`
- `enhanced`
- `Matching`
- `assert_compiles`

**Code:**

```simple
test "enhanced_pattern_matching_18":
    if 0 < x < 10:
        print "single digit"
    assert_compiles()
```

### Test 19: Context Managers {#context_managers_19}

*Source line: ~5*

**Test name:** `context_managers_19`

**Description:**

Context managers ensure proper resource cleanup:

**Linked Symbols:**
- `context`
- `context_managers`
- `Managers`
- `Context`
- `managers`
- `ContextManagers`
- `assert_compiles`
- `write`
- `read`
- `open`
- ... and 1 more

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

### Test 20: Context Managers {#context_managers_20}

*Source line: ~16*

**Test name:** `context_managers_20`

**Description:**

with open("in.txt") as input, open("out.txt", "w") as output:
    output.write(transform(input.read(...

**Linked Symbols:**
- `context`
- `context_managers`
- `Managers`
- `Context`
- `managers`
- `ContextManagers`
- `assert_compiles`
- `close`
- `File`
- `exit`
- ... and 4 more

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

### Test 21: Move Closures {#create_counter}

*Source line: ~5*

**Test name:** `create_counter`

**Description:**

By default, closures capture variables by reference. Use `move` to capture by value:

**Linked Symbols:**
- `create`
- `Create`
- `counter`
- `Counter`
- `CreateCounter`
- `create_counter`

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

### Test 22: Move Closures {#move_closures_22}

*Source line: ~22*

**Test name:** `move_closures_22`

**Description:**

Move closures are essential for:
- Sending closures to other actors
- Storing closures that outlive ...

**Linked Symbols:**
- `move`
- `Closures`
- `move_closures`
- `Move`
- `MoveClosures`
- `closures`
- `assert_compiles`
- `process`
- `expensive_compute`
- `par_map`
- ... and 1 more

**Code:**

```simple
test "move_closures_22":
    actor.send(move \: process(captured_data))
    items.par_map(move \x: expensive_compute(x, config))
    assert_compiles()
```

### Test 23: Error Handling {#error_handling_23}

*Source line: ~7*

**Test name:** `error_handling_23`

**Description:**

Simple uses explicit error handling with Result types and the `?` operator.

**Linked Symbols:**
- `error`
- `ErrorHandling`
- `Handling`
- `handling`
- `Error`
- `error_handling`
- `assert_compiles`
- `Err`
- `Result`
- `divide`

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

### Test 24: Error Handling {#process_file}

*Source line: ~20*

**Test name:** `process_file`

**Description:**

fn divide(a: i64, b: i64) -> Result[i64, str]:
    if b == 0:
        return Err("division by zero")...

**Linked Symbols:**
- `file`
- `File`
- `process`
- `process_file`
- `ProcessFile`
- `Process`
- `Returns`
- `Err`
- `Data`
- `read_all`
- ... and 4 more

**Code:**

```simple
fn process_file(path: str) -> Result[Data, Error]:
    let file = open(path)?           # Returns Err if open fails
    let content = file.read_all()?   # Returns Err if read fails
    let data = parse(content)?       # Returns Err if parse fails
    return Ok(data)
```

---

## Source Code

**View full specification:** [metaprogramming_spec.spl](../../tests/specs/metaprogramming_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/metaprogramming_spec.spl`*

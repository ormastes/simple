# Simple Language Syntax Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/syntax_spec.spl`
> **Generated:** 2026-01-09 06:23:37
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/syntax_spec.spl
> ```

**Status:** Stable
**Feature IDs:** #10-19
**Keywords:** syntax, lexical, operators, execution-modes, indentation
**Last Updated:** 2025-12-28
**Topics:** syntax, type-system
**Symbols:** Token, Operator, ExecutionMode, Parser, Lexer
**Module:** simple_parser

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (21 tests)
- [Source Code](#source-code)

## Overview

Comprehensive specification of Simple's syntax, execution modes, and lexical structure.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Async Default** - Execution mode semantics
- **Parser** - Parser implementation details

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Add` | [1](#add), [2](#add) |
| `Alice` | [20](#parsing_design_rationale_20) |
| `Backslashes` | [10](#string_literals_10) |
| `Binary` | [5](#literals_5) |
| `Braces` | [10](#string_literals_10) |
| `Clear` | [21](#parsing_design_rationale_21) |
| `Config` | [18](#functional_update_syntax___18) |
| `Count` | [9](#string_literals_9) |
| `Decimal` | [5](#literals_5) |
| `Design` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `Discard` | [14](#operators_14) |
| `ERROR` | [13](#string_literals_13) |
| `Error` | [20](#parsing_design_rationale_20) |
| `File` | [12](#string_literals_12) |
| `Functional` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `FunctionalUpdateSyntax` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `Hello` | [9](#string_literals_9), [11](#string_literals_11) |
| `Hexadecimal` | [5](#literals_5) |
| `HttpUrl` | [13](#string_literals_13) |
| `IDs` | [8](#literals_8) |
| `Invalid` | [20](#parsing_design_rationale_20) |
| `Item` | [4](#syntax_overview_4) |
| `Iterating` | [4](#syntax_overview_4) |
| `Literals` | [5](#literals_5), [6](#literals_6), [7](#literals_7), [8](#literals_8), [9](#string_literals_9), ... (9 total) |
| `Multiple` | [4](#syntax_overview_4), [21](#parsing_design_rationale_21) |
| `Network` | [12](#string_literals_12) |
| `Octal` | [5](#literals_5) |
| `Operators` | [14](#operators_14) |
| `OrderId` | [8](#literals_8) |
| `Overview` | [3](#syntax_overview_3), [4](#syntax_overview_4) |
| `Parser` | [19](#functional_update_syntax___19) |
| `Parsing` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `ParsingDesignRationale` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `Percentage` | [8](#literals_8) |
| `Percentages` | [8](#literals_8) |
| `Physical` | [8](#literals_8) |
| `RGB` | [5](#literals_5) |
| `Rationale` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `Result` | [9](#string_literals_9) |
| `Same` | [11](#string_literals_11) |
| `Semantic` | [8](#literals_8) |
| `Socket` | [12](#string_literals_12) |
| `String` | [9](#string_literals_9), [10](#string_literals_10), [11](#string_literals_11), [12](#string_literals_12), [13](#string_literals_13) |
| `StringLiterals` | [9](#string_literals_9), [10](#string_literals_10), [11](#string_literals_11), [12](#string_literals_12), [13](#string_literals_13) |
| `Suspending` | [14](#operators_14) |
| `Syntax` | [3](#syntax_overview_3), [4](#syntax_overview_4), [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), ... (7 total) |
| `SyntaxOverview` | [3](#syntax_overview_3), [4](#syntax_overview_4) |
| `URLs` | [12](#string_literals_12) |
| `Unix` | [5](#literals_5) |
| `Update` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `UserId` | [8](#literals_8) |
| `Users` | [10](#string_literals_10), [12](#string_literals_12) |
| `Valid` | [20](#parsing_design_rationale_20) |
| `add` | [1](#add), [2](#add) |
| `append` | [17](#functional_update_syntax___17) |
| `assert_compiles` | [3](#syntax_overview_3), [4](#syntax_overview_4), [5](#literals_5), [6](#literals_6), [7](#literals_7), ... (19 total) |
| `block` | [4](#syntax_overview_4) |
| `design` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `done` | [14](#operators_14) |
| `f32` | [7](#literals_7) |
| `f64` | [7](#literals_7) |
| `fetch_user` | [14](#operators_14) |
| `filter` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16) |
| `format` | [20](#parsing_design_rationale_20) |
| `from_str` | [13](#string_literals_13) |
| `functional` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `functional_update_syntax__` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `is_ready` | [14](#operators_14) |
| `literals` | [5](#literals_5), [6](#literals_6), [7](#literals_7), [8](#literals_8), [9](#string_literals_9), ... (9 total) |
| `load_data` | [15](#functional_update_syntax___15) |
| `new` | [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `normalize` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16) |
| `operators` | [14](#operators_14) |
| `overview` | [3](#syntax_overview_3), [4](#syntax_overview_4) |
| `parse_body` | [19](#functional_update_syntax___19) |
| `parsing` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `parsing_design_rationale` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `paths` | [12](#string_literals_12) |
| `proceed` | [14](#operators_14) |
| `rationale` | [20](#parsing_design_rationale_20), [21](#parsing_design_rationale_21) |
| `read_header` | [19](#functional_update_syntax___19) |
| `reverse` | [17](#functional_update_syntax___17) |
| `save` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16) |
| `set_host` | [18](#functional_update_syntax___18) |
| `set_port` | [18](#functional_update_syntax___18) |
| `set_timeout` | [18](#functional_update_syntax___18) |
| `sleep` | [14](#operators_14) |
| `sort` | [17](#functional_update_syntax___17) |
| `string` | [9](#string_literals_9), [10](#string_literals_10), [11](#string_literals_11), [12](#string_literals_12), [13](#string_literals_13) |
| `string_literals` | [9](#string_literals_9), [10](#string_literals_10), [11](#string_literals_11), [12](#string_literals_12), [13](#string_literals_13) |
| `syntax` | [3](#syntax_overview_3), [4](#syntax_overview_4), [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), ... (7 total) |
| `syntax_overview` | [3](#syntax_overview_3), [4](#syntax_overview_4) |
| `type` | [8](#literals_8) |
| `update` | [15](#functional_update_syntax___15), [16](#functional_update_syntax___16), [17](#functional_update_syntax___17), [18](#functional_update_syntax___18), [19](#functional_update_syntax___19) |
| `validate` | [19](#functional_update_syntax___19) |

---

## Test Cases (21 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [add](#add) | Execution Modes | `add`, `Add` |
| 2 | [add](#add) | Execution Modes | `add`, `Add` |
| 3 | [syntax_overview_3](#syntax_overview_3) | Syntax Overview | `Overview`, `syntax_overview`, `overview` +4 |
| 4 | [syntax_overview_4](#syntax_overview_4) | Syntax Overview | `Overview`, `syntax_overview`, `overview` +8 |
| 5 | [literals_5](#literals_5) | Literals | `literals`, `Literals`, `assert_compiles` +6 |
| 6 | [literals_6](#literals_6) | Literals | `literals`, `Literals`, `assert_compiles` |
| 7 | [literals_7](#literals_7) | Literals | `literals`, `Literals`, `assert_compiles` +2 |
| 8 | [literals_8](#literals_8) | Literals | `literals`, `Literals`, `assert_compiles` +8 |
| 9 | [string_literals_9](#string_literals_9) | String Literals | `String`, `literals`, `string` +7 |
| 10 | [string_literals_10](#string_literals_10) | String Literals | `String`, `literals`, `string` +7 |
| 11 | [string_literals_11](#string_literals_11) | String Literals | `String`, `literals`, `string` +6 |
| 12 | [string_literals_12](#string_literals_12) | String Literals | `String`, `literals`, `string` +10 |
| 13 | [string_literals_13](#string_literals_13) | String Literals | `String`, `literals`, `string` +7 |
| 14 | [operators_14](#operators_14) | Operators | `operators`, `Operators`, `assert_compiles` +7 |
| 15 | [functional_update_syntax___15](#functional_update_syntax___15) | Functional Update Syntax (`->`) | `update`, `functional_update_syntax__`, `Functional` +10 |
| 16 | [functional_update_syntax___16](#functional_update_syntax___16) | Functional Update Syntax (`->`) | `update`, `functional_update_syntax__`, `Functional` +9 |
| 17 | [functional_update_syntax___17](#functional_update_syntax___17) | Functional Update Syntax (`->`) | `update`, `functional_update_syntax__`, `Functional` +9 |
| 18 | [functional_update_syntax___18](#functional_update_syntax___18) | Functional Update Syntax (`->`) | `update`, `functional_update_syntax__`, `Functional` +11 |
| 19 | [functional_update_syntax___19](#functional_update_syntax___19) | Functional Update Syntax (`->`) | `update`, `functional_update_syntax__`, `Functional` +11 |
| 20 | [parsing_design_rationale_20](#parsing_design_rationale_20) | Parsing Design Rationale | `parsing_design_rationale`, `Parsing`, `Rationale` +11 |
| 21 | [parsing_design_rationale_21](#parsing_design_rationale_21) | Parsing Design Rationale | `parsing_design_rationale`, `Parsing`, `Rationale` +8 |

---

### Test 1: Execution Modes {#add}

**Test name:** `add`

**Description:**

### Scenario: ### Compiler Mode (Native Codegen)
- Requires explicit type annotations on all f...

### Compiler Mode (Native Codegen)
- Requires explicit type annotations on all function parameters and return types (like Rust)
- Compiles to native machine code via Cranelift
- Faster execution, suitable for production
- Example:

**Linked Symbols:**
- `add`
- `Add`

**Code:**

```simple
fn add(a: i64, b: i64) -> i64:
      return a + b
```

### Test 2: Execution Modes {#add}

**Test name:** `add`

**Description:**

### Scenario: ### Interpreter Mode
- Type annotations are optional - types are inferred at run...

### Interpreter Mode
- Type annotations are optional - types are inferred at runtime
- Supports all language features including dynamic typing
- Better for prototyping and scripting
- Example:

**Linked Symbols:**
- `add`
- `Add`

**Code:**

```simple
fn add(a, b):
      return a + b
```

### Test 3: Syntax Overview {#syntax_overview_3}

**Test name:** `syntax_overview_3`

**Linked Symbols:**
- `Overview`
- `syntax_overview`
- `overview`
- `syntax`
- `SyntaxOverview`
- `Syntax`
- `assert_compiles`

**Code:**

```simple
test "syntax_overview_3":
    """
    Syntax Overview
    """
    # An if/else example with indentation
    if x > 0:
        print "x is positive"
    else:
        print "x is non-positive"
    assert_compiles()
```

### Test 4: Syntax Overview {#syntax_overview_4}

**Test name:** `syntax_overview_4`

**Linked Symbols:**
- `Overview`
- `syntax_overview`
- `overview`
- `syntax`
- `SyntaxOverview`
- `Syntax`
- `assert_compiles`
- `Item`
- `Iterating`
- `Multiple`
- ... and 1 more

**Code:**

```simple
test "syntax_overview_4":
    """
    Syntax Overview
    """
    # Iterating with a trailing block (using backslash for lambda params)
    list.each \item:
        print "Item: {item}"

    # Multiple parameters
    map.each \key, value:
        print "{key}: {value}"
    assert_compiles()
```

### Test 5: Literals {#literals_5}

**Test name:** `literals_5`

**Linked Symbols:**
- `literals`
- `Literals`
- `assert_compiles`
- `Unix`
- `RGB`
- `Hexadecimal`
- `Decimal`
- `Binary`
- `Octal`

**Code:**

```simple
test "literals_5":
    """
    Literals
    """
    # Decimal (default)
    let count = 1_000_000         # underscores for readability

    # Hexadecimal (0x prefix)
    let color = 0xFF5733          # RGB color
    let mask = 0x0000_FFFF        # bit mask

    # Binary (0b prefix)
    let flags = 0b1010_0101       # bit flags

    # Octal (0o prefix)
    let permissions = 0o755       # Unix file permissions
    assert_compiles()
```

### Test 6: Literals {#literals_6}

**Test name:** `literals_6`

**Linked Symbols:**
- `literals`
- `Literals`
- `assert_compiles`

**Code:**

```simple
test "literals_6":
    """
    Literals
    """
    let pi = 3.14159
    let avogadro = 6.022e23       # scientific notation
    let tiny = 1.5e-10
    let big = 1_234_567.890_123   # with underscores
    assert_compiles()
```

### Test 7: Literals {#literals_7}

**Test name:** `literals_7`

**Linked Symbols:**
- `literals`
- `Literals`
- `assert_compiles`
- `f64`
- `f32`

**Code:**

```simple
test "literals_7":
    """
    Literals
    """
    let a = 42i32                 # i32
    let b = 100u64                # u64
    let c = 3.14f32               # f32 (single precision)
    let d = 2.718f64              # f64 (double precision)
    assert_compiles()
```

### Test 8: Literals {#literals_8}

**Test name:** `literals_8`

**Linked Symbols:**
- `literals`
- `Literals`
- `assert_compiles`
- `OrderId`
- `Physical`
- `UserId`
- `Semantic`
- `IDs`
- `Percentages`
- `type`
- ... and 1 more

**Code:**

```simple
test "literals_8":
    """
    Literals
    """
    # Physical units
    let distance = 100_km         # length type
    let duration = 2_hr           # time type
    let weight = 5_kg             # mass type

    # Semantic IDs
    let user = 42_uid             # UserId type
    let order = 100_oid           # OrderId type

    # Percentages
    let discount = 20_pct         # Percentage type (stored as 0.2)
    assert_compiles()
```

### Test 9: String Literals {#string_literals_9}

**Test name:** `string_literals_9`

**Linked Symbols:**
- `String`
- `literals`
- `string`
- `StringLiterals`
- `string_literals`
- `Literals`
- `assert_compiles`
- `Result`
- `Hello`
- `Count`

**Code:**

```simple
test "string_literals_9":
    """
    String Literals
    """
    let name = "world"
    let count = 42
    let msg = "Hello, {name}! Count is {count + 1}"
    # Result: "Hello, world! Count is 43"
    assert_compiles()
```

### Test 10: String Literals {#string_literals_10}

**Test name:** `string_literals_10`

**Linked Symbols:**
- `String`
- `literals`
- `string`
- `StringLiterals`
- `string_literals`
- `Literals`
- `assert_compiles`
- `Users`
- `Braces`
- `Backslashes`

**Code:**

```simple
test "string_literals_10":
    """
    String Literals
    """
    let regex = '[a-z]+\d{2,3}'     # No escaping needed
    let path = 'C:\Users\name'      # Backslashes are literal
    let template = '{name}'         # Braces are literal, not interpolation
    assert_compiles()
```

### Test 11: String Literals {#string_literals_11}

**Test name:** `string_literals_11`

**Linked Symbols:**
- `String`
- `literals`
- `string`
- `StringLiterals`
- `string_literals`
- `Literals`
- `assert_compiles`
- `Hello`
- `Same`

**Code:**

```simple
test "string_literals_11":
    """
    String Literals
    """
    let msg = f"Hello, {name}!"  # Same as "Hello, {name}!"
    assert_compiles()
```

### Test 12: String Literals {#string_literals_12}

**Test name:** `string_literals_12`

**Linked Symbols:**
- `String`
- `literals`
- `string`
- `StringLiterals`
- `string_literals`
- `Literals`
- `assert_compiles`
- `Users`
- `Network`
- `Socket`
- ... and 3 more

**Code:**

```simple
test "string_literals_12":
    """
    String Literals
    """
    # File paths (supports mingw-style with drive letters)
    let config = "/etc/config.json"_file
    let win_path = "C:/Users/data.txt"_file    # mingw-style drive letter

    # Network addresses
    let server = "192.168.1.1"_ip
    let api = "https://api.example.com/v1"_http
    let ftp_server = "ftp://files.example.com"_ftp

    # Socket addresses
    let endpoint = "127.0.0.1:8080"_sock

    # URLs and components
    let host = "example.com"_host
    let path = "/api/users"_urlpath
    assert_compiles()
```

### Test 13: String Literals {#string_literals_13}

**Test name:** `string_literals_13`

**Linked Symbols:**
- `String`
- `literals`
- `string`
- `StringLiterals`
- `string_literals`
- `Literals`
- `from_str`
- `assert_compiles`
- `ERROR`
- `HttpUrl`

**Code:**

```simple
test "string_literals_13":
    """
    String Literals
    """
    # ERROR: postfix not allowed on interpolated strings
    let url = "https://{host}/api"_http

    # OK: explicit conversion
    let url = HttpUrl::from_str("https://{host}/api")?
    assert_compiles()
```

### Test 14: Operators {#operators_14}

**Test name:** `operators_14`

**Linked Symbols:**
- `operators`
- `Operators`
- `assert_compiles`
- `is_ready`
- `proceed`
- `Discard`
- `done`
- `Suspending`
- `sleep`
- `fetch_user`

**Code:**

```simple
test "operators_14":
    """
    Operators
    """
    # Suspending assignment
    let user ~= fetch_user(id)

    # Suspending guard
    if~ is_ready():
        proceed()

    # Suspending loop
    while~ not done():
        _ ~= timer.sleep(100_ms)

    # Discard result
    _ ~= timer.sleep(100_ms)
    assert_compiles()
```

### Test 15: Functional Update Syntax (`->`) {#functional_update_syntax___15}

**Test name:** `functional_update_syntax___15`

**Linked Symbols:**
- `update`
- `functional_update_syntax__`
- `Functional`
- `syntax`
- `Update`
- `functional`
- `FunctionalUpdateSyntax`
- `Syntax`
- `assert_compiles`
- `filter`
- ... and 3 more

**Code:**

```simple
test "functional_update_syntax___15":
    """
    Functional Update Syntax (`->`)
    """
    let mut data = load_data()
    data->normalize()           # data = data.normalize()
    data->filter(min: 0)        # data = data.filter(min: 0)
    data->save("out.txt")       # data = data.save("out.txt")
    assert_compiles()
```

### Test 16: Functional Update Syntax (`->`) {#functional_update_syntax___16}

**Test name:** `functional_update_syntax___16`

**Linked Symbols:**
- `update`
- `functional_update_syntax__`
- `Functional`
- `syntax`
- `Update`
- `functional`
- `FunctionalUpdateSyntax`
- `Syntax`
- `assert_compiles`
- `normalize`
- ... and 2 more

**Code:**

```simple
test "functional_update_syntax___16":
    """
    Functional Update Syntax (`->`)
    """
    data->normalize()->filter(min: 0)->save("out.txt")
    assert_compiles()
```

### Test 17: Functional Update Syntax (`->`) {#functional_update_syntax___17}

**Test name:** `functional_update_syntax___17`

**Description:**

### Scenario: 1. Immutable data transformations - When methods return new instances:...

1. Immutable data transformations - When methods return new instances:

**Linked Symbols:**
- `update`
- `functional_update_syntax__`
- `Functional`
- `syntax`
- `Update`
- `functional`
- `FunctionalUpdateSyntax`
- `Syntax`
- `assert_compiles`
- `append`
- ... and 2 more

**Code:**

```simple
test "functional_update_syntax___17":
    """
    Functional Update Syntax (`->`)
    """
    let mut list = [1, 2, 3]
       list->append(4)->sort()->reverse()
       # list is now [4, 3, 2, 1]
    assert_compiles()
```

### Test 18: Functional Update Syntax (`->`) {#functional_update_syntax___18}

**Test name:** `functional_update_syntax___18`

**Description:**

### Scenario: 2. Builder patterns - When constructing objects step by step:...

2. Builder patterns - When constructing objects step by step:

**Linked Symbols:**
- `update`
- `functional_update_syntax__`
- `Functional`
- `syntax`
- `Update`
- `functional`
- `FunctionalUpdateSyntax`
- `Syntax`
- `assert_compiles`
- `new`
- ... and 4 more

**Code:**

```simple
test "functional_update_syntax___18":
    """
    Functional Update Syntax (`->`)
    """
    let mut config = Config.new()
       config->set_host("localhost")->set_port(8080)->set_timeout(30)
    assert_compiles()
```

### Test 19: Functional Update Syntax (`->`) {#functional_update_syntax___19}

**Test name:** `functional_update_syntax___19`

**Description:**

### Scenario: 3. State machine transitions:...

3. State machine transitions:

**Linked Symbols:**
- `update`
- `functional_update_syntax__`
- `Functional`
- `syntax`
- `Update`
- `functional`
- `FunctionalUpdateSyntax`
- `Syntax`
- `assert_compiles`
- `new`
- ... and 4 more

**Code:**

```simple
test "functional_update_syntax___19":
    """
    Functional Update Syntax (`->`)
    """
    let mut parser = Parser.new(input)
       parser->read_header()->validate()->parse_body()
    assert_compiles()
```

### Test 20: Parsing Design Rationale {#parsing_design_rationale_20}

**Test name:** `parsing_design_rationale_20`

**Description:**

### Scenario: 1. No-parentheses calls restricted to statement level: Parentheses can only be o...

1. No-parentheses calls restricted to statement level: Parentheses can only be omitted for the outermost method call in a statement:

**Linked Symbols:**
- `parsing_design_rationale`
- `Parsing`
- `Rationale`
- `Design`
- `ParsingDesignRationale`
- `rationale`
- `design`
- `parsing`
- `assert_compiles`
- `Valid`
- ... and 4 more

**Code:**

```simple
test "parsing_design_rationale_20":
    """
    Parsing Design Rationale
    """
    # Valid: outermost call drops parens
       print format("value: {x}")
       user.set name: "Alice", age: 30

       # Invalid: nested no-paren call is ambiguous
       # print format "value: {x}"  # Error: use parens for nested calls
    assert_compiles()
```

### Test 21: Parsing Design Rationale {#parsing_design_rationale_21}

**Test name:** `parsing_design_rationale_21`

**Description:**

### Scenario: 2. Backslash-prefixed lambda parameters: Lambda/block parameters use `\x` rather...

2. Backslash-prefixed lambda parameters: Lambda/block parameters use `\x` rather than `|x|`. The backslash is unambiguous:

**Linked Symbols:**
- `parsing_design_rationale`
- `Parsing`
- `Rationale`
- `Design`
- `ParsingDesignRationale`
- `rationale`
- `design`
- `parsing`
- `assert_compiles`
- `Clear`
- ... and 1 more

**Code:**

```simple
test "parsing_design_rationale_21":
    """
    Parsing Design Rationale
    """
    # Clear lambda syntax
       let double = \x: x * 2
       items.filter \x: x > 0

       # Multiple parameters
       pairs.map \a, b: a + b
    assert_compiles()
```

---

## Source Code

**View full specification:** [syntax_spec.spl](../../tests/specs/syntax_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/syntax_spec.spl`*

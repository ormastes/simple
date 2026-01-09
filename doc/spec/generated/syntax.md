# Simple Language Syntax Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/syntax_spec.spl`
> **Generated:** 2026-01-09 04:37:07
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

## Overview

Comprehensive specification of Simple's syntax, execution modes, and lexical structure.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

---

## Test Cases (21 total)

| Test | Section | Description |
|------|---------|-------------|
| [add](#test-1) | Execution Modes | ### Scenario: ### Compiler Mode (Native Codegen)... |
| [add](#test-2) | Execution Modes | ### Scenario: ### Interpreter Mode... |
| [syntax_overview_3](#test-3) | Syntax Overview |  |
| [syntax_overview_4](#test-4) | Syntax Overview |  |
| [literals_5](#test-5) | Literals |  |
| [literals_6](#test-6) | Literals |  |
| [literals_7](#test-7) | Literals |  |
| [literals_8](#test-8) | Literals |  |
| [string_literals_9](#test-9) | String Literals |  |
| [string_literals_10](#test-10) | String Literals |  |
| [string_literals_11](#test-11) | String Literals |  |
| [string_literals_12](#test-12) | String Literals |  |
| [string_literals_13](#test-13) | String Literals |  |
| [operators_14](#test-14) | Operators |  |
| [functional_update_syntax___15](#test-15) | Functional Update Syntax (`->`) |  |
| [functional_update_syntax___16](#test-16) | Functional Update Syntax (`->`) |  |
| [functional_update_syntax___17](#test-17) | Functional Update Syntax (`->`) | ### Scenario: 1. Immutable data transformations - When metho... |
| [functional_update_syntax___18](#test-18) | Functional Update Syntax (`->`) | ### Scenario: 2. Builder patterns - When constructing object... |
| [functional_update_syntax___19](#test-19) | Functional Update Syntax (`->`) | ### Scenario: 3. State machine transitions:...... |
| [parsing_design_rationale_20](#test-20) | Parsing Design Rationale | ### Scenario: 1. No-parentheses calls restricted to statemen... |
| [parsing_design_rationale_21](#test-21) | Parsing Design Rationale | ### Scenario: 2. Backslash-prefixed lambda parameters: Lambd... |

---

### Test 1: Execution Modes

**Test name:** `add`

**Description:**

### Scenario: ### Compiler Mode (Native Codegen)
- Requires explicit type annotations on all f...

### Compiler Mode (Native Codegen)
- Requires explicit type annotations on all function parameters and return types (like Rust)
- Compiles to native machine code via Cranelift
- Faster execution, suitable for production
- Example:

**Code:**

```simple
fn add(a: i64, b: i64) -> i64:
      return a + b
```

### Test 2: Execution Modes

**Test name:** `add`

**Description:**

### Scenario: ### Interpreter Mode
- Type annotations are optional - types are inferred at run...

### Interpreter Mode
- Type annotations are optional - types are inferred at runtime
- Supports all language features including dynamic typing
- Better for prototyping and scripting
- Example:

**Code:**

```simple
fn add(a, b):
      return a + b
```

### Test 3: Syntax Overview

**Test name:** `syntax_overview_3`

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

### Test 4: Syntax Overview

**Test name:** `syntax_overview_4`

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

### Test 5: Literals

**Test name:** `literals_5`

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

### Test 6: Literals

**Test name:** `literals_6`

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

### Test 7: Literals

**Test name:** `literals_7`

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

### Test 8: Literals

**Test name:** `literals_8`

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

### Test 9: String Literals

**Test name:** `string_literals_9`

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

### Test 10: String Literals

**Test name:** `string_literals_10`

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

### Test 11: String Literals

**Test name:** `string_literals_11`

**Code:**

```simple
test "string_literals_11":
    """
    String Literals
    """
    let msg = f"Hello, {name}!"  # Same as "Hello, {name}!"
    assert_compiles()
```

### Test 12: String Literals

**Test name:** `string_literals_12`

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

### Test 13: String Literals

**Test name:** `string_literals_13`

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

### Test 14: Operators

**Test name:** `operators_14`

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

### Test 15: Functional Update Syntax (`->`)

**Test name:** `functional_update_syntax___15`

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

### Test 16: Functional Update Syntax (`->`)

**Test name:** `functional_update_syntax___16`

**Code:**

```simple
test "functional_update_syntax___16":
    """
    Functional Update Syntax (`->`)
    """
    data->normalize()->filter(min: 0)->save("out.txt")
    assert_compiles()
```

### Test 17: Functional Update Syntax (`->`)

**Test name:** `functional_update_syntax___17`

**Description:**

### Scenario: 1. Immutable data transformations - When methods return new instances:...

1. Immutable data transformations - When methods return new instances:

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

### Test 18: Functional Update Syntax (`->`)

**Test name:** `functional_update_syntax___18`

**Description:**

### Scenario: 2. Builder patterns - When constructing objects step by step:...

2. Builder patterns - When constructing objects step by step:

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

### Test 19: Functional Update Syntax (`->`)

**Test name:** `functional_update_syntax___19`

**Description:**

### Scenario: 3. State machine transitions:...

3. State machine transitions:

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

### Test 20: Parsing Design Rationale

**Test name:** `parsing_design_rationale_20`

**Description:**

### Scenario: 1. No-parentheses calls restricted to statement level: Parentheses can only be o...

1. No-parentheses calls restricted to statement level: Parentheses can only be omitted for the outermost method call in a statement:

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

### Test 21: Parsing Design Rationale

**Test name:** `parsing_design_rationale_21`

**Description:**

### Scenario: 2. Backslash-prefixed lambda parameters: Lambda/block parameters use `\x` rather...

2. Backslash-prefixed lambda parameters: Lambda/block parameters use `\x` rather than `|x|`. The backslash is unambiguous:

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

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/syntax_spec.spl`*

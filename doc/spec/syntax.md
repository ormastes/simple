# Simple Language Syntax Specification

> **⚠️ MIGRATED:** This specification has been migrated to an executable test file:  
> **→** `tests/specs/syntax_spec.spl`  
> **Date:** 2026-01-09  
> 
> This file is kept for reference but may become outdated. The _spec.spl file is the source of truth.

**Status:** Stable
**Feature IDs:** #10-19
**Last Updated:** 2025-12-28
**Keywords:** syntax, lexical, operators, execution-modes, indentation
**Topics:** syntax, type-system

Comprehensive specification of Simple's syntax, execution modes, and lexical structure.

## Related Specifications
- [Types](types.md) - Type annotations and type syntax
- [Functions](functions.md) - Function definition syntax
- [Parser](parser/overview.md) - Parser implementation details

---

This document covers the core syntax, execution modes, and basic language constructs.

## Execution Modes

Simple supports two execution modes with different type requirements:

### Compiler Mode (Native Codegen)
- **Requires explicit type annotations** on all function parameters and return types (like Rust)
- Compiles to native machine code via Cranelift
- Faster execution, suitable for production
- Example:
  ```simple
  fn add(a: i64, b: i64) -> i64:
      return a + b
  ```

### Interpreter Mode
- **Type annotations are optional** - types are inferred at runtime
- Supports all language features including dynamic typing
- Better for prototyping and scripting
- Example:
  ```simple
  fn add(a, b):
      return a + b
  ```

**Compatibility**: Code written for compiler mode (with types) runs in both modes. Code without type annotations only runs in interpreter mode.

---

## Syntax Overview

Simple is a statically typed programming language with a clean, high-level syntax. It uses indentation to define code blocks (similar to Python) instead of braces or end keywords. All statements indented at the same level belong to the same block, and a decrease in indentation signifies the end of the current block. Indentation makes the structure of code clear and enforceable by the language (not just a style choice). For example:

```simple
# An if/else example with indentation
if x > 0:
    print "x is positive"
else:
    print "x is non-positive"
```

Simple's syntax also draws inspiration from Ruby for method calls and DSLs. Method calls do not require parentheses around arguments at the **statement level** (outermost position only), especially for DSL-style usage. For instance, `user.set name: "John", age: 30` is valid, treating `name:` and `age:` as named arguments. However, nested calls require parentheses to maintain unambiguous, one-pass parsing: `print format("Hello", name)` rather than `print format "Hello", name`. This restriction ensures the grammar remains LL(1)-compatible with single-token lookahead.

### Trailing Blocks

Trailing blocks (closures) can be passed to methods for iteration or DSL constructs. A method call can be followed by a block introduced by a backslash-prefixed parameter list and colon:

```simple
# Iterating with a trailing block (using backslash for lambda params)
list.each \item:
    print "Item: {item}"

# Multiple parameters
map.each \key, value:
    print "{key}: {value}"
```

The block is introduced by `\item` (the backslash signals lambda parameters, inspired by ML-family languages) and a colon, then indented code as the block body. No semicolons are needed at end of lines (newlines separate statements). Comments begin with `#` and extend to end of line.

---

## Literals

### Numbers

Numbers (`42`, `3.14`), booleans (`true`, `false`), and `nil` for "null" are supported. Underscores can be used in numeric literals for readability (e.g. `1_000_000`).

### Numeric Literal Formats

Simple supports multiple numeric literal formats for different bases:

| Format | Prefix | Example | Value |
|--------|--------|---------|-------|
| Decimal | (none) | `42`, `1_000_000` | 42, 1000000 |
| Hexadecimal | `0x` | `0xFF`, `0x1A2B` | 255, 6699 |
| Binary | `0b` | `0b1010`, `0b1111_0000` | 10, 240 |
| Octal | `0o` | `0o755`, `0o17` | 493, 15 |

```simple
# Decimal (default)
let count = 1_000_000         # underscores for readability

# Hexadecimal (0x prefix)
let color = 0xFF5733          # RGB color
let mask = 0x0000_FFFF        # bit mask

# Binary (0b prefix)
let flags = 0b1010_0101       # bit flags

# Octal (0o prefix)
let permissions = 0o755       # Unix file permissions
```

### Floating Point Literals

```simple
let pi = 3.14159
let avogadro = 6.022e23       # scientific notation
let tiny = 1.5e-10
let big = 1_234_567.890_123   # with underscores
```

### Type Suffixes

Explicit type suffixes for numeric literals:

```simple
let a = 42i32                 # i32
let b = 100u64                # u64
let c = 3.14f32               # f32 (single precision)
let d = 2.718f64              # f64 (double precision)
```

### Unit Type Suffixes

Simple supports **unit literal suffixes** for creating values with semantic types. This is the recommended way to create unit-typed values:

```simple
# Physical units
let distance = 100_km         # length type
let duration = 2_hr           # time type
let weight = 5_kg             # mass type

# Semantic IDs
let user = 42_uid             # UserId type
let order = 100_oid           # OrderId type

# Percentages
let discount = 20_pct         # Percentage type (stored as 0.2)
```

The underscore `_` separates the numeric value from the unit suffix. The compiler looks up the suffix in defined unit types (see [Unit Types](units.md) for the complete specification).

**Grammar:**
```
suffixed_literal = number_literal '_' identifier
```

**Benefits:**
- Type safety at compile time
- Self-documenting code
- No accidental mixing of incompatible units

See [Unit Types](units.md) for defining custom unit types.

---

## String Literals

Simple has two string literal types:

### Interpolated Strings (default)

Double quotes `"..."` create strings with automatic interpolation where `{expr}` embeds the value of any expression:

```simple
let name = "world"
let count = 42
let msg = "Hello, {name}! Count is {count + 1}"
# Result: "Hello, world! Count is 43"
```

Use `{{` and `}}` for literal braces.

### Raw Strings

Single quotes `'...'` create raw strings with no interpolation or escape processing:

```simple
let regex = '[a-z]+\d{2,3}'     # No escaping needed
let path = 'C:\Users\name'      # Backslashes are literal
let template = '{name}'         # Braces are literal, not interpolation
```

Raw strings are useful for regular expressions, file paths, and templates.

### Legacy f-string prefix

For compatibility, the `f` prefix is still supported but optional since double-quoted strings interpolate by default:

```simple
let msg = f"Hello, {name}!"  # Same as "Hello, {name}!"
```

### String Unit Suffixes

String literals can have **unit suffixes** for semantic typing. This creates type-safe wrappers around string values:

```simple
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
```

**Grammar:**
```
string_unit = string_literal '_' identifier
```

**Note**: F-strings (interpolated) cannot have unit suffixes. Use explicit conversion:

```simple
# ERROR: postfix not allowed on interpolated strings
let url = "https://{host}/api"_http

# OK: explicit conversion
let url = HttpUrl::from_str("https://{host}/api")?
```

**Standard String Unit Suffixes:**

| Category | Suffix | Unit Type | Example |
|----------|--------|-----------|---------|
| Files | `_file` | FilePath | `"/path/to/file"_file` |
| | `_filename` | FileName | `"config"_filename` |
| | `_ext` | FileExt | `"json"_ext` |
| | `_dir` | DirPath | `"/home/user"_dir` |
| Network | `_ip` | IpAddr | `"127.0.0.1"_ip` |
| | `_ipv4` | Ipv4Addr | `"192.168.1.1"_ipv4` |
| | `_ipv6` | Ipv6Addr | `"::1"_ipv6` |
| | `_sock` | SocketAddr | `"127.0.0.1:8080"_sock` |
| | `_mac` | MacAddr | `"00:1A:2B:3C:4D:5E"_mac` |
| URLs | `_url` | Url | `"https://example.com"_url` |
| | `_http` | HttpUrl | `"https://api.example.com"_http` |
| | `_ftp` | FtpUrl | `"ftp://files.example.com"_ftp` |
| | `_host` | Host | `"example.com"_host` |
| | `_urlpath` | UrlPath | `"/api/v1"_urlpath` |

See [Unit Types](units.md) for the complete specification of string unit types.

---

## Operators

Standard arithmetic and comparison operators (`+`, `-`, `*`, `/`, `==`, `!=`, `<`, `>` etc.), logical operators (`and`, `or`, `not`), and the method chaining arrow operator (`->`) are available.

### Suspension Operator (`~`)

The `~` operator marks explicit suspension points for async operations:

| Syntax | Context | Meaning |
|--------|---------|---------|
| `x ~= expr` | Assignment | Await `expr` and assign to `x` |
| `if~ cond:` | Guard | Suspending condition |
| `while~ cond:` | Guard | Suspending loop condition |
| `for~ x in iter:` | Loop | Async iterator |
| `and~`, `or~` | Boolean | Suspending operand |
| `~+=`, `~-=` | Compound | Suspending modify-assign |

```simple
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
```

See [Suspension Operator](suspension_operator.md) for complete specification.

---

## Functional Update Syntax (`->`)

Simple introduces a functional update syntax using `->`. Writing `target->method(args)` is syntactic sugar that:
1. Calls `target.method(args)`
2. Assigns the result back to `target`

This is equivalent to `target = target.method(args)` but more concise.

### Basic Usage

```simple
let mut data = load_data()
data->normalize()           # data = data.normalize()
data->filter(min: 0)        # data = data.filter(min: 0)
data->save("out.txt")       # data = data.save("out.txt")
```

### Chaining

Multiple updates can be chained in a single expression:

```simple
data->normalize()->filter(min: 0)->save("out.txt")
```

### Use Cases

The `->` operator is particularly useful for:

1. **Immutable data transformations** - When methods return new instances:
   ```simple
   let mut list = [1, 2, 3]
   list->append(4)->sort()->reverse()
   # list is now [4, 3, 2, 1]
   ```

2. **Builder patterns** - When constructing objects step by step:
   ```simple
   let mut config = Config.new()
   config->set_host("localhost")->set_port(8080)->set_timeout(30)
   ```

3. **State machine transitions**:
   ```simple
   let mut parser = Parser.new(input)
   parser->read_header()->validate()->parse_body()
   ```

### Requirements

- The target must be a mutable variable (`let mut` or mutable field)
- The method must return a value compatible with the target's type
- Works with any expression that evaluates to an assignable location

---

## Line Continuation

A line ending with a backslash `\` followed immediately by a newline will continue on the next line (though in many cases, indentation or parentheses make this unnecessary). Note: This is unambiguous with lambda syntax since line continuation requires `\` at line end, while lambda params have `\` followed by identifiers.

---

## Parsing Design Rationale

Simple's syntax is carefully designed to support **true one-pass, predictive parsing** with at most one token of lookahead (LL(1) or near-LL(1)). Two key decisions enable this:

1. **No-parentheses calls restricted to statement level**: Parentheses can only be omitted for the outermost method call in a statement:
   ```simple
   # Valid: outermost call drops parens
   print format("value: {x}")
   user.set name: "Alice", age: 30

   # Invalid: nested no-paren call is ambiguous
   # print format "value: {x}"  # Error: use parens for nested calls
   ```

2. **Backslash-prefixed lambda parameters**: Lambda/block parameters use `\x` rather than `|x|`. The backslash is unambiguous:
   ```simple
   # Clear lambda syntax
   let double = \x: x * 2
   items.filter \x: x > 0

   # Multiple parameters
   pairs.map \a, b: a + b
   ```

---

## Grammar Summary

```
integer     = decimal | hex | binary | octal
decimal     = [0-9][0-9_]*
hex         = '0x' [0-9a-fA-F][0-9a-fA-F_]*
binary      = '0b' [01][01_]*
octal       = '0o' [0-7][0-7_]*

float       = decimal '.' decimal [exponent]? | decimal exponent
exponent    = [eE] [+-]? decimal

type_suffix = 'i8' | 'i16' | 'i32' | 'i64' | 'u8' | 'u16' | 'u32' | 'u64' | 'f32' | 'f64'
unit_suffix = identifier

suffixed    = (integer | float) '_' (unit_suffix | type_suffix)
```

---

## Related Specifications

- [Types and Mutability](types.md)
- [Unit Types](units.md)
- [Functions and Pattern Matching](functions.md)
- [Lexer and Parser](lexer_parser.md)

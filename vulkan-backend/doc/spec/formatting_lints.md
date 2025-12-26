# Simple Language Formatting and Semantic Lints

**Version:** 2025-12
**Status:** Specification

This document defines the canonical formatting rules and semantic lint set for Simple, providing deterministic, reproducible code style and compile-time semantic checks.

---

## 1. Overview

Simple provides:

1. **Canonical Formatter** - Deterministic formatting with no configuration
2. **Semantic Lints** - Compile-time checks encoding language invariants
3. **Fix-it Hints** - Actionable suggestions in diagnostics
4. **Lint Control** - Attributes to allow/deny specific lints

Goals:
- **No style debates** - One canonical format
- **Stable diffs** - Formatting changes don't cause churn
- **LLM-friendly** - Clear, predictable output for code generation
- **Safety by default** - Semantic lints catch common errors

---

## 2. Canonical Formatter

### 2.1 Design Principles

| Principle | Description |
|-----------|-------------|
| **Deterministic** | Same input always produces same output |
| **No config** | Zero configuration options |
| **Stable** | Format preserves semantics exactly |
| **Fast** | O(n) in file size |
| **Idempotent** | format(format(x)) == format(x) |

### 2.2 Indentation Rules

```simple
# Indentation: 4 spaces (always, no tabs)
fn example():
    let x = 1
    if x > 0:
        print("positive")
    else:
        print("non-positive")

# Continuation indent: 8 spaces (2 × 4)
let long_expression = some_function(
        arg1,
        arg2,
        arg3,
    )

# No trailing whitespace
# No multiple blank lines (max 1)
```

### 2.3 Line Length

```simple
# Maximum line length: 100 characters
# Exception: Strings that would break are kept intact

# Break before operators for long expressions
let result = very_long_expression
    + another_long_expression
    + yet_another_expression

# Break after opening for calls/collections
let list = [
    item1,
    item2,
    item3,
]
```

### 2.4 Spacing Rules

```simple
# Binary operators: space on both sides
let x = a + b * c

# Unary operators: no space
let neg = -x
let not_flag = !flag

# Colons in types: space after
fn foo(x: i32, y: str) -> bool:

# Colons in dicts/structs: space after
let d = {key: value, other: 42}
let p = Point{x: 1.0, y: 2.0}

# Commas: space after, not before
let tuple = (a, b, c)

# No space inside parentheses/brackets
let arr = [1, 2, 3]
fn call(arg)
```

### 2.5 Blank Line Rules

```simple
# Two blank lines between top-level definitions
fn first():
    pass


fn second():
    pass


# One blank line between methods in class/impl
class Example:
    fn method1(self):
        pass

    fn method2(self):
        pass

# No blank lines at start/end of blocks
fn clean():
    let x = 1
    return x
```

### 2.6 Import Formatting

```simple
# Imports sorted alphabetically
# Standard library first, then third-party, then local
use core.collections.{Dict, List}
use core.io.{File, Path}

use external.http.Client
use external.json.parse

use myproject.utils.helper
```

### 2.7 Comment Formatting

```simple
# Single-line comments: space after #
# This is a comment

# Block comments: aligned, no trailing spaces
#
# Multi-line comment block
# continues here
#

# Doc comments: triple quotes, first line summary
"""
Short summary of the function.

Longer description if needed.
"""
fn documented():
    pass
```

---

## 3. Semantic Lint Categories

### 3.1 Lint Severity Levels

| Level | Description | Default Action |
|-------|-------------|----------------|
| `error` | Definite bug or safety issue | Compile fails |
| `warn` | Likely bug or bad practice | Compile succeeds with warning |
| `info` | Style suggestion | Only shown with --verbose |
| `allow` | Explicitly permitted | Not shown |

### 3.2 Safety Lints (Default: error)

| Lint | Description |
|------|-------------|
| `unsafe_without_context` | Unsafe operation outside unsafe block |
| `data_race_potential` | Shared mutation without sync in lock_base mode |
| `null_deref` | Potential null pointer dereference |
| `use_after_move` | Using moved value |
| `uninitialized_read` | Reading uninitialized memory |
| `buffer_overflow` | Array access potentially out of bounds |

```simple
# Example: unsafe_without_context
fn bad():
    let ptr: *mut i64 = get_pointer()
    *ptr = 42  # ERROR: unsafe operation outside unsafe block

fn good():
    let ptr: *mut i64 = get_pointer()
    unsafe:
        *ptr = 42  # OK
```

### 3.3 Correctness Lints (Default: error)

| Lint | Description |
|------|-------------|
| `non_exhaustive_match` | Match doesn't cover all cases |
| `unreachable_pattern` | Pattern can never match |
| `unused_result` | Result/Option not handled |
| `infinite_loop` | Loop with no break/return |
| `dead_code` | Code that can never execute |
| `type_mismatch` | Type error |

```simple
# Example: non_exhaustive_match
enum Status:
    Ok
    Error
    Pending

fn check(s: Status) -> str:
    match s:
        case Ok:
            return "ok"
        case Error:
            return "error"
        # ERROR: non-exhaustive match, missing: Pending
```

### 3.4 Warning Lints (Default: warn)

| Lint | Description |
|------|-------------|
| `unused_variable` | Variable declared but never used |
| `unused_import` | Import never referenced |
| `unused_mut` | Mutable variable never mutated |
| `shadowing` | Variable shadows outer scope |
| `redundant_clone` | Unnecessary clone operation |
| `unnecessary_cast` | Cast to same type |
| `deprecated` | Using deprecated API |

```simple
# Example: unused_mut
fn example():
    let mut x = 1  # WARN: variable `x` is mut but never mutated
    return x

# Fixed:
fn example():
    let x = 1  # OK
    return x
```

### 3.5 Style Lints (Default: info)

| Lint | Description |
|------|-------------|
| `naming_convention` | Name doesn't follow convention |
| `line_too_long` | Line exceeds 100 characters |
| `missing_doc` | Public item without documentation |
| `complex_function` | Function too complex (cyclomatic > 10) |
| `deep_nesting` | Nesting depth > 4 levels |
| `magic_number` | Literal number without name |

```simple
# Example: naming_convention
fn BadName():  # WARN: function should be snake_case
    pass

fn good_name():  # OK
    pass
```

### 3.6 Concurrency Lints (Default varies by mode)

| Lint | Default in actor | Default in lock_base |
|------|------------------|---------------------|
| `shared_mut_state` | error | allow |
| `mutex_in_actor` | error | allow |
| `missing_sync` | N/A | warn |
| `lock_ordering` | N/A | warn |

```simple
# Example: shared_mut_state in actor mode
#[concurrency_mode(actor)]
mod my_module

let mut global: i64 = 0  # ERROR: shared mutable state in actor mode
```

---

## 4. Lint Control Attributes

### 4.1 Allow/Deny/Warn

```simple
# Allow specific lint
#[allow(unused_variable)]
fn example():
    let x = 1  # No warning

# Deny lint (upgrade to error)
#[deny(deprecated)]
fn strict():
    old_api()  # ERROR instead of warning

# Warn (downgrade from error)
#[warn(non_exhaustive_match)]
fn lenient(s: Status):
    match s:
        case Ok:
            return "ok"
        # Warning instead of error
```

### 4.2 Scope of Lint Attributes

```simple
# Module-level
#[allow(unused_import)]
mod my_module

# Function-level
#[deny(magic_number)]
fn precise():
    let timeout = 30  # ERROR: magic number

# Expression-level
fn mixed():
    let x = #[allow(magic_number)] 42
```

### 4.3 Lint Groups

```simple
# Predefined groups
#[deny(all)]              # All lints as errors
#[allow(style)]           # All style lints allowed
#[deny(safety)]           # All safety lints as errors
#[warn(correctness)]      # All correctness lints as warnings

# Custom group in config
# simple.sdn
lints:
    groups:
        my_strict: [unused_mut, shadowing, magic_number]
```

---

## 5. Fix-it Hints

### 5.1 Actionable Suggestions

Every warning/error includes actionable fix suggestions:

```
warning[W0101]: unused variable `x`
  --> src/main.spl:5:9
   |
 5 |     let x = compute()
   |         ^ unused variable
   |
   = help: prefix with underscore if intentional: `_x`
   = fix: remove the variable declaration
```

### 5.2 Auto-fix Support

```bash
# Apply all auto-fixable suggestions
simple fix src/

# Apply specific lint fixes
simple fix --lint unused_import src/

# Preview fixes without applying
simple fix --dry-run src/
```

### 5.3 Fix Categories

| Category | Description | Auto-fixable |
|----------|-------------|--------------|
| **Trivial** | Remove unused, add underscore | Yes |
| **Simple** | Add missing case, remove redundant | Yes |
| **Complex** | Refactor logic, split function | No (suggestion only) |

---

## 6. Diagnostic Contracts

### 6.1 Diagnostic Structure

Every diagnostic MUST include:

```
<severity>[<code>]: <message>
  --> <file>:<line>:<column>
   |
<context lines with annotations>
   |
   = help: <explanation>
   = fix: <actionable suggestion>
   = note: <additional context> (optional)
```

### 6.2 Error Codes

| Range | Category |
|-------|----------|
| E0001-E0099 | Syntax errors |
| E0100-E0199 | Type errors |
| E0200-E0299 | Borrow/ownership errors |
| E0300-E0399 | Pattern matching errors |
| E0400-E0499 | Concurrency errors |
| E0500-E0599 | FFI errors |
| W0001-W0099 | Unused warnings |
| W0100-W0199 | Style warnings |
| W0200-W0299 | Performance warnings |
| W0300-W0399 | Deprecation warnings |

### 6.3 Diagnostic Stability

- Error codes are **stable** across versions
- New lints get new codes
- Removed lints: code reserved, never reused
- Lint behavior changes require deprecation cycle

---

## 7. Configuration

### 7.1 Project Configuration (simple.sdn)

```sdn
lints:
    # Global settings
    default_level: warn

    # Per-lint overrides
    allow: [magic_number, line_too_long]
    deny: [unsafe_without_context, data_race_potential]
    warn: [unused_variable]

    # Per-path overrides
    paths:
        test/**:
            allow: [unused_variable, dead_code]
        src/ffi/**:
            allow: [unsafe_without_context]

formatter:
    # No options - deterministic
    enabled: true
```

### 7.2 Command Line

```bash
# Format
simple fmt                    # Format all
simple fmt --check            # Check only (CI)
simple fmt src/main.spl       # Format specific file

# Lint
simple lint                   # Run all lints
simple lint --deny all        # Strict mode
simple lint --allow style     # Ignore style lints
simple lint --explain E0101   # Explain error code
```

---

## 8. LLM-Friendly Features

### 8.1 Predictable Output

- Canonical format means LLM-generated code matches human style
- No ambiguity in formatting decisions
- Generated code passes `simple fmt --check`

### 8.2 Clear Error Messages

- Error messages written for clarity
- Include relevant context
- Suggest specific fixes

### 8.3 Semantic Constraints as Guardrails

| Lint | LLM Benefit |
|------|-------------|
| `non_exhaustive_match` | Forces complete handling |
| `unused_result` | Prevents ignoring errors |
| `type_mismatch` | Clear type constraints |
| `unsafe_without_context` | Explicit safety boundaries |

---

## 9. Implementation Checklist

| Feature ID | Feature | Status |
|------------|---------|--------|
| #1131 | Canonical formatter | 📋 |
| #1132 | Formatter CLI (`simple fmt`) | 📋 |
| #1133 | Format-on-save IDE integration | 📋 |
| #1134 | Safety lint set | 📋 |
| #1135 | Correctness lint set | 📋 |
| #1136 | Warning lint set | 📋 |
| #1137 | Style lint set | 📋 |
| #1138 | Concurrency lint set | 📋 |
| #1139 | `#[allow]`/`#[deny]`/`#[warn]` attributes | 📋 |
| #1140 | Lint groups | 📋 |
| #1141 | Fix-it hints in diagnostics | 📋 |
| #1142 | Auto-fix CLI (`simple fix`) | 📋 |
| #1143 | Error code stability | 📋 |
| #1144 | Lint configuration in simple.sdn | 📋 |
| #1145 | `--explain` for error codes | 📋 |

---

## Related Documents

- [Concurrency Modes](language_enhancement.md) - Mode-specific lints
- [Pattern Matching](language_enhancement.md) - Exhaustiveness
- [FFI/ABI](ffi_abi.md) - FFI safety lints
- [SDN](sdn.md) - Configuration format

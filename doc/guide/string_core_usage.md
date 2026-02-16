# String Core Module - Usage Guide

**Module:** `src/std/string_core.spl`
**Purpose:** Canonical string utility implementations
**Status:** Production Ready

## Quick Start

```simple
use std.text_core.{str_len, str_concat, str_trim}

val text = "  hello world  "
val cleaned = str_trim(text)           # "hello world"
val length = str_len(cleaned)          # 11
val result = str_concat(cleaned, "!") # "hello world!"
```

## When to Use

**Use `string_core` when:**
- You need basic string operations (length, concat, slicing)
- You need search operations (contains, index_of, starts_with)
- You need case conversion (to_lower, to_upper)
- You need string manipulation (reverse, repeat, truncate)
- You want consistent, tested implementations

**Use `std.text` when:**
- You need `char_code` / `char_from_code` (ASCII lookup tables)
- You need platform-specific newlines
- You need hash functions
- You need integer parsing

**Use `std.template.utilities` when:**
- You need HTML/URL/JS/CSS escaping
- You need hexadecimal conversion
- You're working with template engines

## Function Reference

### Basic Operations

```simple
use std.text_core.{str_len, str_concat, str_eq}

str_len("hello")              # → 5
str_concat("hello", " world") # → "hello world"
str_eq("test", "test")        # → true
```

### Slicing and Access

```simple
use std.text_core.{str_slice, str_char_at, str_safe_slice}

str_slice("hello", 0, 3)       # → "hel"
str_char_at("hello", 1)        # → "e"
str_char_at("hello", 99)       # → "" (safe, returns empty)
str_safe_slice("hi", -1, 100)  # → "hi" (bounds-safe)
```

**CRITICAL:** Always use `s[0:idx]` format in slicing - never `s[:idx]` (runtime parser bug)

### Search Operations

```simple
use std.text_core.{str_contains, str_starts_with, str_ends_with}
use std.text_core.{str_index_of, str_last_index_of}

str_contains("hello world", "world")  # → true
str_starts_with("hello", "hel")       # → true
str_ends_with("hello", "lo")          # → true
str_index_of("hello", "l")            # → 2 (first occurrence)
str_last_index_of("hello", "l")       # → 3 (last occurrence)
str_index_of("hello", "x")            # → -1 (not found)
```

### Whitespace Trimming

```simple
use std.text_core.{str_trim, str_trim_left, str_trim_right}
use std.text_core.{is_whitespace_char}

str_trim("  hello  ")       # → "hello"
str_trim_left("  hello  ")  # → "hello  "
str_trim_right("  hello  ") # → "  hello"
is_whitespace_char(" ")     # → true
is_whitespace_char("a")     # → false
```

### Replacement

```simple
use std.text_core.{str_replace, str_replace_all}

str_replace("hello", "l", "L")      # → "heLlo" (first only)
str_replace_all("hello", "l", "L")  # → "heLLo" (all)
```

**WARNING:** Avoid chained method calls (runtime bug). Use intermediate `var`:

```simple
# Bad (chained methods broken in runtime)
val result = s.replace("a", "A").replace("b", "B")

# Good (use intermediate var)
var step1 = s.replace("a", "A")
var result = step1.replace("b", "B")

# Better (use str_replace_all)
var result = str_replace_all(s, "a", "A")
result = str_replace_all(result, "b", "B")
```

### Split and Join

```simple
use std.text_core.{str_split, str_join}

val parts = str_split("a,b,c", ",")  # → ["a", "b", "c"]
str_join(["x", "y", "z"], "-")       # → "x-y-z"
str_join([], ",")                    # → ""
```

### Character Classification

```simple
use std.text_core.{is_alpha_char, is_digit_char, is_alnum_char}

is_alpha_char("a")  # → true
is_alpha_char("5")  # → false
is_digit_char("5")  # → true
is_digit_char("a")  # → false
is_alnum_char("a")  # → true
is_alnum_char("5")  # → true
is_alnum_char(" ")  # → false
```

### Case Conversion

```simple
use std.text_core.{str_to_lower, str_to_upper, str_capitalize}

str_to_lower("HELLO")   # → "hello"
str_to_upper("hello")   # → "HELLO"
str_capitalize("hello") # → "Hello"
```

**Note:** ASCII only (A-Z, a-z). Non-ASCII characters are preserved unchanged.

### String Manipulation

```simple
use std.text_core.{str_reverse, str_repeat, str_truncate}
use std.text_core.{str_pad_left, str_pad_right, str_center}

str_reverse("hello")          # → "olleh"
str_repeat("ab", 3)           # → "ababab"
str_truncate("hello world", 8) # → "hello wo..."

str_pad_left("42", 5, "0")    # → "00042"
str_pad_right("42", 5, "0")   # → "42000"
str_center("hi", 6)           # → "  hi  "
```

## Migration Guide

### From Template Utilities

**Before:**
```simple
use std.template.utilities.{str_trim, str_contains, str_to_lower}
```

**After:**
```simple
use std.text_core.{str_trim, str_contains, str_to_lower}
```

**Compatibility:** Both work! Template utilities re-exports string_core functions.

### From Core Types

**Before:**
```simple
use core.types.{str_concat, str_len, str_trim}
```

**After:**
```simple
# For application code, use string_core
use std.text_core.{str_concat, str_len, str_trim}

# For compiler code, continue using core.types (avoids circular deps)
use core.types.{str_concat, str_len, str_trim}
```

## Best Practices

1. **Import what you need**
   ```simple
   # Good
   use std.text_core.{str_trim, str_split}

   # Avoid (explicit is better)
   use std.text_core.*
   ```

2. **Use safe variants for untrusted input**
   ```simple
   # Unsafe (may panic on invalid index)
   val ch = s[idx]

   # Safe (returns empty on invalid index)
   use std.text_core.{str_char_at}
   val ch = str_char_at(s, idx)
   ```

3. **Avoid runtime limitations**
   ```simple
   # Broken (runtime slicing bug)
   val prefix = s[:3]

   # Works (always use explicit start)
   use std.text_core.{str_slice}
   val prefix = str_slice(s, 0, 3)
   ```

4. **Prefer string_core over reimplementing**
   ```simple
   # Don't do this
   fn my_trim(s: text) -> text:
       var result = s
       while result.len() > 0 and result[0:1] == " ":
           result = result[1:]
       result

   # Do this
   use std.text_core.{str_trim}
   val result = str_trim(s)
   ```

## Complete Function List

**Basic:** str_len, str_concat, str_eq

**Slicing:** str_slice, str_char_at, str_safe_slice

**Search:** str_contains, str_starts_with, str_ends_with, str_index_of, str_last_index_of

**Trimming:** str_trim, str_trim_left, str_trim_right, is_whitespace_char

**Replacement:** str_replace, str_replace_all

**Split/Join:** str_split, str_join

**Classification:** is_alpha_char, is_digit_char, is_alnum_char

**Case:** str_to_lower, str_to_upper, str_capitalize

**Manipulation:** str_reverse, str_repeat, str_truncate, str_pad_left, str_pad_right, str_center

## See Also

- **Full implementation:** `src/std/string_core.spl`
- **Tests:** `test/unit/std/string_core_spec.spl`
- **Migration report:** `doc/report/string_utilities_consolidation_2026-02-14.md`
- **Related modules:** `src/std/text.spl`, `src/std/template/utilities.spl`

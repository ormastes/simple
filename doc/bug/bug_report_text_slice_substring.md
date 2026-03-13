# Bug Report: text.slice() returns wrong results, text.substring() crashes

**Bug ID:** INTERP-SLICE-001
**Date:** 2026-03-13
**Severity:** P0 - Critical (breaks all substring extraction in interpreter mode)
**Component:** Interpreter — text/string methods
**Status:** Confirmed, minimal reproduction available

## Summary

Three related bugs in the interpreter's text type:

1. **`text.slice(start, end)` returns wrong results** — only works for `slice(0, 1)`. Any other arguments return either a single char or empty string.
2. **`text.substring(start, end)` crashes** — throws "string index out of bounds" error.
3. **`s[i] == text_var` comparison crashes** — char (from indexing) vs text comparison fails.

## Minimal Reproduction

```simple
val s = "abcdefghijk"

# Bug 1: slice() broken
print s.slice(0, 1)   # "a" — correct
print s.slice(0, 2)   # "a" — WRONG, expected "ab"
print s.slice(0, 5)   # "a" — WRONG, expected "abcde"
print s.slice(1, 2)   # ""  — WRONG, expected "b"
print s.slice(1, 5)   # ""  — WRONG, expected "bcde"
print s.slice(2, 5)   # ""  — WRONG, expected "cde"

# Bug 2: substring() crashes
print s.substring(0, 5)   # CRASH: "string index out of bounds: index is 5 but length is 0"

# Bug 3: s[i] vs text comparison crashes
val ch_a: text = "a"
print s[0] == ch_a   # CRASH: "string index out of bounds: index is 0 but length is 0"

# These WORK (char literal comparison):
print s[0] == 'a'    # true — char == char works
print s[5] == ' '    # true — char == char works
```

## Observed Behavior

### Bug 1: `text.slice(start, end)`

| Expression | Expected | Actual |
|-----------|----------|--------|
| `"abcdefghijk".slice(0, 1)` | `"a"` | `"a"` (correct) |
| `"abcdefghijk".slice(0, 2)` | `"ab"` | `"a"` |
| `"abcdefghijk".slice(0, 3)` | `"abc"` | `"a"` |
| `"abcdefghijk".slice(1, 2)` | `"b"` | `""` |
| `"abcdefghijk".slice(1, 3)` | `"bc"` | `""` |
| `"abcdefghijk".slice(2, 5)` | `"cde"` | `""` |
| `"abcdefghijk".slice(5, 11)` | `"fghijk"` | `""` |

Pattern: only `slice(0, N)` returns any content (always just the first char). All `slice(N>0, M)` return empty.

### Bug 2: `text.substring(start, end)`
Crashes with: `semantic: string index out of bounds: index is 5 but length is 0`

### Bug 3: `s[i] == text_variable`
`s[i]` returns a **char** type. Comparing char with a **text** variable crashes with: `semantic: string index out of bounds: index is 0 but length is 0`

Char-literal comparison (`s[i] == 'x'`) works correctly.

## What Works (Workarounds)

- `s[i]` with char literal: `s[0] == 'a'` — works
- `for ch in text` iteration: yields single-char **text**, comparison with `"x"` works
- `text.split(delim)` — works correctly
- `text.starts_with()`, `text.ends_with()`, `text.trim()`, `text.len()` — all work

### Workaround for substring extraction

```simple
fn substr(s: text, start: i64, end_pos: i64) -> text:
    var buf: [text] = []
    var idx = 0
    for ch in s:
        if idx >= start and idx < end_pos:
            buf.push(ch)
        idx = idx + 1
    buf.join("")
```

### Workaround for single-char text extraction

```simple
fn char_at(s: text, index: i64) -> text:
    var idx = 0
    for ch in s:
        if idx == index:
            return ch
        idx = idx + 1
    ""
```

## Impact

- **T32 MCP JSON helpers**: All JSON field extraction broken (uses `t32_char_at` → `s.slice()`)
- **T32 CLI text parsers**: `split_on`, `split_whitespace` broken when using `s[i]` with text params
- **T32 SDN catalog parser**: Property parsing broken (uses `s.slice()` for key/value extraction)
- **Any code using `text.slice()` for substring extraction** in interpreter mode

## Environment

- Binary: `bin/release/simple` (interpreter mode)
- Platform: Linux x86_64
- Version: Simple v0.8.1

## Related

- The `for ch in text` iteration is the only reliable way to access individual characters as text type
- `s[i]` char indexing works but returns a **char** type that cannot be compared with text variables

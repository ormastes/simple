# Text Helpers P1 — Design Document

**Feature:** text_helpers_p1 (Phase A1 from `doc/02_requirements/feature/stdlib_helpers.md`)
**Plan:** `doc/03_plan/text_helpers_p1.md`
**Requirement:** `doc/02_requirements/feature/stdlib_helpers.md` — items T1-T5, T12, T20, T26, T40
**Date:** 2026-03-26

---

## Module Structure

All 9 methods are implemented as **library functions** in Simple (.spl), not as Rust built-in methods. This follows the "100% Pure Simple" principle and matches the existing pattern where `to_snake_case`, `to_camel_case`, and `to_title_case` live in the library.

### File Placement

| Method | File | Rationale |
|--------|------|-----------|
| `to_kebab_case()` | `src/lib/common/text_advanced.spl` | Case conversion — same section as `to_snake_case`, `to_camel_case` |
| `to_pascal_case()` | `src/lib/common/text_advanced.spl` | Case conversion — same section |
| `to_screaming_snake()` | `src/lib/common/text_advanced.spl` | Case conversion — same section |
| `chars_map(fn)` | `src/lib/common/text_advanced.spl` | Character transformation — new section |
| `tr(from, to)` | `src/lib/common/text_advanced.spl` | Character transformation — new section |
| `split_n(sep, n)` | `src/lib/common/text_advanced.spl` | Tokenization — extends existing section |
| `contains_any(chars)` | `src/lib/common/text_advanced.spl` | Character search — new section |
| `cut(sep)` | `src/lib/common/text_advanced.spl` | Tokenization — extends existing section |
| `gsub(pattern, fn)` | `src/lib/common/text_advanced.spl` | String manipulation — new section |
| `_split_words()` | `src/lib/common/text_advanced.spl` | Private helper — shared by case conversions |

### Why Not Built-in (Rust)?

1. Simple is self-hosted; all new stdlib code goes in `.spl` files.
2. These methods do not require low-level runtime access (no FFI, no syscalls).
3. Existing case conversions (`to_snake_case`, `to_camel_case`) are already library functions and work correctly.
4. The interpreter's `string.rs` built-in methods are only for operations that need Rust-level string primitives (`len`, `split`, `find`, `trim`, etc.).

---

## API Surface

### Shared Private Helper

```simple
fn _split_words(s: text) -> [text]
```

Splits text into word segments at:
- Uppercase letter transitions (camelCase boundaries): `"helloWorld"` -> `["hello", "World"]`
- Underscores: `"hello_world"` -> `["hello", "world"]`
- Hyphens: `"hello-world"` -> `["hello", "world"]`
- Spaces: `"hello world"` -> `["hello", "world"]`
- Consecutive uppercase followed by lowercase: `"XMLParser"` -> `["XML", "Parser"]`

Returns `[text]` of non-empty word segments. Private (prefixed with `_`).

---

### 1. `to_kebab_case(text) -> text`

**Requirement ref:** T1
**Signature:**
```simple
fn to_kebab_case(text: text) -> text
```

**Behavior:**
- Split input into words via `_split_words()`
- Lowercase each word
- Join with `"-"`

**Examples:**
```simple
to_kebab_case("HelloWorld")      # "hello-world"
to_kebab_case("hello_world")     # "hello-world"
to_kebab_case("XMLParser")       # "xml-parser"
to_kebab_case("already-kebab")   # "already-kebab"
to_kebab_case("")                # ""
```

**Edge cases:**
- Empty string returns `""`
- Single word returns lowercase: `"Hello"` -> `"hello"`
- All-uppercase: `"ABC"` -> `"abc"`

---

### 2. `to_pascal_case(text) -> text`

**Requirement ref:** T2
**Signature:**
```simple
fn to_pascal_case(text: text) -> text
```

**Behavior:**
- Split input into words via `_split_words()`
- Capitalize first letter of each word, lowercase the rest
- Join without separator

**Examples:**
```simple
to_pascal_case("hello_world")    # "HelloWorld"
to_pascal_case("hello world")    # "HelloWorld"
to_pascal_case("hello-world")    # "HelloWorld"
to_pascal_case("helloWorld")     # "HelloWorld"
to_pascal_case("")               # ""
```

**Relationship to `to_camel_case`:**
`to_pascal_case` capitalizes the first word; `to_camel_case` lowercases it.
Implementation: same as `to_camel_case` but capitalize the first word too.

---

### 3. `to_screaming_snake(text) -> text`

**Requirement ref:** T3
**Signature:**
```simple
fn to_screaming_snake(text: text) -> text
```

**Behavior:**
- Call `to_snake_case(text)` (existing function)
- Uppercase the entire result

**Examples:**
```simple
to_screaming_snake("helloWorld")   # "HELLO_WORLD"
to_screaming_snake("hello-world")  # "HELLO_WORLD"
to_screaming_snake("HelloWorld")   # "HELLO_WORLD"
to_screaming_snake("")             # ""
```

**Implementation note:** This is a two-line function — the simplest of all 9 methods.

---

### 4. `chars_map(text, fn(text) -> text) -> text`

**Requirement ref:** T4
**Signature:**
```simple
fn chars_map(s: text, f: fn(text) -> text) -> text
```

**Behavior:**
- Iterate each character of `s` (by index, `s[i]`)
- Call `f(char)` for each character
- Collect results into a `StringBuilder`
- Return the concatenated result

**Examples:**
```simple
chars_map("hello", \c: c.to_upper())                    # "HELLO"
chars_map("abc", \c: if c == "b": "_" else: c)          # "a_c"
chars_map("123", \c: "{c}{c}")                           # "112233"
```

**Design choice:** The callback receives and returns `text` (single character as text), not a char code. This matches Simple's convention where `s[i]` returns `text`.

**Note:** The callback may return a multi-character string, which makes `chars_map` more general than a 1:1 mapping. This is intentional (matches Go's `strings.Map` which allows deletion by returning -1, here by returning `""`).

---

### 5. `tr(text, text, text) -> text`

**Requirement ref:** T5
**Signature:**
```simple
fn tr(s: text, from: text, to: text) -> text
```

**Behavior:**
- Build a mapping: `from[0]` -> `to[0]`, `from[1]` -> `to[1]`, etc.
- If `to` is shorter than `from`, pad `to` with its last character
- For each character in `s`, if it appears in `from`, replace with corresponding `to` character; otherwise keep unchanged
- Return the transformed string

**Examples:**
```simple
tr("hello", "el", "ip")       # "hippo"
tr("abc", "abc", "xyz")       # "xyz"
tr("hello", "aeiou", "*")     # "h*ll*"  (to shorter than from)
tr("hello", "xyz", "abc")     # "hello"  (no matches)
```

**Edge cases:**
- Empty `from`: return `s` unchanged
- Empty `to` with non-empty `from`: delete matched characters (return only non-matched chars)
- Duplicate chars in `from`: first mapping wins

**Design note:** This is a literal character-level operation, not regex. Named `tr` after the Unix `tr` command and Ruby's `String#tr`.

---

### 6. `split_n(text, text, i64) -> [text]`

**Requirement ref:** T20
**Signature:**
```simple
fn split_n(s: text, sep: text, n: i64) -> [text]
```

**Behavior:**
- Split `s` by `sep`, producing at most `n` parts
- After `n-1` splits, the remainder (including any further separators) becomes the final part
- If there are fewer than `n` parts, return all parts found

**Examples:**
```simple
split_n("a.b.c.d", ".", 3)    # ["a", "b", "c.d"]
split_n("a.b.c.d", ".", 1)    # ["a.b.c.d"]
split_n("a.b", ".", 5)        # ["a", "b"]
split_n("hello", ".", 3)      # ["hello"]
```

**Edge cases:**
- `n <= 0`: return `[s]` (no splitting)
- `n == 1`: return `[s]` (no splitting)
- `sep` not found: return `[s]`
- Empty `sep`: return `[s]` (no splitting on empty separator)

---

### 7. `contains_any(text, text) -> bool`

**Requirement ref:** T26
**Signature:**
```simple
fn contains_any(s: text, chars: text) -> bool
```

**Behavior:**
- For each character in `s`, check if it exists anywhere in `chars`
- Return `true` on first match, `false` if no character matches

**Examples:**
```simple
contains_any("hello", "aeiou")     # true  ('e' and 'o' match)
contains_any("rhythm", "aeiou")    # false
contains_any("", "abc")            # false
contains_any("hello", "")          # false
```

**Design note:** This checks whether `s` contains any single character from the `chars` set. It is NOT substring search — each character in `chars` is checked independently.

---

### 8. `cut(text, text) -> (text, text, bool)`

**Requirement ref:** T40
**Signature:**
```simple
fn cut(s: text, sep: text) -> (text, text, bool)
```

**Behavior:**
- Find first occurrence of `sep` in `s`
- If found: return `(before, after, true)` where `before` = text before separator, `after` = text after separator (separator itself is excluded)
- If not found: return `(s, "", false)`

**Examples:**
```simple
cut("user=admin", "=")       # ("user", "admin", true)
cut("user=a=b", "=")         # ("user", "a=b", true)
cut("noequals", "=")         # ("noequals", "", false)
cut("", "=")                 # ("", "", false)
```

**Design note:** Modeled directly after Go's `strings.Cut`. Returns a 3-tuple. The `found` boolean allows callers to distinguish between "separator at end" (`cut("a=", "=")` -> `("a", "", true)`) and "no separator" (`cut("a", "=")` -> `("a", "", false)`).

**Relationship to existing `partition`:** The built-in `partition` method (in `string.rs`) returns `[before, sep, after]` as an array of 3 strings. `cut` differs by: (1) returning a tuple not array, (2) including a boolean `found` flag, (3) not including the separator in the result. `cut` is the idiomatic Go pattern; `partition` is the Python/Ruby pattern. Both are useful.

---

### 9. `gsub(text, text, fn(text) -> text) -> text`

**Requirement ref:** T12
**Signature:**
```simple
fn gsub(s: text, pattern: text, f: fn(text) -> text) -> text
```

**Behavior:**
- Find all non-overlapping occurrences of `pattern` in `s` (left to right)
- For each match, call `f(match)` to produce a replacement string
- Return the string with all matches replaced

**Examples:**
```simple
gsub("hello world", "o", \m: m.to_upper())     # "hellO wOrld"
gsub("aabbcc", "bb", \m: "XX")                  # "aaXXcc"
gsub("no match", "xyz", \m: "!")                 # "no match"
gsub("aaa", "a", \m: "{m}{m}")                  # "aaaaaa"
```

**Edge cases:**
- Empty `pattern`: return `s` unchanged (no infinite loop)
- `pattern` not found: return `s` unchanged
- Callback returns empty string: effectively deletes all matches

**Design note:** This is literal pattern matching only (not regex). Named after Ruby's `String#gsub` with block. The existing built-in `replace` method handles literal find-and-replace with a static string; `gsub` extends this with a callback for dynamic replacement.

**Future extension:** When Simple gains regex support, `gsub` could be overloaded to accept regex patterns. The literal-string version remains useful regardless.

---

## Integration Points

### 1. Re-exports in `text.spl`

After implementing all functions in `text_advanced.spl`, add them to the re-export line in `src/lib/common/text.spl` (line 418):

```simple
use lib.common.text_advanced.{
    # ... existing exports ...
    to_kebab_case, to_pascal_case, to_screaming_snake,
    chars_map, tr, split_n, contains_any, cut, gsub
}
```

This makes them available via `use std.text.{to_kebab_case}` or `use lib.common.text.{to_kebab_case}`.

### 2. Section Organization in `text_advanced.spl`

New functions are added in sections matching the existing file structure:

```
# ============================================================================
# Advanced Case Conversion (existing section — add to_kebab_case, to_pascal_case, to_screaming_snake)
# ============================================================================

# ============================================================================
# Character Transformation (NEW section — chars_map, tr)
# ============================================================================

# ============================================================================
# Advanced Tokenization (existing section — add split_n, cut)
# ============================================================================

# ============================================================================
# Character Search (NEW section — contains_any)
# ============================================================================

# ============================================================================
# Advanced String Replacement (NEW section — gsub)
# ============================================================================
```

### 3. Shared Helper Refactoring

The `_split_words()` helper extracts logic currently inline in `to_snake_case()`. After extraction:
- `to_snake_case()` calls `_split_words()` then joins with `"_"` and lowercases
- `to_camel_case()` could optionally be refactored to use `_split_words()` (not required, but recommended for consistency)
- `to_kebab_case()`, `to_pascal_case()`, `to_screaming_snake()` all use `_split_words()`

### 4. Existing Built-in Methods (No Conflicts)

The interpreter's `string.rs` already has:
- `split` — our `split_n` is a new function (not method), no conflict
- `partition` — our `cut` has different semantics (tuple + bool), no conflict
- `replace` — our `gsub` has callback variant, no conflict
- `contains` — our `contains_any` checks char set, no conflict

No changes to `src/compiler_rust/compiler/src/interpreter_method/string.rs` are needed.

### 5. Import Dependencies

All new functions use only:
- `std.string_core.{char_code, is_whitespace_char}` (already imported in text_advanced.spl)
- `common.string_builder.{StringBuilder}` (already imported in text_advanced.spl)
- Existing private helpers: `_is_alpha`, `_is_uppercase_char`, `_is_lowercase_char` (already defined in text_advanced.spl)
- `to_snake_case()` (for `to_screaming_snake`, already defined in same file)

No new imports are required.

---

## Test Plan

**Test file:** `test/lib/common/text_helpers_p1_spec.spl`

Each method gets a `describe` block with tests for:
1. Normal cases (2-3 examples from the requirement)
2. Edge cases (empty string, no match, single character)
3. Boundary cases (all-uppercase, all-lowercase, mixed separators)

For callback-accepting methods (`chars_map`, `gsub`):
4. Callback that returns empty string (deletion)
5. Callback that returns multi-character string (expansion)

---

## Cross-References

| Document | Relationship |
|----------|-------------|
| `doc/02_requirements/feature/stdlib_helpers.md` | Parent requirement (items T1-T5, T12, T20, T26, T40) |
| `doc/03_plan/text_helpers_p1.md` | Implementation plan (task breakdown, DAG, difficulty) |
| `src/lib/common/text_advanced.spl` | Implementation target |
| `src/lib/common/text.spl` | Re-export integration point |
| `src/compiler_rust/compiler/src/interpreter_method/string.rs` | Built-in methods (no changes needed) |

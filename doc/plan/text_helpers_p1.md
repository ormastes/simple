# Text Helpers P1 — Implementation Plan

**Feature:** text_helpers_p1 (Phase A1 from `doc/plan/requirement/stdlib_helpers.md`)
**Date:** 2026-03-26
**Scope:** 9 P1 text/string methods
**Status:** Planning

---

## Overview

Implement the 9 highest-priority text helper methods identified in the stdlib gap analysis.
All implementations are in Simple (.spl), following the "100% Pure Simple" principle.

---

## Task Breakdown

### Task 1: `to_kebab_case()` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Convert text to kebab-case. Splits on word boundaries (uppercase transitions, underscores, spaces), lowercases, joins with hyphens.
**Examples:**
- `"HelloWorld"` -> `"hello-world"`
- `"hello_world"` -> `"hello-world"`
- `"XMLParser"` -> `"xml-parser"`

**Subtasks:**
1. Reuse existing `_split_words()` helper (extract from `to_snake_case` pattern)
2. Lowercase each word, join with `"-"`
3. Add docstring and examples

**Dependencies:** None (uses existing `_is_uppercase_char`, `_is_lowercase_char`, `StringBuilder`)

---

### Task 2: `to_pascal_case()` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Convert text to PascalCase. Splits on word boundaries, capitalizes first letter of each word, joins without separator.
**Examples:**
- `"hello_world"` -> `"HelloWorld"`
- `"hello world"` -> `"HelloWorld"`
- `"hello-world"` -> `"HelloWorld"`

**Subtasks:**
1. Split on underscores, spaces, hyphens, and camelCase boundaries
2. Capitalize first char of each word, lowercase rest
3. Add docstring and examples

**Dependencies:** None (uses existing helpers)

---

### Task 3: `to_screaming_snake()` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Convert text to SCREAMING_SNAKE_CASE. Reuse `to_snake_case()` then uppercase.
**Examples:**
- `"helloWorld"` -> `"HELLO_WORLD"`
- `"hello-world"` -> `"HELLO_WORLD"`

**Subtasks:**
1. Call `to_snake_case()` on input
2. Uppercase the result
3. Add docstring and examples

**Dependencies:** Task 1 pattern (shared word-splitting), existing `to_snake_case()`

---

### Task 4: `chars_map(fn)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Apply a function to each character of a string, rebuild the result. Similar to Go's `strings.Map`.
**Signature:** `fn chars_map(s: text, f: fn(text) -> text) -> text`
**Examples:**
- `chars_map("hello", \c: c.to_upper())` -> `"HELLO"`
- `chars_map("abc", \c: if c == "b": "_" else: c)` -> `"a_c"`

**Subtasks:**
1. Iterate characters using `while i < s.len()`
2. Apply callback to each character
3. Collect results via `StringBuilder`
4. Add docstring and examples

**Dependencies:** None

---

### Task 5: `tr(from, to)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 3/5
**Description:** Character transliteration. Each character in `from` is replaced with the corresponding character in `to`. Characters not in `from` pass through unchanged. If `to` is shorter than `from`, the last character of `to` is used for remaining `from` characters.
**Signature:** `fn tr(s: text, from: text, to: text) -> text`
**Examples:**
- `tr("hello", "el", "ip")` -> `"hippo"`
- `tr("abc", "abc", "xyz")` -> `"xyz"`

**Subtasks:**
1. Build character mapping from `from` -> `to` (iterate in parallel)
2. Handle `to` shorter than `from` (extend with last char)
3. Iterate input, apply mapping via lookup
4. Collect via `StringBuilder`
5. Add docstring and examples

**Dependencies:** None

---

### Task 6: `split_n(sep, n)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Split string with a maximum of N parts. After N-1 splits, the remainder goes into the last part.
**Signature:** `fn split_n(s: text, sep: text, n: i64) -> [text]`
**Examples:**
- `split_n("a.b.c.d", ".", 3)` -> `["a", "b", "c.d"]`
- `split_n("a.b", ".", 5)` -> `["a", "b"]`

**Subtasks:**
1. Track split count, stop splitting at n-1
2. Append remainder as final element
3. Handle edge cases (n <= 0, n == 1, sep not found)
4. Add docstring and examples

**Dependencies:** None

---

### Task 7: `contains_any(chars)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 1/5
**Description:** Check if string contains any character from the given character set.
**Signature:** `fn contains_any(s: text, chars: text) -> bool`
**Examples:**
- `contains_any("hello", "aeiou")` -> `true`
- `contains_any("rhythm", "aeiou")` -> `false`

**Subtasks:**
1. Iterate each char of `s`
2. For each, check if it appears in `chars`
3. Return true on first match, false if none found
4. Add docstring and examples

**Dependencies:** None

---

### Task 8: `cut(sep)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Cut string at the first occurrence of separator. Returns a tuple `(before, after, found)`. Modeled after Go's `strings.Cut`.
**Signature:** `fn cut(s: text, sep: text) -> (text, text, bool)`
**Examples:**
- `cut("hello=world", "=")` -> `("hello", "world", true)`
- `cut("hello", "=")` -> `("hello", "", false)`

**Subtasks:**
1. Find first occurrence of `sep` in `s`
2. If found, split into before/after, return with `true`
3. If not found, return `(s, "", false)`
4. Add docstring and examples

**Dependencies:** None

---

### Task 9: `gsub(pattern, fn)` — Library function
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 3/5
**Description:** Replace all occurrences of a literal pattern using a callback function. The callback receives each match and returns its replacement. (Literal pattern matching only; regex support is out of scope for P1.)
**Signature:** `fn gsub(s: text, pattern: text, f: fn(text) -> text) -> text`
**Examples:**
- `gsub("hello world", "o", \m: m.to_upper())` -> `"hellO wOrld"`
- `gsub("aabbcc", "bb", \m: "XX")` -> `"aaXXcc"`

**Subtasks:**
1. Scan for non-overlapping occurrences of `pattern`
2. For each match, call `f(match)` to get replacement
3. Collect non-matching segments and replacements via `StringBuilder`
4. Handle edge cases (empty pattern, pattern not found)
5. Add docstring and examples

**Dependencies:** None

---

## Task 0: Extract shared `_split_words()` helper
**File:** `src/lib/common/text_advanced.spl`
**Difficulty:** 2/5
**Description:** Extract the word-splitting logic used by `to_snake_case` (and needed by Tasks 1-3) into a reusable `_split_words(text) -> [text]` private helper. Splits on: uppercase transitions, underscores, spaces, hyphens.

**Dependencies:** None (prerequisite for Tasks 1-3)

---

## Dependency DAG

```
Task 0: _split_words() helper
  ├── Task 1: to_kebab_case()      [depends on Task 0]
  ├── Task 2: to_pascal_case()     [depends on Task 0]
  └── Task 3: to_screaming_snake() [depends on Task 0, existing to_snake_case]

Task 4: chars_map(fn)              [independent]
Task 5: tr(from, to)               [independent]
Task 6: split_n(sep, n)            [independent]
Task 7: contains_any(chars)        [independent]
Task 8: cut(sep)                   [independent]
Task 9: gsub(pattern, fn)          [independent]
```

**Parallel tracks:**
- Track A (case conversions): Task 0 -> Tasks 1, 2, 3
- Track B (independent): Tasks 4, 5, 6, 7, 8, 9 (all parallelizable)

---

## Re-export Integration

After implementation, add new functions to the re-export list in `src/lib/common/text.spl` (line 418) alongside existing re-exports from `text_advanced`.

---

## Difficulty Summary

| Task | Method | Difficulty | Rationale |
|------|--------|------------|-----------|
| 0 | `_split_words()` | 2/5 | Refactor of existing logic |
| 1 | `to_kebab_case()` | 2/5 | Follows `to_snake_case` pattern |
| 2 | `to_pascal_case()` | 2/5 | Follows `to_camel_case` pattern |
| 3 | `to_screaming_snake()` | 2/5 | Trivial: `to_snake_case` + uppercase |
| 4 | `chars_map(fn)` | 2/5 | Simple iteration with callback |
| 5 | `tr(from, to)` | 3/5 | Character mapping logic, edge cases |
| 6 | `split_n(sep, n)` | 2/5 | Straightforward split with counter |
| 7 | `contains_any(chars)` | 1/5 | Nested char loop |
| 8 | `cut(sep)` | 2/5 | Single find + slice |
| 9 | `gsub(pattern, fn)` | 3/5 | Non-overlapping scan with callback |

No task is rated >= 4, so no splitting is required.

---

## Estimated Effort

- Total: ~10 tasks (including Task 0)
- Average difficulty: 2.1/5
- Estimated implementation time: 2-3 hours
- Testing: 1-2 hours (one spec file covering all 9 methods)

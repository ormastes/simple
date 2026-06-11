# String Core Coverage Specification

> Comprehensive branch-coverage tests for `src/lib/common/string_core.spl`. Exercises every exported function with inputs that trigger BOTH sides of every if/elif/else guard, targeting 90%+ branch coverage.

<!-- sdn-diagram:id=string_core_basic_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_basic_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_basic_coverage_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_basic_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 264 | 264 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Coverage Specification

Comprehensive branch-coverage tests for `src/lib/common/string_core.spl`. Exercises every exported function with inputs that trigger BOTH sides of every if/elif/else guard, targeting 90%+ branch coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/string_core_basic_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch-coverage tests for `src/lib/common/string_core.spl`.
Exercises every exported function with inputs that trigger BOTH sides of
every if/elif/else guard, targeting 90%+ branch coverage.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Branch coverage | Every conditional evaluates to both true and false |
| Edge cases | Empty strings, single chars, boundary indices |
| ASCII helpers | char_code_inline / char_from_code_inline lookup tables |

## Behavior

- All functions are pure (no side-effects)
- Bounds-checking functions clamp or return empty on invalid input
- ASCII helpers return 0 / "" for unknown input

## Scenarios

### string_core - Basic Operations

#### str_len

#### returns length of normal string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_len("hello")).to_equal(5)
```

</details>

#### returns 0 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_len("")).to_equal(0)
```

</details>

#### returns 1 for single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_len("x")).to_equal(1)
```

</details>

#### counts spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_len("a b")).to_equal(3)
```

</details>

#### str_concat

#### joins two non-empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_concat("hello", " world")).to_equal("hello world")
```

</details>

#### joins empty with non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_concat("", "test")).to_equal("test")
```

</details>

#### joins non-empty with empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_concat("test", "")).to_equal("test")
```

</details>

#### joins two empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_concat("", "")).to_equal("")
```

</details>

#### str_eq

#### returns true for equal strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_eq("hello", "hello")).to_equal(true)
```

</details>

#### returns false for different strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_eq("hello", "world")).to_equal(false)
```

</details>

#### returns true for two empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_eq("", "")).to_equal(true)
```

</details>

#### returns false for empty vs non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_eq("", "a")).to_equal(false)
```

</details>

#### is case-sensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_eq("Hello", "hello")).to_equal(false)
```

</details>

### string_core - Slicing and Access

#### str_slice

#### extracts full string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_slice("hello", 0, 5)).to_equal("hello")
```

</details>

#### extracts middle portion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_slice("hello", 1, 4)).to_equal("ell")
```

</details>

#### extracts single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_slice("hello", 0, 1)).to_equal("h")
```

</details>

#### extracts last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_slice("hello", 4, 5)).to_equal("o")
```

</details>

#### returns empty for equal indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_slice("hello", 2, 2)).to_equal("")
```

</details>

#### str_char_at

#### returns character at valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", 0)).to_equal("h")
```

</details>

#### returns last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", 4)).to_equal("o")
```

</details>

#### returns middle character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("abcde", 2)).to_equal("c")
```

</details>

#### returns empty for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", -1)).to_equal("")
```

</details>

#### returns empty for large negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", -100)).to_equal("")
```

</details>

#### returns empty for index equal to length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", 5)).to_equal("")
```

</details>

#### returns empty for index beyond length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("hello", 10)).to_equal("")
```

</details>

#### returns empty for empty string at index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("", 0)).to_equal("")
```

</details>

#### handles single-char string at index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("x", 0)).to_equal("x")
```

</details>

#### handles single-char string at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_char_at("x", 1)).to_equal("")
```

</details>

#### str_safe_slice

#### returns full string for valid range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", 0, 5)).to_equal("hello")
```

</details>

#### clamps negative start to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", -5, 3)).to_equal("hel")
```

</details>

#### clamps end beyond length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", 0, 100)).to_equal("hello")
```

</details>

#### clamps both start and end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", -10, 100)).to_equal("hello")
```

</details>

#### returns empty when start equals end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", 3, 3)).to_equal("")
```

</details>

#### returns empty when start exceeds end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", 4, 2)).to_equal("")
```

</details>

#### extracts middle portion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("hello", 1, 4)).to_equal("ell")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("", 0, 0)).to_equal("")
```

</details>

#### handles empty string with out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("", -1, 5)).to_equal("")
```

</details>

#### handles start at 0 with end clamped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("ab", 0, 10)).to_equal("ab")
```

</details>

#### handles start negative with end at length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_safe_slice("abc", -3, 3)).to_equal("abc")
```

</details>

### string_core - Search Operations

#### str_contains

#### finds substring present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_contains("hello world", "world")).to_equal(true)
```

</details>

#### returns false for missing substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_contains("hello world", "xyz")).to_equal(false)
```

</details>

#### finds empty needle in any string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_contains("hello", "")).to_equal(true)
```

</details>

#### finds string in itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_contains("abc", "abc")).to_equal(true)
```

</details>

#### handles empty haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_contains("", "a")).to_equal(false)
```

</details>

#### str_starts_with

#### returns true for matching prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_starts_with("hello", "hel")).to_equal(true)
```

</details>

#### returns false for non-matching prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_starts_with("hello", "llo")).to_equal(false)
```

</details>

#### returns true for empty prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_starts_with("hello", "")).to_equal(true)
```

</details>

#### returns true for exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_starts_with("hello", "hello")).to_equal(true)
```

</details>

#### returns false when prefix longer than string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_starts_with("hi", "hello")).to_equal(false)
```

</details>

#### str_ends_with

#### returns true for matching suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_ends_with("hello", "llo")).to_equal(true)
```

</details>

#### returns false for non-matching suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_ends_with("hello", "hel")).to_equal(false)
```

</details>

#### returns true for empty suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_ends_with("hello", "")).to_equal(true)
```

</details>

#### returns true for exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_ends_with("hello", "hello")).to_equal(true)
```

</details>

#### str_index_of

#### finds first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hello", "l")).to_equal(2)
```

</details>

#### finds substring at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hello", "hel")).to_equal(0)
```

</details>

#### finds substring at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hello", "lo")).to_equal(3)
```

</details>

#### returns -1 for missing substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hello", "xyz")).to_equal(-1)
```

</details>

#### returns -1 for needle longer than haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hi", "hello")).to_equal(-1)
```

</details>

#### finds empty needle at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("hello", "")).to_equal(0)
```

</details>

#### returns -1 for empty haystack with non-empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_index_of("", "a")).to_equal(-1)
```

</details>

#### str_last_index_of

#### finds last occurrence with duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("hello", "l")).to_equal(3)
```

</details>

#### finds last occurrence at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("abcabc", "c")).to_equal(5)
```

</details>

#### finds last occurrence at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("aaa", "a")).to_equal(2)
```

</details>

#### returns -1 for missing substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("hello", "xyz")).to_equal(-1)
```

</details>

#### finds single occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("hello", "o")).to_equal(4)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("", "a")).to_equal(-1)
```

</details>

#### finds multi-char pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("abab", "ab")).to_equal(2)
```

</details>

#### finds pattern at very end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_last_index_of("xyzabc", "abc")).to_equal(3)
```

</details>

### string_core - Whitespace Trimming

#### is_whitespace_char

#### identifies space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char(" ")).to_equal(true)
```

</details>

#### identifies tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\t")).to_equal(true)
```

</details>

#### identifies newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\n")).to_equal(true)
```

</details>

#### identifies carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("\r")).to_equal(true)
```

</details>

#### rejects letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("a")).to_equal(false)
```

</details>

#### rejects digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char("0")).to_equal(false)
```

</details>

#### rejects punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_whitespace_char(".")).to_equal(false)
```

</details>

#### str_trim

#### removes both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim("  hello  ")).to_equal("hello")
```

</details>

#### removes tabs and newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim("\thello\n")).to_equal("hello")
```

</details>

#### returns same when no whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim("hello")).to_equal("hello")
```

</details>

#### returns empty for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim("   ")).to_equal("")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim("")).to_equal("")
```

</details>

#### str_trim_left

#### removes leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("  hello")).to_equal("hello")
```

</details>

#### removes leading tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("\thello")).to_equal("hello")
```

</details>

#### removes mixed leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left(" \t\nhello")).to_equal("hello")
```

</details>

#### preserves trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("hello  ")).to_equal("hello  ")
```

</details>

#### returns empty for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("   ")).to_equal("")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("")).to_equal("")
```

</details>

#### returns same when no leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("hello")).to_equal("hello")
```

</details>

#### handles single whitespace char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left(" ")).to_equal("")
```

</details>

#### handles single non-whitespace char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_left("a")).to_equal("a")
```

</details>

#### str_trim_right

#### removes trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello  ")).to_equal("hello")
```

</details>

#### removes trailing newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello\n")).to_equal("hello")
```

</details>

#### removes trailing tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello\t")).to_equal("hello")
```

</details>

#### removes trailing carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello\r")).to_equal("hello")
```

</details>

#### removes mixed trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello \t\n\r")).to_equal("hello")
```

</details>

#### preserves leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("  hello")).to_equal("  hello")
```

</details>

#### returns empty for whitespace-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("   ")).to_equal("")
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("")).to_equal("")
```

</details>

#### returns same when no trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_trim_right("hello")).to_equal("hello")
```

</details>

#### trim aliases

#### trim_whitespace delegates to str_trim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_whitespace("  hi  ")).to_equal("hi")
```

</details>

#### trim_left delegates to str_trim_left

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_left("  hi")).to_equal("hi")
```

</details>

#### trim_right delegates to str_trim_right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_right("hi  ")).to_equal("hi")
```

</details>

#### trim_field

#### trims when should_trim is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_field("  hello  ", true)).to_equal("hello")
```

</details>

#### preserves when should_trim is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_field("  hello  ", false)).to_equal("  hello  ")
```

</details>

#### handles empty field with trim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_field("", true)).to_equal("")
```

</details>

#### handles empty field without trim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(trim_field("", false)).to_equal("")
```

</details>

### string_core - Replacement

#### str_replace

#### replaces first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("hello", "l", "L")).to_equal("heLLo")
```

</details>

#### returns same when pattern not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("hello", "x", "X")).to_equal("hello")
```

</details>

#### replaces at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("hello", "h", "H")).to_equal("Hello")
```

</details>

#### replaces at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("hello", "o", "O")).to_equal("hellO")
```

</details>

#### replaces with longer string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("abc", "b", "BBB")).to_equal("aBBBc")
```

</details>

#### replaces with empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace("abc", "b", "")).to_equal("ac")
```

</details>

#### str_replace_all

#### replaces all occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("hello", "l", "L")).to_equal("heLLo")
```

</details>

#### replaces all in repeated pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("aaa", "a", "b")).to_equal("bbb")
```

</details>

#### returns same when pattern not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("hello", "x", "X")).to_equal("hello")
```

</details>

#### returns same for empty old_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("hello", "", "X")).to_equal("hello")
```

</details>

#### replaces adjacent occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("aabb", "a", "c")).to_equal("ccbb")
```

</details>

#### replaces with empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("abcabc", "b", "")).to_equal("acac")
```

</details>

#### replaces with longer string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("ab", "a", "xxx")).to_equal("xxxb")
```

</details>

#### handles pattern at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("abc", "a", "X")).to_equal("Xbc")
```

</details>

#### handles pattern at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("abc", "c", "X")).to_equal("abX")
```

</details>

#### handles single-char string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("a", "a", "b")).to_equal("b")
```

</details>

#### handles empty input string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("", "a", "b")).to_equal("")
```

</details>

#### handles idx == 0 case where match is at start of remaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_replace_all("aXaXa", "a", "b")).to_equal("bXbXb")
```

</details>

### string_core - Split and Join

#### str_split

#### splits by comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = str_split("a,b,c", ",")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("a")
expect(parts[1]).to_equal("b")
expect(parts[2]).to_equal("c")
```

</details>

#### splits by space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = str_split("hello world", " ")
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("hello")
```

</details>

#### returns single element when no delimiter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = str_split("hello", ",")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("hello")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = str_split("", ",")
expect(parts.len()).to_be_greater_than(0)
```

</details>

#### handles consecutive delimiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = str_split("a,,b", ",")
expect(parts.len()).to_equal(3)
```

</details>

#### str_join

#### joins with comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_join(["a", "b", "c"], ",")).to_equal("a,b,c")
```

</details>

#### joins single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_join(["a"], ",")).to_equal("a")
```

</details>

#### joins empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_join([], ",")).to_equal("")
```

</details>

#### joins with empty separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_join(["a", "b", "c"], "")).to_equal("abc")
```

</details>

#### joins with multi-char separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_join(["a", "b"], " - ")).to_equal("a - b")
```

</details>

### string_core - char_code_inline

#### whitespace characters

#### returns 32 for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(" ")).to_equal(32)
```

</details>

#### returns 10 for newline

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("\r")).to_equal(13)
```

</details>

#### punctuation

#### returns 33 for exclamation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("!")).to_equal(33)
```

</details>

#### returns 35 for hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("#")).to_equal(35)
```

</details>

#### returns 46 for period

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(".")).to_equal(46)
```

</details>

#### returns 44 for comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(",")).to_equal(44)
```

</details>

#### returns 45 for hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("-")).to_equal(45)
```

</details>

#### returns 95 for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("_")).to_equal(95)
```

</details>

#### returns 64 for at-sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("@")).to_equal(64)
```

</details>

#### returns 40 for open paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("(")).to_equal(40)
```

</details>

#### returns 41 for close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(")")).to_equal(41)
```

</details>

#### returns 91 for open bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("[")).to_equal(91)
```

</details>

#### returns 93 for close bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("]")).to_equal(93)
```

</details>

#### returns 123 for open brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("{")).to_equal(123)
```

</details>

#### returns 125 for close brace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("}")).to_equal(125)
```

</details>

#### returns 124 for pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("|")).to_equal(124)
```

</details>

#### returns 126 for tilde

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("~")).to_equal(126)
```

</details>

#### returns 94 for caret

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("^")).to_equal(94)
```

</details>

#### returns 36 for dollar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("$")).to_equal(36)
```

</details>

#### returns 37 for percent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("%")).to_equal(37)
```

</details>

#### returns 38 for ampersand

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("&")).to_equal(38)
```

</details>

#### returns 42 for asterisk

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("*")).to_equal(42)
```

</details>

#### returns 43 for plus

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("+")).to_equal(43)
```

</details>

#### returns 47 for slash

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("/")).to_equal(47)
```

</details>

#### returns 58 for colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(":")).to_equal(58)
```

</details>

#### returns 59 for semicolon

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(";")).to_equal(59)
```

</details>

#### returns 60 for less-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("<")).to_equal(60)
```

</details>

#### returns 61 for equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("=")).to_equal(61)
```

</details>

#### returns 62 for greater-than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline(">")).to_equal(62)
```

</details>

#### returns 39 for single quote

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("'")).to_equal(39)
```

</details>

#### digits

#### returns 48 for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("0")).to_equal(48)
```

</details>

#### returns 53 for 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("5")).to_equal(53)
```

</details>

#### returns 57 for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("9")).to_equal(57)
```

</details>

#### uppercase letters

#### returns 65 for A

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("A")).to_equal(65)
```

</details>

#### returns 77 for M

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("M")).to_equal(77)
```

</details>

#### returns 90 for Z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns 97 for a

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("a")).to_equal(97)
```

</details>

#### returns 109 for m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("m")).to_equal(109)
```

</details>

#### returns 122 for z

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("z")).to_equal(122)
```

</details>

#### unknown characters

#### returns 0 for unknown character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("")).to_equal(0)
```

</details>

#### question mark

#### returns 63 for question mark

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qm = char_from_code_inline(63)
expect(char_code_inline(qm)).to_equal(63)
```

</details>

### string_core - char_from_code_inline

#### whitespace codes

#### returns space for 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(32)).to_equal(" ")
```

</details>

#### returns newline for 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(10)).to_equal("\n")
```

</details>

#### returns tab for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(13)).to_equal("\r")
```

</details>

#### punctuation codes

#### returns exclamation for 33

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(33)).to_equal("!")
```

</details>

#### returns period for 46

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(46)).to_equal(".")
```

</details>

#### returns underscore for 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(95)).to_equal("_")
```

</details>

#### returns open paren for 40

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(40)).to_equal("(")
```

</details>

#### returns close paren for 41

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(41)).to_equal(")")
```

</details>

#### returns open bracket for 91

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(91)).to_equal("[")
```

</details>

#### returns close bracket for 93

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(93)).to_equal("]")
```

</details>

#### returns open brace for 123

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(123)).to_equal("{")
```

</details>

#### returns close brace for 125

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(125)).to_equal("}")
```

</details>

#### returns pipe for 124

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(124)).to_equal("|")
```

</details>

#### returns tilde for 126

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(126)).to_equal("~")
```

</details>

#### returns caret for 94

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(94)).to_equal("^")
```

</details>

#### returns hash for 35

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(35)).to_equal("#")
```

</details>

#### returns dollar for 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(36)).to_equal("$")
```

</details>

#### returns percent for 37

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(37)).to_equal("%")
```

</details>

#### returns ampersand for 38

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(38)).to_equal("&")
```

</details>

#### returns single quote for 39

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(39)).to_equal("'")
```

</details>

#### returns asterisk for 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(42)).to_equal("*")
```

</details>

#### returns plus for 43

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(43)).to_equal("+")
```

</details>

#### returns comma for 44

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(44)).to_equal(",")
```

</details>

#### returns hyphen for 45

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(45)).to_equal("-")
```

</details>

#### returns slash for 47

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(47)).to_equal("/")
```

</details>

#### returns colon for 58

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(58)).to_equal(":")
```

</details>

#### returns semicolon for 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(59)).to_equal(";")
```

</details>

#### returns less-than for 60

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(60)).to_equal("<")
```

</details>

#### returns equals for 61

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(61)).to_equal("=")
```

</details>

#### returns greater-than for 62

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(62)).to_equal(">")
```

</details>

#### returns at-sign for 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(64)).to_equal("@")
```

</details>

#### digit codes

#### returns 0 for 48

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(48)).to_equal("0")
```

</details>

#### returns 5 for 53

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(53)).to_equal("5")
```

</details>

#### returns 9 for 57

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(57)).to_equal("9")
```

</details>

#### uppercase letter codes

#### returns A for 65

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(65)).to_equal("A")
```

</details>

#### returns M for 77

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(77)).to_equal("M")
```

</details>

#### returns Z for 90

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(90)).to_equal("Z")
```

</details>

#### lowercase letter codes

#### returns a for 97

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(97)).to_equal("a")
```

</details>

#### returns m for 109

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(109)).to_equal("m")
```

</details>

#### returns z for 122

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(122)).to_equal("z")
```

</details>

#### unknown codes

#### returns empty for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(0)).to_equal("")
```

</details>

#### returns empty for 999

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(999)).to_equal("")
```

</details>

#### returns empty for negative code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(-1)).to_equal("")
```

</details>

#### returns empty for code 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(1)).to_equal("")
```

</details>

### string_core - Character Classification

#### is_alpha_char

#### returns true for lowercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for middle lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### returns true for middle uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### returns false for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("5")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### is_digit_char

#### returns true for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for middle digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns false for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### is_alnum_char

#### returns true for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### returns true for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("5")).to_equal(true)
```

</details>

#### returns false for space

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_alnum_char("_")).to_equal(false)
```

</details>

### string_core - Case Conversion

#### str_to_lower

#### converts all uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("HELLO")).to_equal("hello")
```

</details>

#### converts mixed case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("HeLLo")).to_equal("hello")
```

</details>

#### keeps already lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("hello")).to_equal("hello")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("")).to_equal("")
```

</details>

#### preserves digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("ABC123")).to_equal("abc123")
```

</details>

#### preserves punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("A.B-C")).to_equal("a.b-c")
```

</details>

#### handles single uppercase char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("A")).to_equal("a")
```

</details>

#### handles single lowercase char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_lower("a")).to_equal("a")
```

</details>

#### str_to_upper

#### converts all lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("hello")).to_equal("HELLO")
```

</details>

#### converts mixed case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("HeLLo")).to_equal("HELLO")
```

</details>

#### keeps already uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("HELLO")).to_equal("HELLO")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("")).to_equal("")
```

</details>

#### preserves digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("abc123")).to_equal("ABC123")
```

</details>

#### preserves punctuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("a.b-c")).to_equal("A.B-C")
```

</details>

#### handles single lowercase char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("a")).to_equal("A")
```

</details>

#### handles single uppercase char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_to_upper("A")).to_equal("A")
```

</details>

#### str_capitalize

#### capitalizes lowercase first char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("hello")).to_equal("Hello")
```

</details>

#### keeps uppercase first char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("Hello")).to_equal("Hello")
```

</details>

#### capitalizes all-uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("HELLO")).to_equal("HELLO")
```

</details>

#### returns empty for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("")).to_equal("")
```

</details>

#### capitalizes single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("a")).to_equal("A")
```

</details>

#### handles digit first char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize("1abc")).to_equal("1abc")
```

</details>

#### handles space first char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_capitalize(" hello")).to_equal(" hello")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 264 |
| Active scenarios | 264 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

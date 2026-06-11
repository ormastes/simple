# String Core Operations Specification

> Tests for string operations: basic ops, slicing, search, trimming, replacement, split/join, case conversion, manipulation, aliases, and round-trips.

<!-- sdn-diagram:id=string_core_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_ops_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 203 | 203 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Operations Specification

Tests for string operations: basic ops, slicing, search, trimming, replacement, split/join, case conversion, manipulation, aliases, and round-trips.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/01_unit/lib/common/string_core_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for string operations: basic ops, slicing, search, trimming,
replacement, split/join, case conversion, manipulation, aliases, and round-trips.

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

### string_core - Manipulation

#### str_reverse

#### reverses normal string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_reverse("hello")).to_equal("olleh")
```

</details>

#### reverses single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_reverse("a")).to_equal("a")
```

</details>

#### reverses empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_reverse("")).to_equal("")
```

</details>

#### reverses palindrome

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_reverse("aba")).to_equal("aba")
```

</details>

#### reverses two chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_reverse("ab")).to_equal("ba")
```

</details>

#### str_repeat

#### repeats multiple times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("ab", 3)).to_equal("ababab")
```

</details>

#### repeats once

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("x", 1)).to_equal("x")
```

</details>

#### repeats zero times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("x", 0)).to_equal("")
```

</details>

#### repeats empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("", 5)).to_equal("")
```

</details>

#### repeats multi-char string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_repeat("abc", 2)).to_equal("abcabc")
```

</details>

#### str_truncate

#### truncates long string with ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("hello world", 5)).to_equal("hello...")
```

</details>

#### returns same when within max_len

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("hello", 10)).to_equal("hello")
```

</details>

#### returns same when exactly max_len

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("hello", 5)).to_equal("hello")
```

</details>

#### truncates to 1 char with ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("hello", 1)).to_equal("h...")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("", 5)).to_equal("")
```

</details>

#### truncates to 0 chars with ellipsis

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_truncate("hello", 0)).to_equal("...")
```

</details>

#### str_pad_left

#### pads with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("42", 5, "0")).to_equal("00042")
```

</details>

#### pads with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("hi", 5, " ")).to_equal("   hi")
```

</details>

#### returns same when already at width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("hello", 5, " ")).to_equal("hello")
```

</details>

#### returns same when exceeds width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("hello", 3, " ")).to_equal("hello")
```

</details>

#### pads single char to width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("x", 3, "-")).to_equal("--x")
```

</details>

#### pads empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_left("", 3, ".")).to_equal("...")
```

</details>

#### str_pad_right

#### pads with zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("42", 5, "0")).to_equal("42000")
```

</details>

#### pads with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("hi", 5, " ")).to_equal("hi   ")
```

</details>

#### returns same when already at width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("hello", 5, " ")).to_equal("hello")
```

</details>

#### returns same when exceeds width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("hello", 3, " ")).to_equal("hello")
```

</details>

#### pads single char to width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("x", 3, "-")).to_equal("x--")
```

</details>

#### pads empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_pad_right("", 3, ".")).to_equal("...")
```

</details>

#### str_center

#### centers short string in wider field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_center("hi", 6)).to_equal("  hi  ")
```

</details>

#### returns same when string exceeds width

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_center("hello", 3)).to_equal("hello")
```

</details>

#### centers single char

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_center("x", 5)).to_equal("  x  ")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(str_center("", 4)).to_equal("    ")
```

</details>

### string_core - Compatibility Aliases

#### char_code alias

#### returns same as char_code_inline for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("A")).to_equal(65)
```

</details>

#### returns same as char_code_inline for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("0")).to_equal(48)
```

</details>

#### returns 0 for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code("")).to_equal(0)
```

</details>

#### char_from_code alias

#### returns same as char_from_code_inline for letter

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code(65)).to_equal("A")
```

</details>

#### returns same as char_from_code_inline for digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code(48)).to_equal("0")
```

</details>

#### returns empty for unknown code

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code(0)).to_equal("")
```

</details>

### string_core - Round-trip Tests

#### char_code round-trip

#### round-trips lowercase letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_inline("a")
val ch = char_from_code_inline(code)
expect(ch).to_equal("a")
```

</details>

#### round-trips uppercase letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_inline("Z")
val ch = char_from_code_inline(code)
expect(ch).to_equal("Z")
```

</details>

#### round-trips digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_inline("5")
val ch = char_from_code_inline(code)
expect(ch).to_equal("5")
```

</details>

#### round-trips space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = char_code_inline(" ")
val ch = char_from_code_inline(code)
expect(ch).to_equal(" ")
```

</details>

#### case conversion round-trip

#### to_lower then to_upper restores uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "HELLO"
val lower = str_to_lower(original)
val upper = str_to_upper(lower)
expect(upper).to_equal(original)
```

</details>

#### to_upper then to_lower restores lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "hello"
val upper = str_to_upper(original)
val lower = str_to_lower(upper)
expect(lower).to_equal(original)
```

</details>

#### trim + pad round-trip

#### trim removes what pad adds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val padded = str_pad_left("hi", 5, " ")
val trimmed = str_trim_left(padded)
expect(trimmed).to_equal("hi")
```

</details>

#### split + join round-trip

#### split then join restores original

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = "a,b,c"
val parts = str_split(original, ",")
val joined = str_join(parts, ",")
expect(joined).to_equal(original)
```

</details>

#### replace_all + index_of integration

#### replacement removes all occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = str_replace_all("abcabc", "a", "")
expect(str_index_of(result, "a")).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 203 |
| Active scenarios | 203 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

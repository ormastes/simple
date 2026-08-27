# String Core Operations Specification

> Purpose: Prove that string_core - Basic Operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 205 | 205 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Operations Specification

Purpose: Prove that string_core - Basic Operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-STRING-CORE |
| Category | Stdlib |
| Status | Implemented |
| Source | `test/unit/lib/common/string_core_ops_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that string_core - Basic Operations.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### string_core - Basic Operations

#### str_len

#### returns length of normal string

- returns length of normal string
- Verify: returns length of normal string
   - Expected: str_len("hello") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns length of normal string")
step("Verify: returns length of normal string")
# @req: REQ-LIB-COMMON-001
expect(str_len("hello")).to_equal(5)
```

</details>

#### returns 0 for empty string

- returns 0 for empty string
- Verify: returns 0 for empty string
   - Expected: str_len("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for empty string")
step("Verify: returns 0 for empty string")
expect(str_len("")).to_equal(0)
```

</details>

#### returns 1 for single character

- returns 1 for single character
- Verify: returns 1 for single character
   - Expected: str_len("x") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 1 for single character")
step("Verify: returns 1 for single character")
expect(str_len("x")).to_equal(1)
```

</details>

#### counts spaces

- counts spaces
- Verify: counts spaces
   - Expected: str_len("a b") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts spaces")
step("Verify: counts spaces")
expect(str_len("a b")).to_equal(3)
```

</details>

#### str_concat

#### joins two non-empty strings

- joins two non-empty strings
- Verify: joins two non-empty strings
   - Expected: str_concat("hello", " world") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins two non-empty strings")
step("Verify: joins two non-empty strings")
expect(str_concat("hello", " world")).to_equal("hello world")
```

</details>

#### joins empty with non-empty

- joins empty with non-empty
- Verify: joins empty with non-empty
   - Expected: str_concat("", "test") equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins empty with non-empty")
step("Verify: joins empty with non-empty")
expect(str_concat("", "test")).to_equal("test")
```

</details>

#### joins non-empty with empty

- joins non-empty with empty
- Verify: joins non-empty with empty
   - Expected: str_concat("test", "") equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins non-empty with empty")
step("Verify: joins non-empty with empty")
expect(str_concat("test", "")).to_equal("test")
```

</details>

#### joins two empty strings

- joins two empty strings
- Verify: joins two empty strings
   - Expected: str_concat("", "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins two empty strings")
step("Verify: joins two empty strings")
expect(str_concat("", "")).to_equal("")
```

</details>

#### str_eq

#### returns true for equal strings

- returns true for equal strings
- Verify: returns true for equal strings
   - Expected: str_eq("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for equal strings")
step("Verify: returns true for equal strings")
expect(str_eq("hello", "hello")).to_equal(true)
```

</details>

#### returns false for different strings

- returns false for different strings
- Verify: returns false for different strings
   - Expected: str_eq("hello", "world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for different strings")
step("Verify: returns false for different strings")
expect(str_eq("hello", "world")).to_equal(false)
```

</details>

#### returns true for two empty strings

- returns true for two empty strings
- Verify: returns true for two empty strings
   - Expected: str_eq("", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for two empty strings")
step("Verify: returns true for two empty strings")
expect(str_eq("", "")).to_equal(true)
```

</details>

#### returns false for empty vs non-empty

- returns false for empty vs non-empty
- Verify: returns false for empty vs non-empty
   - Expected: str_eq("", "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for empty vs non-empty")
step("Verify: returns false for empty vs non-empty")
expect(str_eq("", "a")).to_equal(false)
```

</details>

#### is case-sensitive

- is case-sensitive
- Verify: is case-sensitive
   - Expected: str_eq("Hello", "hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is case-sensitive")
step("Verify: is case-sensitive")
expect(str_eq("Hello", "hello")).to_equal(false)
```

</details>

### string_core - Slicing and Access

#### str_slice

#### extracts full string

- extracts full string
- Verify: extracts full string
   - Expected: str_slice("hello", 0, 5) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts full string")
step("Verify: extracts full string")
expect(str_slice("hello", 0, 5)).to_equal("hello")
```

</details>

#### extracts middle portion

- extracts middle portion
- Verify: extracts middle portion
   - Expected: str_slice("hello", 1, 4) equals `ell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts middle portion")
step("Verify: extracts middle portion")
expect(str_slice("hello", 1, 4)).to_equal("ell")
```

</details>

#### extracts single character

- extracts single character
- Verify: extracts single character
   - Expected: str_slice("hello", 0, 1) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts single character")
step("Verify: extracts single character")
expect(str_slice("hello", 0, 1)).to_equal("h")
```

</details>

#### extracts last character

- extracts last character
- Verify: extracts last character
   - Expected: str_slice("hello", 4, 5) equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts last character")
step("Verify: extracts last character")
expect(str_slice("hello", 4, 5)).to_equal("o")
```

</details>

#### returns empty for equal indices

- returns empty for equal indices
- Verify: returns empty for equal indices
   - Expected: str_slice("hello", 2, 2) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for equal indices")
step("Verify: returns empty for equal indices")
expect(str_slice("hello", 2, 2)).to_equal("")
```

</details>

#### str_char_at

#### returns character at valid index

- returns character at valid index
- Verify: returns character at valid index
   - Expected: str_char_at("hello", 0) equals `h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns character at valid index")
step("Verify: returns character at valid index")
expect(str_char_at("hello", 0)).to_equal("h")
```

</details>

#### returns last character

- returns last character
- Verify: returns last character
   - Expected: str_char_at("hello", 4) equals `o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns last character")
step("Verify: returns last character")
expect(str_char_at("hello", 4)).to_equal("o")
```

</details>

#### returns middle character

- returns middle character
- Verify: returns middle character
   - Expected: str_char_at("abcde", 2) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns middle character")
step("Verify: returns middle character")
expect(str_char_at("abcde", 2)).to_equal("c")
```

</details>

#### returns empty for negative index

- returns empty for negative index
- Verify: returns empty for negative index
   - Expected: str_char_at("hello", -1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative index")
step("Verify: returns empty for negative index")
expect(str_char_at("hello", -1)).to_equal("")
```

</details>

#### returns empty for large negative index

- returns empty for large negative index
- Verify: returns empty for large negative index
   - Expected: str_char_at("hello", -100) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for large negative index")
step("Verify: returns empty for large negative index")
expect(str_char_at("hello", -100)).to_equal("")
```

</details>

#### returns empty for index equal to length

- returns empty for index equal to length
- Verify: returns empty for index equal to length
   - Expected: str_char_at("hello", 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for index equal to length")
step("Verify: returns empty for index equal to length")
expect(str_char_at("hello", 5)).to_equal("")
```

</details>

#### returns empty for index beyond length

- returns empty for index beyond length
- Verify: returns empty for index beyond length
   - Expected: str_char_at("hello", 10) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for index beyond length")
step("Verify: returns empty for index beyond length")
expect(str_char_at("hello", 10)).to_equal("")
```

</details>

#### returns empty for empty string at index 0

- returns empty for empty string at index 0
- Verify: returns empty for empty string at index 0
   - Expected: str_char_at("", 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty string at index 0")
step("Verify: returns empty for empty string at index 0")
expect(str_char_at("", 0)).to_equal("")
```

</details>

#### handles single-char string at index 0

- handles single-char string at index 0
- Verify: handles single-char string at index 0
   - Expected: str_char_at("x", 0) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-char string at index 0")
step("Verify: handles single-char string at index 0")
expect(str_char_at("x", 0)).to_equal("x")
```

</details>

#### handles single-char string at index 1

- handles single-char string at index 1
- Verify: handles single-char string at index 1
   - Expected: str_char_at("x", 1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-char string at index 1")
step("Verify: handles single-char string at index 1")
expect(str_char_at("x", 1)).to_equal("")
```

</details>

#### str_safe_slice

#### returns full string for valid range

- returns full string for valid range
- Verify: returns full string for valid range
   - Expected: str_safe_slice("hello", 0, 5) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns full string for valid range")
step("Verify: returns full string for valid range")
expect(str_safe_slice("hello", 0, 5)).to_equal("hello")
```

</details>

#### clamps negative start to 0

- clamps negative start to 0
- Verify: clamps negative start to 0
   - Expected: str_safe_slice("hello", -5, 3) equals `hel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps negative start to 0")
step("Verify: clamps negative start to 0")
expect(str_safe_slice("hello", -5, 3)).to_equal("hel")
```

</details>

#### clamps end beyond length

- clamps end beyond length
- Verify: clamps end beyond length
   - Expected: str_safe_slice("hello", 0, 100) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps end beyond length")
step("Verify: clamps end beyond length")
expect(str_safe_slice("hello", 0, 100)).to_equal("hello")
```

</details>

#### clamps both start and end

- clamps both start and end
- Verify: clamps both start and end
   - Expected: str_safe_slice("hello", -10, 100) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps both start and end")
step("Verify: clamps both start and end")
expect(str_safe_slice("hello", -10, 100)).to_equal("hello")
```

</details>

#### returns empty when start equals end

- returns empty when start equals end
- Verify: returns empty when start equals end
   - Expected: str_safe_slice("hello", 3, 3) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when start equals end")
step("Verify: returns empty when start equals end")
expect(str_safe_slice("hello", 3, 3)).to_equal("")
```

</details>

#### returns empty when start exceeds end

- returns empty when start exceeds end
- Verify: returns empty when start exceeds end
   - Expected: str_safe_slice("hello", 4, 2) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty when start exceeds end")
step("Verify: returns empty when start exceeds end")
expect(str_safe_slice("hello", 4, 2)).to_equal("")
```

</details>

#### extracts middle portion

- extracts middle portion
- Verify: extracts middle portion
   - Expected: str_safe_slice("hello", 1, 4) equals `ell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts middle portion")
step("Verify: extracts middle portion")
expect(str_safe_slice("hello", 1, 4)).to_equal("ell")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_safe_slice("", 0, 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_safe_slice("", 0, 0)).to_equal("")
```

</details>

#### handles empty string with out-of-bounds

- handles empty string with out-of-bounds
- Verify: handles empty string with out-of-bounds
   - Expected: str_safe_slice("", -1, 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string with out-of-bounds")
step("Verify: handles empty string with out-of-bounds")
expect(str_safe_slice("", -1, 5)).to_equal("")
```

</details>

#### handles start at 0 with end clamped

- handles start at 0 with end clamped
- Verify: handles start at 0 with end clamped
   - Expected: str_safe_slice("ab", 0, 10) equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles start at 0 with end clamped")
step("Verify: handles start at 0 with end clamped")
expect(str_safe_slice("ab", 0, 10)).to_equal("ab")
```

</details>

#### handles start negative with end at length

- handles start negative with end at length
- Verify: handles start negative with end at length
   - Expected: str_safe_slice("abc", -3, 3) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles start negative with end at length")
step("Verify: handles start negative with end at length")
expect(str_safe_slice("abc", -3, 3)).to_equal("abc")
```

</details>

### string_core - Search Operations

#### str_contains

#### finds substring present

- finds substring present
- Verify: finds substring present
   - Expected: str_contains("hello world", "world") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds substring present")
step("Verify: finds substring present")
expect(str_contains("hello world", "world")).to_equal(true)
```

</details>

#### returns false for missing substring

- returns false for missing substring
- Verify: returns false for missing substring
   - Expected: str_contains("hello world", "xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for missing substring")
step("Verify: returns false for missing substring")
expect(str_contains("hello world", "xyz")).to_equal(false)
```

</details>

#### finds empty needle in any string

- finds empty needle in any string
- Verify: finds empty needle in any string
   - Expected: str_contains("hello", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds empty needle in any string")
step("Verify: finds empty needle in any string")
expect(str_contains("hello", "")).to_equal(true)
```

</details>

#### finds string in itself

- finds string in itself
- Verify: finds string in itself
   - Expected: str_contains("abc", "abc") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds string in itself")
step("Verify: finds string in itself")
expect(str_contains("abc", "abc")).to_equal(true)
```

</details>

#### handles empty haystack

- handles empty haystack
- Verify: handles empty haystack
   - Expected: str_contains("", "a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty haystack")
step("Verify: handles empty haystack")
expect(str_contains("", "a")).to_equal(false)
```

</details>

#### str_starts_with

#### returns true for matching prefix

- returns true for matching prefix
- Verify: returns true for matching prefix
   - Expected: str_starts_with("hello", "hel") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for matching prefix")
step("Verify: returns true for matching prefix")
expect(str_starts_with("hello", "hel")).to_equal(true)
```

</details>

#### returns false for non-matching prefix

- returns false for non-matching prefix
- Verify: returns false for non-matching prefix
   - Expected: str_starts_with("hello", "llo") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-matching prefix")
step("Verify: returns false for non-matching prefix")
expect(str_starts_with("hello", "llo")).to_equal(false)
```

</details>

#### returns true for empty prefix

- returns true for empty prefix
- Verify: returns true for empty prefix
   - Expected: str_starts_with("hello", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for empty prefix")
step("Verify: returns true for empty prefix")
expect(str_starts_with("hello", "")).to_equal(true)
```

</details>

#### returns true for exact match

- returns true for exact match
- Verify: returns true for exact match
   - Expected: str_starts_with("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for exact match")
step("Verify: returns true for exact match")
expect(str_starts_with("hello", "hello")).to_equal(true)
```

</details>

#### returns false when prefix longer than string

- returns false when prefix longer than string
- Verify: returns false when prefix longer than string
   - Expected: str_starts_with("hi", "hello") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when prefix longer than string")
step("Verify: returns false when prefix longer than string")
expect(str_starts_with("hi", "hello")).to_equal(false)
```

</details>

#### str_ends_with

#### returns true for matching suffix

- returns true for matching suffix
- Verify: returns true for matching suffix
   - Expected: str_ends_with("hello", "llo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for matching suffix")
step("Verify: returns true for matching suffix")
expect(str_ends_with("hello", "llo")).to_equal(true)
```

</details>

#### returns false for non-matching suffix

- returns false for non-matching suffix
- Verify: returns false for non-matching suffix
   - Expected: str_ends_with("hello", "hel") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-matching suffix")
step("Verify: returns false for non-matching suffix")
expect(str_ends_with("hello", "hel")).to_equal(false)
```

</details>

#### returns true for empty suffix

- returns true for empty suffix
- Verify: returns true for empty suffix
   - Expected: str_ends_with("hello", "") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for empty suffix")
step("Verify: returns true for empty suffix")
expect(str_ends_with("hello", "")).to_equal(true)
```

</details>

#### returns true for exact match

- returns true for exact match
- Verify: returns true for exact match
   - Expected: str_ends_with("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for exact match")
step("Verify: returns true for exact match")
expect(str_ends_with("hello", "hello")).to_equal(true)
```

</details>

#### str_index_of

#### finds first occurrence

- finds first occurrence
- Verify: finds first occurrence
   - Expected: str_index_of("hello", "l") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds first occurrence")
step("Verify: finds first occurrence")
expect(str_index_of("hello", "l")).to_equal(2)
```

</details>

#### finds substring at start

- finds substring at start
- Verify: finds substring at start
   - Expected: str_index_of("hello", "hel") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds substring at start")
step("Verify: finds substring at start")
expect(str_index_of("hello", "hel")).to_equal(0)
```

</details>

#### finds substring at end

- finds substring at end
- Verify: finds substring at end
   - Expected: str_index_of("hello", "lo") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds substring at end")
step("Verify: finds substring at end")
expect(str_index_of("hello", "lo")).to_equal(3)
```

</details>

#### returns -1 for missing substring

- returns -1 for missing substring
- Verify: returns -1 for missing substring
   - Expected: str_index_of("hello", "xyz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for missing substring")
step("Verify: returns -1 for missing substring")
expect(str_index_of("hello", "xyz")).to_equal(-1)
```

</details>

#### returns -1 for needle longer than haystack

- returns -1 for needle longer than haystack
- Verify: returns -1 for needle longer than haystack
   - Expected: str_index_of("hi", "hello") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for needle longer than haystack")
step("Verify: returns -1 for needle longer than haystack")
expect(str_index_of("hi", "hello")).to_equal(-1)
```

</details>

#### finds empty needle at 0

- finds empty needle at 0
- Verify: finds empty needle at 0
   - Expected: str_index_of("hello", "") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds empty needle at 0")
step("Verify: finds empty needle at 0")
expect(str_index_of("hello", "")).to_equal(0)
```

</details>

#### returns -1 for empty haystack with non-empty needle

- returns -1 for empty haystack with non-empty needle
- Verify: returns -1 for empty haystack with non-empty needle
   - Expected: str_index_of("", "a") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for empty haystack with non-empty needle")
step("Verify: returns -1 for empty haystack with non-empty needle")
expect(str_index_of("", "a")).to_equal(-1)
```

</details>

#### str_last_index_of

#### finds last occurrence with duplicates

- finds last occurrence with duplicates
- Verify: finds last occurrence with duplicates
   - Expected: str_last_index_of("hello", "l") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds last occurrence with duplicates")
step("Verify: finds last occurrence with duplicates")
expect(str_last_index_of("hello", "l")).to_equal(3)
```

</details>

#### finds last occurrence at end

- finds last occurrence at end
- Verify: finds last occurrence at end
   - Expected: str_last_index_of("abcabc", "c") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds last occurrence at end")
step("Verify: finds last occurrence at end")
expect(str_last_index_of("abcabc", "c")).to_equal(5)
```

</details>

#### finds last occurrence at start

- finds last occurrence at start
- Verify: finds last occurrence at start
   - Expected: str_last_index_of("aaa", "a") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds last occurrence at start")
step("Verify: finds last occurrence at start")
expect(str_last_index_of("aaa", "a")).to_equal(2)
```

</details>

#### returns -1 for missing substring

- returns -1 for missing substring
- Verify: returns -1 for missing substring
   - Expected: str_last_index_of("hello", "xyz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 for missing substring")
step("Verify: returns -1 for missing substring")
expect(str_last_index_of("hello", "xyz")).to_equal(-1)
```

</details>

#### finds single occurrence

- finds single occurrence
- Verify: finds single occurrence
   - Expected: str_last_index_of("hello", "o") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds single occurrence")
step("Verify: finds single occurrence")
expect(str_last_index_of("hello", "o")).to_equal(4)
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_last_index_of("", "a") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_last_index_of("", "a")).to_equal(-1)
```

</details>

#### finds multi-char pattern

- finds multi-char pattern
- Verify: finds multi-char pattern
   - Expected: str_last_index_of("abab", "ab") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds multi-char pattern")
step("Verify: finds multi-char pattern")
expect(str_last_index_of("abab", "ab")).to_equal(2)
```

</details>

#### finds pattern at very end

- finds pattern at very end
- Verify: finds pattern at very end
   - Expected: str_last_index_of("xyzabc", "abc") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds pattern at very end")
step("Verify: finds pattern at very end")
expect(str_last_index_of("xyzabc", "abc")).to_equal(3)
```

</details>

### string_core - Whitespace Trimming

#### is_whitespace_char

#### identifies space

- identifies space
- Verify: identifies space
   - Expected: is_whitespace_char(" ") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies space")
step("Verify: identifies space")
expect(is_whitespace_char(" ")).to_equal(true)
```

</details>

#### identifies tab

- identifies tab
- Verify: identifies tab
   - Expected: is_whitespace_char("\t") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies tab")
step("Verify: identifies tab")
expect(is_whitespace_char("\t")).to_equal(true)
```

</details>

#### identifies newline

- identifies newline
- Verify: identifies newline
   - Expected: is_whitespace_char("\n") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies newline")
step("Verify: identifies newline")
expect(is_whitespace_char("\n")).to_equal(true)
```

</details>

#### identifies carriage return

- identifies carriage return
- Verify: identifies carriage return
   - Expected: is_whitespace_char("\r") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies carriage return")
step("Verify: identifies carriage return")
expect(is_whitespace_char("\r")).to_equal(true)
```

</details>

#### rejects letter

- rejects letter
- Verify: rejects letter
   - Expected: is_whitespace_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects letter")
step("Verify: rejects letter")
expect(is_whitespace_char("a")).to_equal(false)
```

</details>

#### rejects digit

- rejects digit
- Verify: rejects digit
   - Expected: is_whitespace_char("0") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects digit")
step("Verify: rejects digit")
expect(is_whitespace_char("0")).to_equal(false)
```

</details>

#### rejects punctuation

- rejects punctuation
- Verify: rejects punctuation
   - Expected: is_whitespace_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects punctuation")
step("Verify: rejects punctuation")
expect(is_whitespace_char(".")).to_equal(false)
```

</details>

#### str_trim

#### removes both sides

- removes both sides
- Verify: removes both sides
   - Expected: str_trim("  hello  ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes both sides")
step("Verify: removes both sides")
expect(str_trim("  hello  ")).to_equal("hello")
```

</details>

#### removes tabs and newlines

- removes tabs and newlines
- Verify: removes tabs and newlines
   - Expected: str_trim("\thello\n") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes tabs and newlines")
step("Verify: removes tabs and newlines")
expect(str_trim("\thello\n")).to_equal("hello")
```

</details>

#### removes ASCII regex whitespace controls

- removes ASCII regex whitespace controls
- Verify: removes ASCII regex whitespace controls
   - Expected: str_trim("\u000Bhello\u000C") equals `hello`
   - Expected: ("\u000Bhello\u000C").trim() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes ASCII regex whitespace controls")
step("Verify: removes ASCII regex whitespace controls")
expect(str_trim("\u000Bhello\u000C")).to_equal("hello")
expect(("\u000Bhello\u000C").trim()).to_equal("hello")
```

</details>

#### returns same when no whitespace

- returns same when no whitespace
- Verify: returns same when no whitespace
   - Expected: str_trim("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when no whitespace")
step("Verify: returns same when no whitespace")
expect(str_trim("hello")).to_equal("hello")
```

</details>

#### returns empty for whitespace-only

- returns empty for whitespace-only
- Verify: returns empty for whitespace-only
   - Expected: str_trim("   ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for whitespace-only")
step("Verify: returns empty for whitespace-only")
expect(str_trim("   ")).to_equal("")
```

</details>

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: str_trim("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
step("Verify: returns empty for empty input")
expect(str_trim("")).to_equal("")
```

</details>

#### str_trim_left

#### removes leading spaces

- removes leading spaces
- Verify: removes leading spaces
   - Expected: str_trim_left("  hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes leading spaces")
step("Verify: removes leading spaces")
expect(str_trim_left("  hello")).to_equal("hello")
```

</details>

#### removes leading tab

- removes leading tab
- Verify: removes leading tab
   - Expected: str_trim_left("\thello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes leading tab")
step("Verify: removes leading tab")
expect(str_trim_left("\thello")).to_equal("hello")
```

</details>

#### removes mixed leading whitespace

- removes mixed leading whitespace
- Verify: removes mixed leading whitespace
   - Expected: str_trim_left(" \t\nhello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes mixed leading whitespace")
step("Verify: removes mixed leading whitespace")
expect(str_trim_left(" \t\nhello")).to_equal("hello")
```

</details>

#### preserves trailing whitespace

- preserves trailing whitespace
- Verify: preserves trailing whitespace
   - Expected: str_trim_left("hello  ") equals `hello  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves trailing whitespace")
step("Verify: preserves trailing whitespace")
expect(str_trim_left("hello  ")).to_equal("hello  ")
```

</details>

#### returns empty for whitespace-only

- returns empty for whitespace-only
- Verify: returns empty for whitespace-only
   - Expected: str_trim_left("   ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for whitespace-only")
step("Verify: returns empty for whitespace-only")
expect(str_trim_left("   ")).to_equal("")
```

</details>

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: str_trim_left("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
step("Verify: returns empty for empty input")
expect(str_trim_left("")).to_equal("")
```

</details>

#### returns same when no leading whitespace

- returns same when no leading whitespace
- Verify: returns same when no leading whitespace
   - Expected: str_trim_left("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when no leading whitespace")
step("Verify: returns same when no leading whitespace")
expect(str_trim_left("hello")).to_equal("hello")
```

</details>

#### handles single whitespace char

- handles single whitespace char
- Verify: handles single whitespace char
   - Expected: str_trim_left(" ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single whitespace char")
step("Verify: handles single whitespace char")
expect(str_trim_left(" ")).to_equal("")
```

</details>

#### handles single non-whitespace char

- handles single non-whitespace char
- Verify: handles single non-whitespace char
   - Expected: str_trim_left("a") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single non-whitespace char")
step("Verify: handles single non-whitespace char")
expect(str_trim_left("a")).to_equal("a")
```

</details>

#### str_trim_right

#### removes trailing spaces

- removes trailing spaces
- Verify: removes trailing spaces
   - Expected: str_trim_right("hello  ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes trailing spaces")
step("Verify: removes trailing spaces")
expect(str_trim_right("hello  ")).to_equal("hello")
```

</details>

#### removes trailing newline

- removes trailing newline
- Verify: removes trailing newline
   - Expected: str_trim_right("hello\n") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes trailing newline")
step("Verify: removes trailing newline")
expect(str_trim_right("hello\n")).to_equal("hello")
```

</details>

#### removes trailing tab

- removes trailing tab
- Verify: removes trailing tab
   - Expected: str_trim_right("hello\t") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes trailing tab")
step("Verify: removes trailing tab")
expect(str_trim_right("hello\t")).to_equal("hello")
```

</details>

#### removes trailing carriage return

- removes trailing carriage return
- Verify: removes trailing carriage return
   - Expected: str_trim_right("hello\r") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes trailing carriage return")
step("Verify: removes trailing carriage return")
expect(str_trim_right("hello\r")).to_equal("hello")
```

</details>

#### removes mixed trailing whitespace

- removes mixed trailing whitespace
- Verify: removes mixed trailing whitespace
   - Expected: str_trim_right("hello \t\n\r") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes mixed trailing whitespace")
step("Verify: removes mixed trailing whitespace")
expect(str_trim_right("hello \t\n\r")).to_equal("hello")
```

</details>

#### preserves leading whitespace

- preserves leading whitespace
- Verify: preserves leading whitespace
   - Expected: str_trim_right("  hello") equals `  hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves leading whitespace")
step("Verify: preserves leading whitespace")
expect(str_trim_right("  hello")).to_equal("  hello")
```

</details>

#### returns empty for whitespace-only

- returns empty for whitespace-only
- Verify: returns empty for whitespace-only
   - Expected: str_trim_right("   ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for whitespace-only")
step("Verify: returns empty for whitespace-only")
expect(str_trim_right("   ")).to_equal("")
```

</details>

#### returns empty for empty input

- returns empty for empty input
- Verify: returns empty for empty input
   - Expected: str_trim_right("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty input")
step("Verify: returns empty for empty input")
expect(str_trim_right("")).to_equal("")
```

</details>

#### returns same when no trailing whitespace

- returns same when no trailing whitespace
- Verify: returns same when no trailing whitespace
   - Expected: str_trim_right("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when no trailing whitespace")
step("Verify: returns same when no trailing whitespace")
expect(str_trim_right("hello")).to_equal("hello")
```

</details>

#### trim aliases

#### trim_whitespace delegates to str_trim

- trim_whitespace delegates to str_trim
- Verify: trim_whitespace delegates to str_trim
   - Expected: trim_whitespace("  hi  ") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim_whitespace delegates to str_trim")
step("Verify: trim_whitespace delegates to str_trim")
expect(trim_whitespace("  hi  ")).to_equal("hi")
```

</details>

#### trim_left delegates to str_trim_left

- trim_left delegates to str_trim_left
- Verify: trim_left delegates to str_trim_left
   - Expected: trim_left("  hi") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim_left delegates to str_trim_left")
step("Verify: trim_left delegates to str_trim_left")
expect(trim_left("  hi")).to_equal("hi")
```

</details>

#### trim_right delegates to str_trim_right

- trim_right delegates to str_trim_right
- Verify: trim_right delegates to str_trim_right
   - Expected: trim_right("hi  ") equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim_right delegates to str_trim_right")
step("Verify: trim_right delegates to str_trim_right")
expect(trim_right("hi  ")).to_equal("hi")
```

</details>

#### trim_field

#### trims when should_trim is true

- trims when should_trim is true
- Verify: trims when should_trim is true
   - Expected: trim_field("  hello  ", true) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims when should_trim is true")
step("Verify: trims when should_trim is true")
expect(trim_field("  hello  ", true)).to_equal("hello")
```

</details>

#### preserves when should_trim is false

- preserves when should_trim is false
- Verify: preserves when should_trim is false
   - Expected: trim_field("  hello  ", false) equals `  hello  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves when should_trim is false")
step("Verify: preserves when should_trim is false")
expect(trim_field("  hello  ", false)).to_equal("  hello  ")
```

</details>

#### handles empty field with trim

- handles empty field with trim
- Verify: handles empty field with trim
   - Expected: trim_field("", true) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty field with trim")
step("Verify: handles empty field with trim")
expect(trim_field("", true)).to_equal("")
```

</details>

#### handles empty field without trim

- handles empty field without trim
- Verify: handles empty field without trim
   - Expected: trim_field("", false) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty field without trim")
step("Verify: handles empty field without trim")
expect(trim_field("", false)).to_equal("")
```

</details>

### string_core - Replacement

#### str_replace

#### replaces first occurrence

- replaces first occurrence
- Verify: replaces first occurrence
   - Expected: str_replace("hello", "l", "L") equals `heLLo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces first occurrence")
step("Verify: replaces first occurrence")
expect(str_replace("hello", "l", "L")).to_equal("heLLo")
```

</details>

#### returns same when pattern not found

- returns same when pattern not found
- Verify: returns same when pattern not found
   - Expected: str_replace("hello", "x", "X") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when pattern not found")
step("Verify: returns same when pattern not found")
expect(str_replace("hello", "x", "X")).to_equal("hello")
```

</details>

#### replaces at start

- replaces at start
- Verify: replaces at start
   - Expected: str_replace("hello", "h", "H") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces at start")
step("Verify: replaces at start")
expect(str_replace("hello", "h", "H")).to_equal("Hello")
```

</details>

#### replaces at end

- replaces at end
- Verify: replaces at end
   - Expected: str_replace("hello", "o", "O") equals `hellO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces at end")
step("Verify: replaces at end")
expect(str_replace("hello", "o", "O")).to_equal("hellO")
```

</details>

#### replaces with longer string

- replaces with longer string
- Verify: replaces with longer string
   - Expected: str_replace("abc", "b", "BBB") equals `aBBBc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces with longer string")
step("Verify: replaces with longer string")
expect(str_replace("abc", "b", "BBB")).to_equal("aBBBc")
```

</details>

#### replaces with empty string

- replaces with empty string
- Verify: replaces with empty string
   - Expected: str_replace("abc", "b", "") equals `ac`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces with empty string")
step("Verify: replaces with empty string")
expect(str_replace("abc", "b", "")).to_equal("ac")
```

</details>

#### str_replace_all

#### replaces all occurrences

- replaces all occurrences
- Verify: replaces all occurrences
   - Expected: str_replace_all("hello", "l", "L") equals `heLLo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces all occurrences")
step("Verify: replaces all occurrences")
expect(str_replace_all("hello", "l", "L")).to_equal("heLLo")
```

</details>

#### replaces all in repeated pattern

- replaces all in repeated pattern
- Verify: replaces all in repeated pattern
   - Expected: str_replace_all("aaa", "a", "b") equals `bbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces all in repeated pattern")
step("Verify: replaces all in repeated pattern")
expect(str_replace_all("aaa", "a", "b")).to_equal("bbb")
```

</details>

#### returns same when pattern not found

- returns same when pattern not found
- Verify: returns same when pattern not found
   - Expected: str_replace_all("hello", "x", "X") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when pattern not found")
step("Verify: returns same when pattern not found")
expect(str_replace_all("hello", "x", "X")).to_equal("hello")
```

</details>

#### returns same for empty old_val

- returns same for empty old_val
- Verify: returns same for empty old_val
   - Expected: str_replace_all("hello", "", "X") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same for empty old_val")
step("Verify: returns same for empty old_val")
expect(str_replace_all("hello", "", "X")).to_equal("hello")
```

</details>

#### replaces adjacent occurrences

- replaces adjacent occurrences
- Verify: replaces adjacent occurrences
   - Expected: str_replace_all("aabb", "a", "c") equals `ccbb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces adjacent occurrences")
step("Verify: replaces adjacent occurrences")
expect(str_replace_all("aabb", "a", "c")).to_equal("ccbb")
```

</details>

#### replaces with empty string

- replaces with empty string
- Verify: replaces with empty string
   - Expected: str_replace_all("abcabc", "b", "") equals `acac`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces with empty string")
step("Verify: replaces with empty string")
expect(str_replace_all("abcabc", "b", "")).to_equal("acac")
```

</details>

#### replaces with longer string

- replaces with longer string
- Verify: replaces with longer string
   - Expected: str_replace_all("ab", "a", "xxx") equals `xxxb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces with longer string")
step("Verify: replaces with longer string")
expect(str_replace_all("ab", "a", "xxx")).to_equal("xxxb")
```

</details>

#### handles pattern at start

- handles pattern at start
- Verify: handles pattern at start
   - Expected: str_replace_all("abc", "a", "X") equals `Xbc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles pattern at start")
step("Verify: handles pattern at start")
expect(str_replace_all("abc", "a", "X")).to_equal("Xbc")
```

</details>

#### handles pattern at end

- handles pattern at end
- Verify: handles pattern at end
   - Expected: str_replace_all("abc", "c", "X") equals `abX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles pattern at end")
step("Verify: handles pattern at end")
expect(str_replace_all("abc", "c", "X")).to_equal("abX")
```

</details>

#### handles single-char string

- handles single-char string
- Verify: handles single-char string
   - Expected: str_replace_all("a", "a", "b") equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single-char string")
step("Verify: handles single-char string")
expect(str_replace_all("a", "a", "b")).to_equal("b")
```

</details>

#### handles empty input string

- handles empty input string
- Verify: handles empty input string
   - Expected: str_replace_all("", "a", "b") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty input string")
step("Verify: handles empty input string")
expect(str_replace_all("", "a", "b")).to_equal("")
```

</details>

#### handles idx == 0 case where match is at start of remaining

- handles idx == 0 case where match is at start of remaining
- Verify: handles idx == 0 case where match is at start of remaining
   - Expected: str_replace_all("aXaXa", "a", "b") equals `bXbXb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles idx == 0 case where match is at start of remaining")
step("Verify: handles idx == 0 case where match is at start of remaining")
expect(str_replace_all("aXaXa", "a", "b")).to_equal("bXbXb")
```

</details>

### string_core - Split and Join

#### str_split

#### splits by comma

- splits by comma
- Verify: splits by comma
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `a`
   - Expected: parts[1] equals `b`
   - Expected: parts[2] equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits by comma")
step("Verify: splits by comma")
val parts = str_split("a,b,c", ",")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("a")
expect(parts[1]).to_equal("b")
expect(parts[2]).to_equal("c")
```

</details>

#### splits by space

- splits by space
- Verify: splits by space
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits by space")
step("Verify: splits by space")
val parts = str_split("hello world", " ")
expect(parts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(parts[0]).to_equal("hello")
```

</details>

#### returns single element when no delimiter

- returns single element when no delimiter
- Verify: returns single element when no delimiter
   - Expected: parts.len() equals `1`
   - Expected: parts[0] equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single element when no delimiter")
step("Verify: returns single element when no delimiter")
val parts = str_split("hello", ",")
expect(parts.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(parts[0]).to_equal("hello")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
val parts = str_split("", ",")
expect(parts.len()).to_be_greater_than(0)
```

</details>

#### handles consecutive delimiters

- handles consecutive delimiters
- Verify: handles consecutive delimiters
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles consecutive delimiters")
step("Verify: handles consecutive delimiters")
val parts = str_split("a,,b", ",")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### str_join

#### joins with comma

- joins with comma
- Verify: joins with comma
   - Expected: str_join(["a", "b", "c"], ",") equals `a,b,c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins with comma")
step("Verify: joins with comma")
expect(str_join(["a", "b", "c"], ",")).to_equal("a,b,c")
```

</details>

#### joins single element

- joins single element
- Verify: joins single element
   - Expected: str_join(["a"], ",") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins single element")
step("Verify: joins single element")
expect(str_join(["a"], ",")).to_equal("a")
```

</details>

#### joins empty array

- joins empty array
- Verify: joins empty array
   - Expected: str_join([], ",") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins empty array")
step("Verify: joins empty array")
expect(str_join([], ",")).to_equal("")
```

</details>

#### joins with empty separator

- joins with empty separator
- Verify: joins with empty separator
   - Expected: str_join(["a", "b", "c"], "") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins with empty separator")
step("Verify: joins with empty separator")
expect(str_join(["a", "b", "c"], "")).to_equal("abc")
```

</details>

#### joins with multi-char separator

- joins with multi-char separator
- Verify: joins with multi-char separator
   - Expected: str_join(["a", "b"], " - ") equals `a - b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins with multi-char separator")
step("Verify: joins with multi-char separator")
expect(str_join(["a", "b"], " - ")).to_equal("a - b")
```

</details>

### string_core - Case Conversion

#### str_to_lower

#### converts all uppercase

- converts all uppercase
- Verify: converts all uppercase
   - Expected: str_to_lower("HELLO") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all uppercase")
step("Verify: converts all uppercase")
expect(str_to_lower("HELLO")).to_equal("hello")
```

</details>

#### converts mixed case

- converts mixed case
- Verify: converts mixed case
   - Expected: str_to_lower("HeLLo") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts mixed case")
step("Verify: converts mixed case")
expect(str_to_lower("HeLLo")).to_equal("hello")
```

</details>

#### keeps already lowercase

- keeps already lowercase
- Verify: keeps already lowercase
   - Expected: str_to_lower("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps already lowercase")
step("Verify: keeps already lowercase")
expect(str_to_lower("hello")).to_equal("hello")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_to_lower("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_to_lower("")).to_equal("")
```

</details>

#### preserves digits

- preserves digits
- Verify: preserves digits
   - Expected: str_to_lower("ABC123") equals `abc123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves digits")
step("Verify: preserves digits")
expect(str_to_lower("ABC123")).to_equal("abc123")
```

</details>

#### preserves punctuation

- preserves punctuation
- Verify: preserves punctuation
   - Expected: str_to_lower("A.B-C") equals `a.b-c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves punctuation")
step("Verify: preserves punctuation")
expect(str_to_lower("A.B-C")).to_equal("a.b-c")
```

</details>

#### handles single uppercase char

- handles single uppercase char
- Verify: handles single uppercase char
   - Expected: str_to_lower("A") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single uppercase char")
step("Verify: handles single uppercase char")
expect(str_to_lower("A")).to_equal("a")
```

</details>

#### handles single lowercase char

- handles single lowercase char
- Verify: handles single lowercase char
   - Expected: str_to_lower("a") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single lowercase char")
step("Verify: handles single lowercase char")
expect(str_to_lower("a")).to_equal("a")
```

</details>

#### str_to_upper

#### converts all lowercase

- converts all lowercase
- Verify: converts all lowercase
   - Expected: str_to_upper("hello") equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts all lowercase")
step("Verify: converts all lowercase")
expect(str_to_upper("hello")).to_equal("HELLO")
```

</details>

#### converts mixed case

- converts mixed case
- Verify: converts mixed case
   - Expected: str_to_upper("HeLLo") equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts mixed case")
step("Verify: converts mixed case")
expect(str_to_upper("HeLLo")).to_equal("HELLO")
```

</details>

#### keeps already uppercase

- keeps already uppercase
- Verify: keeps already uppercase
   - Expected: str_to_upper("HELLO") equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps already uppercase")
step("Verify: keeps already uppercase")
expect(str_to_upper("HELLO")).to_equal("HELLO")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_to_upper("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_to_upper("")).to_equal("")
```

</details>

#### preserves digits

- preserves digits
- Verify: preserves digits
   - Expected: str_to_upper("abc123") equals `ABC123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves digits")
step("Verify: preserves digits")
expect(str_to_upper("abc123")).to_equal("ABC123")
```

</details>

#### preserves punctuation

- preserves punctuation
- Verify: preserves punctuation
   - Expected: str_to_upper("a.b-c") equals `A.B-C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves punctuation")
step("Verify: preserves punctuation")
expect(str_to_upper("a.b-c")).to_equal("A.B-C")
```

</details>

#### handles single lowercase char

- handles single lowercase char
- Verify: handles single lowercase char
   - Expected: str_to_upper("a") equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single lowercase char")
step("Verify: handles single lowercase char")
expect(str_to_upper("a")).to_equal("A")
```

</details>

#### handles single uppercase char

- handles single uppercase char
- Verify: handles single uppercase char
   - Expected: str_to_upper("A") equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single uppercase char")
step("Verify: handles single uppercase char")
expect(str_to_upper("A")).to_equal("A")
```

</details>

#### str_capitalize

#### capitalizes lowercase first char

- capitalizes lowercase first char
- Verify: capitalizes lowercase first char
   - Expected: str_capitalize("hello") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capitalizes lowercase first char")
step("Verify: capitalizes lowercase first char")
expect(str_capitalize("hello")).to_equal("Hello")
```

</details>

#### keeps uppercase first char

- keeps uppercase first char
- Verify: keeps uppercase first char
   - Expected: str_capitalize("Hello") equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps uppercase first char")
step("Verify: keeps uppercase first char")
expect(str_capitalize("Hello")).to_equal("Hello")
```

</details>

#### capitalizes all-uppercase

- capitalizes all-uppercase
- Verify: capitalizes all-uppercase
   - Expected: str_capitalize("HELLO") equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capitalizes all-uppercase")
step("Verify: capitalizes all-uppercase")
expect(str_capitalize("HELLO")).to_equal("HELLO")
```

</details>

#### returns empty for empty string

- returns empty for empty string
- Verify: returns empty for empty string
   - Expected: str_capitalize("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for empty string")
step("Verify: returns empty for empty string")
expect(str_capitalize("")).to_equal("")
```

</details>

#### capitalizes single char

- capitalizes single char
- Verify: capitalizes single char
   - Expected: str_capitalize("a") equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("capitalizes single char")
step("Verify: capitalizes single char")
expect(str_capitalize("a")).to_equal("A")
```

</details>

#### handles digit first char

- handles digit first char
- Verify: handles digit first char
   - Expected: str_capitalize("1abc") equals `1abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles digit first char")
step("Verify: handles digit first char")
expect(str_capitalize("1abc")).to_equal("1abc")
```

</details>

#### handles space first char

- handles space first char
- Verify: handles space first char
   - Expected: str_capitalize(" hello") equals ` hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles space first char")
step("Verify: handles space first char")
expect(str_capitalize(" hello")).to_equal(" hello")
```

</details>

### string_core - Manipulation

#### str_reverse

#### reverses normal string

- reverses normal string
- Verify: reverses normal string
   - Expected: str_reverse("hello") equals `olleh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses normal string")
step("Verify: reverses normal string")
expect(str_reverse("hello")).to_equal("olleh")
```

</details>

#### reverses single char

- reverses single char
- Verify: reverses single char
   - Expected: str_reverse("a") equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses single char")
step("Verify: reverses single char")
expect(str_reverse("a")).to_equal("a")
```

</details>

#### reverses empty string

- reverses empty string
- Verify: reverses empty string
   - Expected: str_reverse("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses empty string")
step("Verify: reverses empty string")
expect(str_reverse("")).to_equal("")
```

</details>

#### reverses palindrome

- reverses palindrome
- Verify: reverses palindrome
   - Expected: str_reverse("aba") equals `aba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses palindrome")
step("Verify: reverses palindrome")
expect(str_reverse("aba")).to_equal("aba")
```

</details>

#### reverses two chars

- reverses two chars
- Verify: reverses two chars
   - Expected: str_reverse("ab") equals `ba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reverses two chars")
step("Verify: reverses two chars")
expect(str_reverse("ab")).to_equal("ba")
```

</details>

#### str_repeat

#### repeats multiple times

- repeats multiple times
- Verify: repeats multiple times
   - Expected: str_repeat("ab", 3) equals `ababab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats multiple times")
step("Verify: repeats multiple times")
expect(str_repeat("ab", 3)).to_equal("ababab")
```

</details>

#### repeats once

- repeats once
- Verify: repeats once
   - Expected: str_repeat("x", 1) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats once")
step("Verify: repeats once")
expect(str_repeat("x", 1)).to_equal("x")
```

</details>

#### repeats zero times

- repeats zero times
- Verify: repeats zero times
   - Expected: str_repeat("x", 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats zero times")
step("Verify: repeats zero times")
expect(str_repeat("x", 0)).to_equal("")
```

</details>

#### repeats empty string

- repeats empty string
- Verify: repeats empty string
   - Expected: str_repeat("", 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats empty string")
step("Verify: repeats empty string")
expect(str_repeat("", 5)).to_equal("")
```

</details>

#### repeats multi-char string

- repeats multi-char string
- Verify: repeats multi-char string
   - Expected: str_repeat("abc", 2) equals `abcabc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats multi-char string")
step("Verify: repeats multi-char string")
expect(str_repeat("abc", 2)).to_equal("abcabc")
```

</details>

#### str_truncate

#### truncates long string with ellipsis

- truncates long string with ellipsis
- Verify: truncates long string with ellipsis
   - Expected: str_truncate("hello world", 5) equals `hello...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates long string with ellipsis")
step("Verify: truncates long string with ellipsis")
expect(str_truncate("hello world", 5)).to_equal("hello...")
```

</details>

#### returns same when within max_len

- returns same when within max_len
- Verify: returns same when within max_len
   - Expected: str_truncate("hello", 10) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when within max_len")
step("Verify: returns same when within max_len")
expect(str_truncate("hello", 10)).to_equal("hello")
```

</details>

#### returns same when exactly max_len

- returns same when exactly max_len
- Verify: returns same when exactly max_len
   - Expected: str_truncate("hello", 5) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when exactly max_len")
step("Verify: returns same when exactly max_len")
expect(str_truncate("hello", 5)).to_equal("hello")
```

</details>

#### truncates to 1 char with ellipsis

- truncates to 1 char with ellipsis
- Verify: truncates to 1 char with ellipsis
   - Expected: str_truncate("hello", 1) equals `h...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates to 1 char with ellipsis")
step("Verify: truncates to 1 char with ellipsis")
expect(str_truncate("hello", 1)).to_equal("h...")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_truncate("", 5) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_truncate("", 5)).to_equal("")
```

</details>

#### truncates to 0 chars with ellipsis

- truncates to 0 chars with ellipsis
- Verify: truncates to 0 chars with ellipsis
   - Expected: str_truncate("hello", 0) equals `...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("truncates to 0 chars with ellipsis")
step("Verify: truncates to 0 chars with ellipsis")
expect(str_truncate("hello", 0)).to_equal("...")
```

</details>

#### str_pad_left

#### pads with zeros

- pads with zeros
- Verify: pads with zeros
   - Expected: str_pad_left("42", 5, "0") equals `00042`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads with zeros")
step("Verify: pads with zeros")
expect(str_pad_left("42", 5, "0")).to_equal("00042")
```

</details>

#### pads with spaces

- pads with spaces
- Verify: pads with spaces
   - Expected: str_pad_left("hi", 5, " ") equals `   hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads with spaces")
step("Verify: pads with spaces")
expect(str_pad_left("hi", 5, " ")).to_equal("   hi")
```

</details>

#### returns same when already at width

- returns same when already at width
- Verify: returns same when already at width
   - Expected: str_pad_left("hello", 5, " ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when already at width")
step("Verify: returns same when already at width")
expect(str_pad_left("hello", 5, " ")).to_equal("hello")
```

</details>

#### returns same when exceeds width

- returns same when exceeds width
- Verify: returns same when exceeds width
   - Expected: str_pad_left("hello", 3, " ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when exceeds width")
step("Verify: returns same when exceeds width")
expect(str_pad_left("hello", 3, " ")).to_equal("hello")
```

</details>

#### pads single char to width

- pads single char to width
- Verify: pads single char to width
   - Expected: str_pad_left("x", 3, "-") equals `--x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads single char to width")
step("Verify: pads single char to width")
expect(str_pad_left("x", 3, "-")).to_equal("--x")
```

</details>

#### pads empty string

- pads empty string
- Verify: pads empty string
   - Expected: str_pad_left("", 3, ".") equals `...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads empty string")
step("Verify: pads empty string")
expect(str_pad_left("", 3, ".")).to_equal("...")
```

</details>

#### str_pad_right

#### pads with zeros

- pads with zeros
- Verify: pads with zeros
   - Expected: str_pad_right("42", 5, "0") equals `42000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads with zeros")
step("Verify: pads with zeros")
expect(str_pad_right("42", 5, "0")).to_equal("42000")
```

</details>

#### pads with spaces

- pads with spaces
- Verify: pads with spaces
   - Expected: str_pad_right("hi", 5, " ") equals `hi   `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads with spaces")
step("Verify: pads with spaces")
expect(str_pad_right("hi", 5, " ")).to_equal("hi   ")
```

</details>

#### returns same when already at width

- returns same when already at width
- Verify: returns same when already at width
   - Expected: str_pad_right("hello", 5, " ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when already at width")
step("Verify: returns same when already at width")
expect(str_pad_right("hello", 5, " ")).to_equal("hello")
```

</details>

#### returns same when exceeds width

- returns same when exceeds width
- Verify: returns same when exceeds width
   - Expected: str_pad_right("hello", 3, " ") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when exceeds width")
step("Verify: returns same when exceeds width")
expect(str_pad_right("hello", 3, " ")).to_equal("hello")
```

</details>

#### pads single char to width

- pads single char to width
- Verify: pads single char to width
   - Expected: str_pad_right("x", 3, "-") equals `x--`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads single char to width")
step("Verify: pads single char to width")
expect(str_pad_right("x", 3, "-")).to_equal("x--")
```

</details>

#### pads empty string

- pads empty string
- Verify: pads empty string
   - Expected: str_pad_right("", 3, ".") equals `...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads empty string")
step("Verify: pads empty string")
expect(str_pad_right("", 3, ".")).to_equal("...")
```

</details>

#### str_center

#### centers short string in wider field

- centers short string in wider field
- Verify: centers short string in wider field
   - Expected: str_center("hi", 6) equals `  hi  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("centers short string in wider field")
step("Verify: centers short string in wider field")
expect(str_center("hi", 6)).to_equal("  hi  ")
```

</details>

#### returns same when string exceeds width

- returns same when string exceeds width
- Verify: returns same when string exceeds width
   - Expected: str_center("hello", 3) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same when string exceeds width")
step("Verify: returns same when string exceeds width")
expect(str_center("hello", 3)).to_equal("hello")
```

</details>

#### centers single char

- centers single char
- Verify: centers single char
   - Expected: str_center("x", 5) equals `  x  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("centers single char")
step("Verify: centers single char")
expect(str_center("x", 5)).to_equal("  x  ")
```

</details>

#### handles empty string

- handles empty string
- Verify: handles empty string
   - Expected: str_center("", 4) equals `    `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
step("Verify: handles empty string")
expect(str_center("", 4)).to_equal("    ")
```

</details>

### string_core - Compatibility Aliases

#### char_code alias

#### returns same as char_code_inline for letter

- returns same as char_code_inline for letter
- Verify: returns same as char_code_inline for letter
   - Expected: char_code("A") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same as char_code_inline for letter")
step("Verify: returns same as char_code_inline for letter")
expect(char_code("A")).to_equal(65)
```

</details>

#### returns same as char_code_inline for digit

- returns same as char_code_inline for digit
- Verify: returns same as char_code_inline for digit
   - Expected: char_code("0") equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same as char_code_inline for digit")
step("Verify: returns same as char_code_inline for digit")
expect(char_code("0")).to_equal(48)
```

</details>

#### returns 0 for unknown

- returns 0 for unknown
- Verify: returns 0 for unknown
   - Expected: char_code("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown")
step("Verify: returns 0 for unknown")
expect(char_code("")).to_equal(0)
```

</details>

#### char_from_code alias

#### returns same as char_from_code_inline for letter

- returns same as char_from_code_inline for letter
- Verify: returns same as char_from_code_inline for letter
   - Expected: char_from_code(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same as char_from_code_inline for letter")
step("Verify: returns same as char_from_code_inline for letter")
expect(char_from_code(65)).to_equal("A")
```

</details>

#### returns same as char_from_code_inline for digit

- returns same as char_from_code_inline for digit
- Verify: returns same as char_from_code_inline for digit
   - Expected: char_from_code(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns same as char_from_code_inline for digit")
step("Verify: returns same as char_from_code_inline for digit")
expect(char_from_code(48)).to_equal("0")
```

</details>

#### returns ASCII whitespace controls

- returns ASCII whitespace controls
- Verify: returns ASCII whitespace controls
   - Expected: char_from_code(11) equals `\u000B`
   - Expected: char_from_code(12) equals `\u000C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ASCII whitespace controls")
step("Verify: returns ASCII whitespace controls")
expect(char_from_code(11)).to_equal("\u000B")
expect(char_from_code(12)).to_equal("\u000C")
```

</details>

#### encodes U+0000 as a one-byte NUL and rejects invalid codepoints

- encodes U+0000 as a one-byte NUL and rejects invalid codepoints
- Verify: encodes U+0000 as a one-byte NUL and rejects invalid codepoints
   - Expected: nul.len() equals `1`
   - Expected: char_from_code(-1) equals ``
   - Expected: char_from_code(0x110000) equals ``
   - Expected: char_from_code(0xD800) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes U+0000 as a one-byte NUL and rejects invalid codepoints")
step("Verify: encodes U+0000 as a one-byte NUL and rejects invalid codepoints")
# U+0000 is a VALID Unicode scalar, not an "unknown code".
# char_from_code is a codepoint->text encoder, and the lexer
# (src/compiler/10.frontend/core/lexer.spl:331,
# lexer_struct.spl:426,799) depends on it producing a real
# one-byte NUL to use as a `.contains()` needle. Returning ""
# here would make that needle match EVERY string -- `s.contains("")`
# is unconditionally true -- silently blanking every saved token
# text in a bootstrap-critical path.
# doc/08_tracking/bug/char_from_code_zero_returns_nul_not_empty_2026-08-10.md
val nul = char_from_code(0)
expect(nul.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
assert_false(nul == "")
# Genuinely invalid codepoints are the ones that yield empty text.
expect(char_from_code(-1)).to_equal("")
expect(char_from_code(0x110000)).to_equal("")
expect(char_from_code(0xD800)).to_equal("")
```

</details>

### string_core - Round-trip Tests

#### char_code round-trip

#### round-trips lowercase letters

- round-trips lowercase letters
- Verify: round-trips lowercase letters
   - Expected: ch equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips lowercase letters")
step("Verify: round-trips lowercase letters")
val code = char_code_inline("a")
val ch = char_from_code_inline(code)
expect(ch).to_equal("a")
```

</details>

#### round-trips uppercase letters

- round-trips uppercase letters
- Verify: round-trips uppercase letters
   - Expected: ch equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips uppercase letters")
step("Verify: round-trips uppercase letters")
val code = char_code_inline("Z")
val ch = char_from_code_inline(code)
expect(ch).to_equal("Z")
```

</details>

#### round-trips digits

- round-trips digits
- Verify: round-trips digits
   - Expected: ch equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips digits")
step("Verify: round-trips digits")
val code = char_code_inline("5")
val ch = char_from_code_inline(code)
expect(ch).to_equal("5")
```

</details>

#### round-trips space

- round-trips space
- Verify: round-trips space
   - Expected: ch equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips space")
step("Verify: round-trips space")
val code = char_code_inline(" ")
val ch = char_from_code_inline(code)
expect(ch).to_equal(" ")
```

</details>

#### case conversion round-trip

#### to_lower then to_upper restores uppercase

- to_lower then to_upper restores uppercase
- Verify: to_lower then to_upper restores uppercase
   - Expected: upper equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_lower then to_upper restores uppercase")
step("Verify: to_lower then to_upper restores uppercase")
val original = "HELLO"
val lower = str_to_lower(original)
val upper = str_to_upper(lower)
expect(upper).to_equal(original)
```

</details>

#### to_upper then to_lower restores lowercase

- to_upper then to_lower restores lowercase
- Verify: to_upper then to_lower restores lowercase
   - Expected: lower equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_upper then to_lower restores lowercase")
step("Verify: to_upper then to_lower restores lowercase")
val original = "hello"
val upper = str_to_upper(original)
val lower = str_to_lower(upper)
expect(lower).to_equal(original)
```

</details>

#### trim + pad round-trip

#### trim removes what pad adds

- trim removes what pad adds
- Verify: trim removes what pad adds
   - Expected: trimmed equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim removes what pad adds")
step("Verify: trim removes what pad adds")
val padded = str_pad_left("hi", 5, " ")
val trimmed = str_trim_left(padded)
expect(trimmed).to_equal("hi")
```

</details>

#### split + join round-trip

#### split then join restores original

- split then join restores original
- Verify: split then join restores original
   - Expected: joined equals `original`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("split then join restores original")
step("Verify: split then join restores original")
val original = "a,b,c"
val parts = str_split(original, ",")
val joined = str_join(parts, ",")
expect(joined).to_equal(original)
```

</details>

#### replace_all + index_of integration

#### replacement removes all occurrences

- replacement removes all occurrences
- Verify: replacement removes all occurrences
   - Expected: str_index_of(result, "a") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replacement removes all occurrences")
step("Verify: replacement removes all occurrences")
val result = str_replace_all("abcabc", "a", "")
expect(str_index_of(result, "a")).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 205 |
| Active scenarios | 205 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cdd86366f1de0a698f09eba53bb6d3b8bf58dd6d0207617c426753e283a8d84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cdd86366f1de0a698f09eba53bb6d3b8bf58dd6d0207617c426753e283a8d84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cdd86366f1de0a698f09eba53bb6d3b8bf58dd6d0207617c426753e283a8d84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/string_core_ops_spec.spl
mirror: doc/06_spec/unit/lib/common/string_core_ops_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/string_core_ops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/string_core_ops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/string_core_ops_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 23 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/string_core_ops_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns length of normal string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_ops_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_ops_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 1 for single character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

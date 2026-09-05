# String Core Coverage Specification

> Purpose: Prove that string_core - Basic Operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 266 | 266 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Coverage Specification

Purpose: Prove that string_core - Basic Operations.

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
| Source | `test/unit/lib/common/string_core_basic_coverage_spec.spl` |
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

### string_core - char_code_inline

#### whitespace characters

#### returns 32 for space

- returns 32 for space
- Verify: returns 32 for space
   - Expected: char_code_inline(" ") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 32 for space")
step("Verify: returns 32 for space")
expect(char_code_inline(" ")).to_equal(32)
```

</details>

#### returns 10 for newline

- returns 10 for newline
- Verify: returns 10 for newline
   - Expected: char_code_inline("\n") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 10 for newline")
step("Verify: returns 10 for newline")
expect(char_code_inline("\n")).to_equal(10)
```

</details>

#### returns 9 for tab

- returns 9 for tab
- Verify: returns 9 for tab
   - Expected: char_code_inline("\t") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 9 for tab")
step("Verify: returns 9 for tab")
expect(char_code_inline("\t")).to_equal(9)
```

</details>

#### returns 13 for carriage return

- returns 13 for carriage return
- Verify: returns 13 for carriage return
   - Expected: char_code_inline("\r") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 13 for carriage return")
step("Verify: returns 13 for carriage return")
expect(char_code_inline("\r")).to_equal(13)
```

</details>

#### punctuation

#### returns 33 for exclamation

- returns 33 for exclamation
- Verify: returns 33 for exclamation
   - Expected: char_code_inline("!") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 33 for exclamation")
step("Verify: returns 33 for exclamation")
expect(char_code_inline("!")).to_equal(33)
```

</details>

#### returns 35 for hash

- returns 35 for hash
- Verify: returns 35 for hash
   - Expected: char_code_inline("#") equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 35 for hash")
step("Verify: returns 35 for hash")
expect(char_code_inline("#")).to_equal(35)
```

</details>

#### returns 46 for period

- returns 46 for period
- Verify: returns 46 for period
   - Expected: char_code_inline(".") equals `46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 46 for period")
step("Verify: returns 46 for period")
expect(char_code_inline(".")).to_equal(46)
```

</details>

#### returns 44 for comma

- returns 44 for comma
- Verify: returns 44 for comma
   - Expected: char_code_inline(",") equals `44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 44 for comma")
step("Verify: returns 44 for comma")
expect(char_code_inline(",")).to_equal(44)
```

</details>

#### returns 45 for hyphen

- returns 45 for hyphen
- Verify: returns 45 for hyphen
   - Expected: char_code_inline("-") equals `45`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 45 for hyphen")
step("Verify: returns 45 for hyphen")
expect(char_code_inline("-")).to_equal(45)
```

</details>

#### returns 95 for underscore

- returns 95 for underscore
- Verify: returns 95 for underscore
   - Expected: char_code_inline("_") equals `95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 95 for underscore")
step("Verify: returns 95 for underscore")
expect(char_code_inline("_")).to_equal(95)
```

</details>

#### returns 64 for at-sign

- returns 64 for at-sign
- Verify: returns 64 for at-sign
   - Expected: char_code_inline("@") equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 64 for at-sign")
step("Verify: returns 64 for at-sign")
expect(char_code_inline("@")).to_equal(64)
```

</details>

#### returns 40 for open paren

- returns 40 for open paren
- Verify: returns 40 for open paren
   - Expected: char_code_inline("(") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 40 for open paren")
step("Verify: returns 40 for open paren")
expect(char_code_inline("(")).to_equal(40)
```

</details>

#### returns 41 for close paren

- returns 41 for close paren
- Verify: returns 41 for close paren
   - Expected: char_code_inline(")") equals `41`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 41 for close paren")
step("Verify: returns 41 for close paren")
expect(char_code_inline(")")).to_equal(41)
```

</details>

#### returns 91 for open bracket

- returns 91 for open bracket
- Verify: returns 91 for open bracket
   - Expected: char_code_inline("[") equals `91`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 91 for open bracket")
step("Verify: returns 91 for open bracket")
expect(char_code_inline("[")).to_equal(91)
```

</details>

#### returns 93 for close bracket

- returns 93 for close bracket
- Verify: returns 93 for close bracket
   - Expected: char_code_inline("]") equals `93`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 93 for close bracket")
step("Verify: returns 93 for close bracket")
expect(char_code_inline("]")).to_equal(93)
```

</details>

#### returns 123 for open brace

- returns 123 for open brace
- Verify: returns 123 for open brace
   - Expected: char_code_inline("{") equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 123 for open brace")
step("Verify: returns 123 for open brace")
expect(char_code_inline("{")).to_equal(123)
```

</details>

#### returns 125 for close brace

- returns 125 for close brace
- Verify: returns 125 for close brace
   - Expected: char_code_inline("}") equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 125 for close brace")
step("Verify: returns 125 for close brace")
expect(char_code_inline("}")).to_equal(125)
```

</details>

#### returns 124 for pipe

- returns 124 for pipe
- Verify: returns 124 for pipe
   - Expected: char_code_inline("|") equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 124 for pipe")
step("Verify: returns 124 for pipe")
expect(char_code_inline("|")).to_equal(124)
```

</details>

#### returns 126 for tilde

- returns 126 for tilde
- Verify: returns 126 for tilde
   - Expected: char_code_inline("~") equals `126`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 126 for tilde")
step("Verify: returns 126 for tilde")
expect(char_code_inline("~")).to_equal(126)
```

</details>

#### returns 94 for caret

- returns 94 for caret
- Verify: returns 94 for caret
   - Expected: char_code_inline("^") equals `94`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 94 for caret")
step("Verify: returns 94 for caret")
expect(char_code_inline("^")).to_equal(94)
```

</details>

#### returns 36 for dollar

- returns 36 for dollar
- Verify: returns 36 for dollar
   - Expected: char_code_inline("$") equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 36 for dollar")
step("Verify: returns 36 for dollar")
expect(char_code_inline("$")).to_equal(36)
```

</details>

#### returns 37 for percent

- returns 37 for percent
- Verify: returns 37 for percent
   - Expected: char_code_inline("%") equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 37 for percent")
step("Verify: returns 37 for percent")
expect(char_code_inline("%")).to_equal(37)
```

</details>

#### returns 38 for ampersand

- returns 38 for ampersand
- Verify: returns 38 for ampersand
   - Expected: char_code_inline("&") equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 38 for ampersand")
step("Verify: returns 38 for ampersand")
expect(char_code_inline("&")).to_equal(38)
```

</details>

#### returns 42 for asterisk

- returns 42 for asterisk
- Verify: returns 42 for asterisk
   - Expected: char_code_inline("*") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 42 for asterisk")
step("Verify: returns 42 for asterisk")
expect(char_code_inline("*")).to_equal(42)
```

</details>

#### returns 43 for plus

- returns 43 for plus
- Verify: returns 43 for plus
   - Expected: char_code_inline("+") equals `43`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 43 for plus")
step("Verify: returns 43 for plus")
expect(char_code_inline("+")).to_equal(43)
```

</details>

#### returns 47 for slash

- returns 47 for slash
- Verify: returns 47 for slash
   - Expected: char_code_inline("/") equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 47 for slash")
step("Verify: returns 47 for slash")
expect(char_code_inline("/")).to_equal(47)
```

</details>

#### returns 58 for colon

- returns 58 for colon
- Verify: returns 58 for colon
   - Expected: char_code_inline(":") equals `58`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 58 for colon")
step("Verify: returns 58 for colon")
expect(char_code_inline(":")).to_equal(58)
```

</details>

#### returns 59 for semicolon

- returns 59 for semicolon
- Verify: returns 59 for semicolon
   - Expected: char_code_inline(";") equals `59`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 59 for semicolon")
step("Verify: returns 59 for semicolon")
expect(char_code_inline(";")).to_equal(59)
```

</details>

#### returns 60 for less-than

- returns 60 for less-than
- Verify: returns 60 for less-than
   - Expected: char_code_inline("<") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 60 for less-than")
step("Verify: returns 60 for less-than")
expect(char_code_inline("<")).to_equal(60)
```

</details>

#### returns 61 for equals

- returns 61 for equals
- Verify: returns 61 for equals
   - Expected: char_code_inline("=") equals `61`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 61 for equals")
step("Verify: returns 61 for equals")
expect(char_code_inline("=")).to_equal(61)
```

</details>

#### returns 62 for greater-than

- returns 62 for greater-than
- Verify: returns 62 for greater-than
   - Expected: char_code_inline(">") equals `62`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 62 for greater-than")
step("Verify: returns 62 for greater-than")
expect(char_code_inline(">")).to_equal(62)
```

</details>

#### returns 39 for single quote

- returns 39 for single quote
- Verify: returns 39 for single quote
   - Expected: char_code_inline("'") equals `39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 39 for single quote")
step("Verify: returns 39 for single quote")
expect(char_code_inline("'")).to_equal(39)
```

</details>

#### digits

#### returns 48 for 0

- returns 48 for 0
- Verify: returns 48 for 0
   - Expected: char_code_inline("0") equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 48 for 0")
step("Verify: returns 48 for 0")
expect(char_code_inline("0")).to_equal(48)
```

</details>

#### returns 53 for 5

- returns 53 for 5
- Verify: returns 53 for 5
   - Expected: char_code_inline("5") equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 53 for 5")
step("Verify: returns 53 for 5")
expect(char_code_inline("5")).to_equal(53)
```

</details>

#### returns 57 for 9

- returns 57 for 9
- Verify: returns 57 for 9
   - Expected: char_code_inline("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 57 for 9")
step("Verify: returns 57 for 9")
expect(char_code_inline("9")).to_equal(57)
```

</details>

#### uppercase letters

#### returns 65 for A

- returns 65 for A
- Verify: returns 65 for A
   - Expected: char_code_inline("A") equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 65 for A")
step("Verify: returns 65 for A")
expect(char_code_inline("A")).to_equal(65)
```

</details>

#### returns 77 for M

- returns 77 for M
- Verify: returns 77 for M
   - Expected: char_code_inline("M") equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 77 for M")
step("Verify: returns 77 for M")
expect(char_code_inline("M")).to_equal(77)
```

</details>

#### returns 90 for Z

- returns 90 for Z
- Verify: returns 90 for Z
   - Expected: char_code_inline("Z") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 90 for Z")
step("Verify: returns 90 for Z")
expect(char_code_inline("Z")).to_equal(90)
```

</details>

#### lowercase letters

#### returns 97 for a

- returns 97 for a
- Verify: returns 97 for a
   - Expected: char_code_inline("a") equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 97 for a")
step("Verify: returns 97 for a")
expect(char_code_inline("a")).to_equal(97)
```

</details>

#### returns 109 for m

- returns 109 for m
- Verify: returns 109 for m
   - Expected: char_code_inline("m") equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 109 for m")
step("Verify: returns 109 for m")
expect(char_code_inline("m")).to_equal(109)
```

</details>

#### returns 122 for z

- returns 122 for z
- Verify: returns 122 for z
   - Expected: char_code_inline("z") equals `122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 122 for z")
step("Verify: returns 122 for z")
expect(char_code_inline("z")).to_equal(122)
```

</details>

#### unknown characters

#### returns 0 for unknown character

- returns 0 for unknown character
- Verify: returns 0 for unknown character
   - Expected: char_code_inline("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown character")
step("Verify: returns 0 for unknown character")
expect(char_code_inline("")).to_equal(0)
```

</details>

#### question mark

#### returns 63 for question mark

- returns 63 for question mark
- Verify: returns 63 for question mark
   - Expected: char_code_inline(qm) equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 63 for question mark")
step("Verify: returns 63 for question mark")
val qm = char_from_code_inline(63)
expect(char_code_inline(qm)).to_equal(63)  # oracle: 63 — named expected value from the requirement
```

</details>

### string_core - char_from_code_inline

#### whitespace codes

#### returns space for 32

- returns space for 32
- Verify: returns space for 32
   - Expected: char_from_code_inline(32) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns space for 32")
step("Verify: returns space for 32")
expect(char_from_code_inline(32)).to_equal(" ")
```

</details>

#### returns newline for 10

- returns newline for 10
- Verify: returns newline for 10
   - Expected: char_from_code_inline(10) equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns newline for 10")
step("Verify: returns newline for 10")
expect(char_from_code_inline(10)).to_equal("\n")
```

</details>

#### returns tab for 9

- returns tab for 9
- Verify: returns tab for 9
   - Expected: char_from_code_inline(9) equals `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tab for 9")
step("Verify: returns tab for 9")
expect(char_from_code_inline(9)).to_equal("\t")
```

</details>

#### returns carriage return for 13

- returns carriage return for 13
- Verify: returns carriage return for 13
   - Expected: char_from_code_inline(13) equals `\r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns carriage return for 13")
step("Verify: returns carriage return for 13")
expect(char_from_code_inline(13)).to_equal("\r")
```

</details>

#### punctuation codes

#### returns exclamation for 33

- returns exclamation for 33
- Verify: returns exclamation for 33
   - Expected: char_from_code_inline(33) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns exclamation for 33")
step("Verify: returns exclamation for 33")
expect(char_from_code_inline(33)).to_equal("!")
```

</details>

#### returns period for 46

- returns period for 46
- Verify: returns period for 46
   - Expected: char_from_code_inline(46) equals `.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns period for 46")
step("Verify: returns period for 46")
expect(char_from_code_inline(46)).to_equal(".")
```

</details>

#### returns underscore for 95

- returns underscore for 95
- Verify: returns underscore for 95
   - Expected: char_from_code_inline(95) equals `_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns underscore for 95")
step("Verify: returns underscore for 95")
expect(char_from_code_inline(95)).to_equal("_")
```

</details>

#### returns open paren for 40

- returns open paren for 40
- Verify: returns open paren for 40
   - Expected: char_from_code_inline(40) equals `(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open paren for 40")
step("Verify: returns open paren for 40")
expect(char_from_code_inline(40)).to_equal("(")
```

</details>

#### returns close paren for 41

- returns close paren for 41
- Verify: returns close paren for 41
   - Expected: char_from_code_inline(41) equals `)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close paren for 41")
step("Verify: returns close paren for 41")
expect(char_from_code_inline(41)).to_equal(")")
```

</details>

#### returns open bracket for 91

- returns open bracket for 91
- Verify: returns open bracket for 91
   - Expected: char_from_code_inline(91) equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open bracket for 91")
step("Verify: returns open bracket for 91")
expect(char_from_code_inline(91)).to_equal("[")
```

</details>

#### returns close bracket for 93

- returns close bracket for 93
- Verify: returns close bracket for 93
   - Expected: char_from_code_inline(93) equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close bracket for 93")
step("Verify: returns close bracket for 93")
expect(char_from_code_inline(93)).to_equal("]")
```

</details>

#### returns open brace for 123

- returns open brace for 123
- Verify: returns open brace for 123
   - Expected: char_from_code_inline(123) equals `{`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns open brace for 123")
step("Verify: returns open brace for 123")
expect(char_from_code_inline(123)).to_equal("{")
```

</details>

#### returns close brace for 125

- returns close brace for 125
- Verify: returns close brace for 125
   - Expected: char_from_code_inline(125) equals `}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns close brace for 125")
step("Verify: returns close brace for 125")
expect(char_from_code_inline(125)).to_equal("}")
```

</details>

#### returns pipe for 124

- returns pipe for 124
- Verify: returns pipe for 124
   - Expected: char_from_code_inline(124) equals `|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pipe for 124")
step("Verify: returns pipe for 124")
expect(char_from_code_inline(124)).to_equal("|")
```

</details>

#### returns tilde for 126

- returns tilde for 126
- Verify: returns tilde for 126
   - Expected: char_from_code_inline(126) equals `~`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns tilde for 126")
step("Verify: returns tilde for 126")
expect(char_from_code_inline(126)).to_equal("~")
```

</details>

#### returns caret for 94

- returns caret for 94
- Verify: returns caret for 94
   - Expected: char_from_code_inline(94) equals `^`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns caret for 94")
step("Verify: returns caret for 94")
expect(char_from_code_inline(94)).to_equal("^")
```

</details>

#### returns hash for 35

- returns hash for 35
- Verify: returns hash for 35
   - Expected: char_from_code_inline(35) equals `#`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hash for 35")
step("Verify: returns hash for 35")
expect(char_from_code_inline(35)).to_equal("#")
```

</details>

#### returns dollar for 36

- returns dollar for 36
- Verify: returns dollar for 36
   - Expected: char_from_code_inline(36) equals `$`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns dollar for 36")
step("Verify: returns dollar for 36")
expect(char_from_code_inline(36)).to_equal("$")
```

</details>

#### returns percent for 37

- returns percent for 37
- Verify: returns percent for 37
   - Expected: char_from_code_inline(37) equals `%`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns percent for 37")
step("Verify: returns percent for 37")
expect(char_from_code_inline(37)).to_equal("%")
```

</details>

#### returns ampersand for 38

- returns ampersand for 38
- Verify: returns ampersand for 38
   - Expected: char_from_code_inline(38) equals `&`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns ampersand for 38")
step("Verify: returns ampersand for 38")
expect(char_from_code_inline(38)).to_equal("&")
```

</details>

#### returns single quote for 39

- returns single quote for 39
- Verify: returns single quote for 39
   - Expected: char_from_code_inline(39) equals `'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single quote for 39")
step("Verify: returns single quote for 39")
expect(char_from_code_inline(39)).to_equal("'")
```

</details>

#### returns asterisk for 42

- returns asterisk for 42
- Verify: returns asterisk for 42
   - Expected: char_from_code_inline(42) equals `*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns asterisk for 42")
step("Verify: returns asterisk for 42")
expect(char_from_code_inline(42)).to_equal("*")
```

</details>

#### returns plus for 43

- returns plus for 43
- Verify: returns plus for 43
   - Expected: char_from_code_inline(43) equals `+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns plus for 43")
step("Verify: returns plus for 43")
expect(char_from_code_inline(43)).to_equal("+")
```

</details>

#### returns comma for 44

- returns comma for 44
- Verify: returns comma for 44
   - Expected: char_from_code_inline(44) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns comma for 44")
step("Verify: returns comma for 44")
expect(char_from_code_inline(44)).to_equal(",")
```

</details>

#### returns hyphen for 45

- returns hyphen for 45
- Verify: returns hyphen for 45
   - Expected: char_from_code_inline(45) equals `-`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hyphen for 45")
step("Verify: returns hyphen for 45")
expect(char_from_code_inline(45)).to_equal("-")
```

</details>

#### returns slash for 47

- returns slash for 47
- Verify: returns slash for 47
   - Expected: char_from_code_inline(47) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns slash for 47")
step("Verify: returns slash for 47")
expect(char_from_code_inline(47)).to_equal("/")
```

</details>

#### returns colon for 58

- returns colon for 58
- Verify: returns colon for 58
   - Expected: char_from_code_inline(58) equals `:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns colon for 58")
step("Verify: returns colon for 58")
expect(char_from_code_inline(58)).to_equal(":")
```

</details>

#### returns semicolon for 59

- returns semicolon for 59
- Verify: returns semicolon for 59
   - Expected: char_from_code_inline(59) equals `;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns semicolon for 59")
step("Verify: returns semicolon for 59")
expect(char_from_code_inline(59)).to_equal(";")
```

</details>

#### returns less-than for 60

- returns less-than for 60
- Verify: returns less-than for 60
   - Expected: char_from_code_inline(60) equals `<`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns less-than for 60")
step("Verify: returns less-than for 60")
expect(char_from_code_inline(60)).to_equal("<")
```

</details>

#### returns equals for 61

- returns equals for 61
- Verify: returns equals for 61
   - Expected: char_from_code_inline(61) equals `=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns equals for 61")
step("Verify: returns equals for 61")
expect(char_from_code_inline(61)).to_equal("=")
```

</details>

#### returns greater-than for 62

- returns greater-than for 62
- Verify: returns greater-than for 62
   - Expected: char_from_code_inline(62) equals `>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns greater-than for 62")
step("Verify: returns greater-than for 62")
expect(char_from_code_inline(62)).to_equal(">")
```

</details>

#### returns at-sign for 64

- returns at-sign for 64
- Verify: returns at-sign for 64
   - Expected: char_from_code_inline(64) equals `@`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns at-sign for 64")
step("Verify: returns at-sign for 64")
expect(char_from_code_inline(64)).to_equal("@")
```

</details>

#### digit codes

#### returns 0 for 48

- returns 0 for 48
- Verify: returns 0 for 48
   - Expected: char_from_code_inline(48) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for 48")
step("Verify: returns 0 for 48")
expect(char_from_code_inline(48)).to_equal("0")
```

</details>

#### returns 5 for 53

- returns 5 for 53
- Verify: returns 5 for 53
   - Expected: char_from_code_inline(53) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 5 for 53")
step("Verify: returns 5 for 53")
expect(char_from_code_inline(53)).to_equal("5")
```

</details>

#### returns 9 for 57

- returns 9 for 57
- Verify: returns 9 for 57
   - Expected: char_from_code_inline(57) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 9 for 57")
step("Verify: returns 9 for 57")
expect(char_from_code_inline(57)).to_equal("9")
```

</details>

#### uppercase letter codes

#### returns A for 65

- returns A for 65
- Verify: returns A for 65
   - Expected: char_from_code_inline(65) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns A for 65")
step("Verify: returns A for 65")
expect(char_from_code_inline(65)).to_equal("A")
```

</details>

#### returns M for 77

- returns M for 77
- Verify: returns M for 77
   - Expected: char_from_code_inline(77) equals `M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns M for 77")
step("Verify: returns M for 77")
expect(char_from_code_inline(77)).to_equal("M")
```

</details>

#### returns Z for 90

- returns Z for 90
- Verify: returns Z for 90
   - Expected: char_from_code_inline(90) equals `Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Z for 90")
step("Verify: returns Z for 90")
expect(char_from_code_inline(90)).to_equal("Z")
```

</details>

#### lowercase letter codes

#### returns a for 97

- returns a for 97
- Verify: returns a for 97
   - Expected: char_from_code_inline(97) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a for 97")
step("Verify: returns a for 97")
expect(char_from_code_inline(97)).to_equal("a")
```

</details>

#### returns m for 109

- returns m for 109
- Verify: returns m for 109
   - Expected: char_from_code_inline(109) equals `m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns m for 109")
step("Verify: returns m for 109")
expect(char_from_code_inline(109)).to_equal("m")
```

</details>

#### returns z for 122

- returns z for 122
- Verify: returns z for 122
   - Expected: char_from_code_inline(122) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns z for 122")
step("Verify: returns z for 122")
expect(char_from_code_inline(122)).to_equal("z")
```

</details>

#### unknown codes

#### encodes U+0000 as a one-byte NUL, not empty text

- encodes U+0000 as a one-byte NUL, not empty text
- Verify: encodes U+0000 as a one-byte NUL, not empty text
   - Expected: nul.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes U+0000 as a one-byte NUL, not empty text")
step("Verify: encodes U+0000 as a one-byte NUL, not empty text")
# Ruled contract (doc/08_tracking/bug/
# char_from_code_zero_returns_nul_not_empty_2026-08-10.md): U+0000
# is a VALID Unicode scalar. The lexer (lexer.spl:331,
# lexer_struct.spl:426,799) depends on char_from_code(0) producing
# a real one-byte NUL as a `.contains()` needle -- returning ""
# here would make that needle match every string.
val nul = char_from_code_inline(0)
expect(nul.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
assert_false(nul == "")
```

</details>

#### encodes 999 (a valid codepoint) rather than rejecting it

- encodes 999 (a valid codepoint) rather than rejecting it
- Verify: encodes 999 (a valid codepoint) rather than rejecting it


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes 999 (a valid codepoint) rather than rejecting it")
step("Verify: encodes 999 (a valid codepoint) rather than rejecting it")
expect(char_from_code_inline(999).len()).to_be_greater_than(0)
```

</details>

#### returns empty for negative code

- returns empty for negative code
- Verify: returns empty for negative code
   - Expected: char_from_code_inline(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for negative code")
step("Verify: returns empty for negative code")
expect(char_from_code_inline(-1)).to_equal("")
```

</details>

#### encodes code 1 (a valid C0 control codepoint) rather than rejecting it

- encodes code 1 (a valid C0 control codepoint) rather than rejecting it
- Verify: encodes code 1 (a valid C0 control codepoint) rather than rejecting it
   - Expected: char_from_code_inline(1).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes code 1 (a valid C0 control codepoint) rather than rejecting it")
step("Verify: encodes code 1 (a valid C0 control codepoint) rather than rejecting it")
expect(char_from_code_inline(1).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns empty for code above U+10FFFF

- returns empty for code above U+10FFFF
- Verify: returns empty for code above U+10FFFF
   - Expected: char_from_code_inline(0x110000) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for code above U+10FFFF")
step("Verify: returns empty for code above U+10FFFF")
expect(char_from_code_inline(0x110000)).to_equal("")
```

</details>

#### returns empty for a lone UTF-16 surrogate

- returns empty for a lone UTF-16 surrogate
- Verify: returns empty for a lone UTF-16 surrogate
   - Expected: char_from_code_inline(0xD800) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for a lone UTF-16 surrogate")
step("Verify: returns empty for a lone UTF-16 surrogate")
expect(char_from_code_inline(0xD800)).to_equal("")
```

</details>

### string_core - Character Classification

#### is_alpha_char

#### returns true for lowercase letter

- returns true for lowercase letter
- Verify: returns true for lowercase letter
   - Expected: is_alpha_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for lowercase letter")
step("Verify: returns true for lowercase letter")
expect(is_alpha_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

- returns true for uppercase letter
- Verify: returns true for uppercase letter
   - Expected: is_alpha_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for uppercase letter")
step("Verify: returns true for uppercase letter")
expect(is_alpha_char("Z")).to_equal(true)
```

</details>

#### returns true for middle lowercase

- returns true for middle lowercase
- Verify: returns true for middle lowercase
   - Expected: is_alpha_char("m") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle lowercase")
step("Verify: returns true for middle lowercase")
expect(is_alpha_char("m")).to_equal(true)
```

</details>

#### returns true for middle uppercase

- returns true for middle uppercase
- Verify: returns true for middle uppercase
   - Expected: is_alpha_char("M") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle uppercase")
step("Verify: returns true for middle uppercase")
expect(is_alpha_char("M")).to_equal(true)
```

</details>

#### returns false for digit

- returns false for digit
- Verify: returns false for digit
   - Expected: is_alpha_char("5") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for digit")
step("Verify: returns false for digit")
expect(is_alpha_char("5")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_alpha_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_alpha_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_alpha_char("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_alpha_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

- returns false for underscore
- Verify: returns false for underscore
   - Expected: is_alpha_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for underscore")
step("Verify: returns false for underscore")
expect(is_alpha_char("_")).to_equal(false)
```

</details>

#### is_digit_char

#### returns true for 0

- returns true for 0
- Verify: returns true for 0
   - Expected: is_digit_char("0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 0")
step("Verify: returns true for 0")
expect(is_digit_char("0")).to_equal(true)
```

</details>

#### returns true for 9

- returns true for 9
- Verify: returns true for 9
   - Expected: is_digit_char("9") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for 9")
step("Verify: returns true for 9")
expect(is_digit_char("9")).to_equal(true)
```

</details>

#### returns true for middle digit

- returns true for middle digit
- Verify: returns true for middle digit
   - Expected: is_digit_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for middle digit")
step("Verify: returns true for middle digit")
expect(is_digit_char("5")).to_equal(true)
```

</details>

#### returns false for letter

- returns false for letter
- Verify: returns false for letter
   - Expected: is_digit_char("a") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for letter")
step("Verify: returns false for letter")
expect(is_digit_char("a")).to_equal(false)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_digit_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_digit_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_digit_char(".") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_digit_char(".")).to_equal(false)
```

</details>

#### is_alnum_char

#### returns true for letter

- returns true for letter
- Verify: returns true for letter
   - Expected: is_alnum_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for letter")
step("Verify: returns true for letter")
expect(is_alnum_char("a")).to_equal(true)
```

</details>

#### returns true for uppercase letter

- returns true for uppercase letter
- Verify: returns true for uppercase letter
   - Expected: is_alnum_char("Z") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for uppercase letter")
step("Verify: returns true for uppercase letter")
expect(is_alnum_char("Z")).to_equal(true)
```

</details>

#### returns true for digit

- returns true for digit
- Verify: returns true for digit
   - Expected: is_alnum_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for digit")
step("Verify: returns true for digit")
expect(is_alnum_char("5")).to_equal(true)
```

</details>

#### returns false for space

- returns false for space
- Verify: returns false for space
   - Expected: is_alnum_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for space")
step("Verify: returns false for space")
expect(is_alnum_char(" ")).to_equal(false)
```

</details>

#### returns false for punctuation

- returns false for punctuation
- Verify: returns false for punctuation
   - Expected: is_alnum_char("!") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for punctuation")
step("Verify: returns false for punctuation")
expect(is_alnum_char("!")).to_equal(false)
```

</details>

#### returns false for underscore

- returns false for underscore
- Verify: returns false for underscore
   - Expected: is_alnum_char("_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for underscore")
step("Verify: returns false for underscore")
expect(is_alnum_char("_")).to_equal(false)
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 266 |
| Active scenarios | 266 |
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

- Canonical SPipe generation for source `40c2cf49a6bab84ddef9dc8fd2e631d8ff95430ce9592a5eb0cf9e79d47c693c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40c2cf49a6bab84ddef9dc8fd2e631d8ff95430ce9592a5eb0cf9e79d47c693c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40c2cf49a6bab84ddef9dc8fd2e631d8ff95430ce9592a5eb0cf9e79d47c693c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/common/string_core_basic_coverage_spec.spl
mirror: doc/06_spec/unit/lib/common/string_core_basic_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/string_core_basic_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/string_core_basic_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/string_core_basic_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 61 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/string_core_basic_coverage_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns length of normal string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_basic_coverage_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 for empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/string_core_basic_coverage_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 1 for single character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

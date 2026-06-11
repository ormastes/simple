# text.slice() and text.substring() Specification

> Verifies that text.slice(start, end) and text.substring(start, end) return correct substrings. Previously:

<!-- sdn-diagram:id=text_slice_substring_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_slice_substring_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_slice_substring_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_slice_substring_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text.slice() and text.substring() Specification

Verifies that text.slice(start, end) and text.substring(start, end) return correct substrings. Previously:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-SLICE-001 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/bug/bug_report_text_slice_substring.md |
| Source | `test/01_unit/bugs/text_slice_substring_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that text.slice(start, end) and text.substring(start, end)
return correct substrings. Previously:
- slice() was completely missing from the interpreter
- substring() crashed with "string index out of bounds"
- char_code_at and char_at also used broken substring internally

## Syntax

```simple
val s = "abcdefghijk"
s.slice(0, 5)       # "abcde"
s.substring(0, 5)   # "abcde"
s[2:5]              # "cde" (slice expression)
s.char_at(3)        # "d"
```

## Scenarios

### text.slice() method

#### single character extraction

#### slices first character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0, 1)).to_equal("a")
```

</details>

#### slices second character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(1, 2)).to_equal("b")
```

</details>

#### slices last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(10, 11)).to_equal("k")
```

</details>

#### slices middle character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(5, 6)).to_equal("f")
```

</details>

#### multi-character ranges

#### slices first two characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0, 2)).to_equal("ab")
```

</details>

#### slices first three characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0, 3)).to_equal("abc")
```

</details>

#### slices first five characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0, 5)).to_equal("abcde")
```

</details>

#### slices from middle to middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(2, 5)).to_equal("cde")
```

</details>

#### slices from offset 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(1, 5)).to_equal("bcde")
```

</details>

#### slices tail portion

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(5, 11)).to_equal("fghijk")
```

</details>

#### slices entire string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0, 11)).to_equal("abcdefghijk")
```

</details>

#### boundary and edge cases

#### returns empty for equal start and end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(3, 3)).to_equal("")
```

</details>

#### returns empty for reversed range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(5, 3)).to_equal("")
```

</details>

#### clamps end beyond string length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.slice(0, 100)).to_equal("abc")
```

</details>

#### clamps negative start to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.slice(-5, 2)).to_equal("ab")
```

</details>

#### handles single-char string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "x"
expect(s.slice(0, 1)).to_equal("x")
```

</details>

#### handles two-char string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "ab"
expect(s.slice(0, 1)).to_equal("a")
expect(s.slice(1, 2)).to_equal("b")
expect(s.slice(0, 2)).to_equal("ab")
```

</details>

#### one-argument form

#### slices from start to end of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(0)).to_equal("abcdefghijk")
```

</details>

#### slices tail from offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.slice(5)).to_equal("fghijk")
```

</details>

#### various string contents

#### slices string with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
expect(s.slice(0, 5)).to_equal("hello")
expect(s.slice(6, 11)).to_equal("world")
```

</details>

#### slices string with numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc123def"
expect(s.slice(3, 6)).to_equal("123")
```

</details>

#### slices string with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "a-b_c.d"
expect(s.slice(1, 4)).to_equal("-b_")
```

</details>

#### slices path-like string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "/home/user/file.txt"
expect(s.slice(0, 5)).to_equal("/home")
```

</details>

#### slices comma-separated values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "one,two,three"
expect(s.slice(0, 3)).to_equal("one")
expect(s.slice(4, 7)).to_equal("two")
expect(s.slice(8, 13)).to_equal("three")
```

</details>

### text.substring() method

#### two-argument form

#### extracts from start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(0, 5)).to_equal("abcde")
```

</details>

#### extracts from middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(2, 5)).to_equal("cde")
```

</details>

#### extracts single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(3, 4)).to_equal("d")
```

</details>

#### extracts to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(5, 11)).to_equal("fghijk")
```

</details>

#### extracts full string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(0, 11)).to_equal("abcdefghijk")
```

</details>

#### one-argument form

#### extracts from start to end of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(0)).to_equal("abcdefghijk")
```

</details>

#### extracts tail

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(5)).to_equal("fghijk")
```

</details>

#### extracts last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s.substring(10)).to_equal("k")
```

</details>

#### boundary handling

#### clamps negative start to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.substring(-1, 2)).to_equal("ab")
```

</details>

#### clamps end beyond length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.substring(0, 100)).to_equal("abc")
```

</details>

#### returns empty for reversed range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.substring(2, 1)).to_equal("")
```

</details>

#### returns empty for start at length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.substring(3, 3)).to_equal("")
```

</details>

### text slice expression s[start:end]

#### slices first five characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[0:5]).to_equal("abcde")
```

</details>

#### slices middle range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[2:5]).to_equal("cde")
```

</details>

#### slices single character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[0:1]).to_equal("a")
```

</details>

#### slices to end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[5:11]).to_equal("fghijk")
```

</details>

#### slices full string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[0:11]).to_equal("abcdefghijk")
```

</details>

#### returns empty for equal indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abcdefghijk"
expect(s[3:3]).to_equal("")
```

</details>

### text.char_at() method

#### returns first character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(0)).to_equal("h")
```

</details>

#### returns second character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(1)).to_equal("e")
```

</details>

#### returns middle character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(2)).to_equal("l")
```

</details>

#### returns last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(4)).to_equal("o")
```

</details>

#### returns empty for out-of-bounds index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(10)).to_equal("")
```

</details>

#### returns empty for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.char_at(-1)).to_equal("")
```

</details>

### text.char_code_at() method

#### returns code for 'a'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.char_code_at(0)).to_equal(97)
```

</details>

#### returns code for 'b'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.char_code_at(1)).to_equal(98)
```

</details>

#### returns code for 'A'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "ABC"
expect(s.char_code_at(0)).to_equal(65)
```

</details>

#### returns 0 for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
expect(s.char_code_at(10)).to_equal(0)
```

</details>

### text indexing s[i]

#### gets first character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
val ch = s[0]
expect(ch).to_equal("a")
```

</details>

#### gets middle character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
val ch = s[1]
expect(ch).to_equal("b")
```

</details>

#### gets last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
val ch = s[2]
expect(ch).to_equal("c")
```

</details>

#### gets space character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "a b"
val ch = s[1]
expect(ch).to_equal(" ")
```

</details>

### text methods regression

#### len() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".len()).to_equal(5)
expect("".len()).to_equal(0)
```

</details>

#### contains() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".contains("ell")).to_equal(true)
expect("hello".contains("xyz")).to_equal(false)
```

</details>

#### starts_with() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".starts_with("hel")).to_equal(true)
expect("hello".starts_with("xyz")).to_equal(false)
```

</details>

#### ends_with() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".ends_with("llo")).to_equal(true)
expect("hello".ends_with("xyz")).to_equal(false)
```

</details>

#### trim() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("  hello  ".trim()).to_equal("hello")
```

</details>

#### replace() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".replace("l", "r")).to_equal("herro")
```

</details>

#### split() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = "a,b,c".split(",")
expect(parts.len()).to_equal(3)
```

</details>

#### index_of() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = "hello".index_of("ll")
expect(idx ?? -1).to_equal(2)
```

</details>

#### to_upper() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".upper()).to_equal("HELLO")
```

</details>

#### to_lower() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("HELLO".lower()).to_equal("hello")
```

</details>

#### to_string() still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello".to_string()).to_equal("hello")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/bug/bug_report_text_slice_substring.md](doc/bug/bug_report_text_slice_substring.md)


</details>

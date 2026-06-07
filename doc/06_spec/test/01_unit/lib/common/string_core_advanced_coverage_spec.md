# String Core Coverage Specification

> Comprehensive branch-coverage tests for `src/lib/common/string_core.spl`. Exercises every exported function with inputs that trigger BOTH sides of every if/elif/else guard, targeting 90%+ branch coverage.

<!-- sdn-diagram:id=string_core_advanced_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_core_advanced_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_core_advanced_coverage_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_core_advanced_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 153 | 153 | 0 | 0 |

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
| Source | `test/01_unit/lib/common/string_core_advanced_coverage_spec.spl` |
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

### string_core - char_code_inline exhaustive digits

#### all digits

#### returns 49 for 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("1")).to_equal(49)
```

</details>

#### returns 50 for 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("2")).to_equal(50)
```

</details>

#### returns 51 for 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("3")).to_equal(51)
```

</details>

#### returns 52 for 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("4")).to_equal(52)
```

</details>

#### returns 54 for 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("6")).to_equal(54)
```

</details>

#### returns 55 for 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("7")).to_equal(55)
```

</details>

#### returns 56 for 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("8")).to_equal(56)
```

</details>

### string_core - char_code_inline exhaustive uppercase

#### uppercase B through L

#### returns 66 for B

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("B")).to_equal(66)
```

</details>

#### returns 67 for C

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("C")).to_equal(67)
```

</details>

#### returns 68 for D

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("D")).to_equal(68)
```

</details>

#### returns 69 for E

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("E")).to_equal(69)
```

</details>

#### returns 70 for F

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("F")).to_equal(70)
```

</details>

#### returns 71 for G

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("G")).to_equal(71)
```

</details>

#### returns 72 for H

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("H")).to_equal(72)
```

</details>

#### returns 73 for I

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("I")).to_equal(73)
```

</details>

#### returns 74 for J

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("J")).to_equal(74)
```

</details>

#### returns 75 for K

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("K")).to_equal(75)
```

</details>

#### returns 76 for L

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("L")).to_equal(76)
```

</details>

#### uppercase N through Y

#### returns 78 for N

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("N")).to_equal(78)
```

</details>

#### returns 79 for O

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("O")).to_equal(79)
```

</details>

#### returns 80 for P

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("P")).to_equal(80)
```

</details>

#### returns 81 for Q

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("Q")).to_equal(81)
```

</details>

#### returns 82 for R

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("R")).to_equal(82)
```

</details>

#### returns 83 for S

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("S")).to_equal(83)
```

</details>

#### returns 84 for T

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("T")).to_equal(84)
```

</details>

#### returns 85 for U

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("U")).to_equal(85)
```

</details>

#### returns 86 for V

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("V")).to_equal(86)
```

</details>

#### returns 87 for W

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("W")).to_equal(87)
```

</details>

#### returns 88 for X

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("X")).to_equal(88)
```

</details>

#### returns 89 for Y

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("Y")).to_equal(89)
```

</details>

### string_core - char_code_inline exhaustive lowercase

#### lowercase b through l

#### returns 98 for b

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("b")).to_equal(98)
```

</details>

#### returns 99 for c

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("c")).to_equal(99)
```

</details>

#### returns 100 for d

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("d")).to_equal(100)
```

</details>

#### returns 101 for e

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("e")).to_equal(101)
```

</details>

#### returns 102 for f

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("f")).to_equal(102)
```

</details>

#### returns 103 for g

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("g")).to_equal(103)
```

</details>

#### returns 104 for h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("h")).to_equal(104)
```

</details>

#### returns 105 for i

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("i")).to_equal(105)
```

</details>

#### returns 106 for j

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("j")).to_equal(106)
```

</details>

#### returns 107 for k

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("k")).to_equal(107)
```

</details>

#### returns 108 for l

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("l")).to_equal(108)
```

</details>

#### lowercase n through y

#### returns 110 for n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("n")).to_equal(110)
```

</details>

#### returns 111 for o

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("o")).to_equal(111)
```

</details>

#### returns 112 for p

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("p")).to_equal(112)
```

</details>

#### returns 113 for q

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("q")).to_equal(113)
```

</details>

#### returns 114 for r

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("r")).to_equal(114)
```

</details>

#### returns 115 for s

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("s")).to_equal(115)
```

</details>

#### returns 116 for t

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("t")).to_equal(116)
```

</details>

#### returns 117 for u

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("u")).to_equal(117)
```

</details>

#### returns 118 for v

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("v")).to_equal(118)
```

</details>

#### returns 119 for w

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("w")).to_equal(119)
```

</details>

#### returns 120 for x

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("x")).to_equal(120)
```

</details>

#### returns 121 for y

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_code_inline("y")).to_equal(121)
```

</details>

### string_core - char_from_code_inline exhaustive digits

#### all digit codes

#### returns 1 for 49

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(49)).to_equal("1")
```

</details>

#### returns 2 for 50

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(50)).to_equal("2")
```

</details>

#### returns 3 for 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(51)).to_equal("3")
```

</details>

#### returns 4 for 52

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(52)).to_equal("4")
```

</details>

#### returns 6 for 54

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(54)).to_equal("6")
```

</details>

#### returns 7 for 55

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(55)).to_equal("7")
```

</details>

#### returns 8 for 56

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(56)).to_equal("8")
```

</details>

### string_core - char_from_code_inline exhaustive uppercase

#### uppercase codes B through L

#### returns B for 66

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(66)).to_equal("B")
```

</details>

#### returns C for 67

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(67)).to_equal("C")
```

</details>

#### returns D for 68

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(68)).to_equal("D")
```

</details>

#### returns E for 69

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(69)).to_equal("E")
```

</details>

#### returns F for 70

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(70)).to_equal("F")
```

</details>

#### returns G for 71

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(71)).to_equal("G")
```

</details>

#### returns H for 72

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(72)).to_equal("H")
```

</details>

#### returns I for 73

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(73)).to_equal("I")
```

</details>

#### returns J for 74

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(74)).to_equal("J")
```

</details>

#### returns K for 75

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(75)).to_equal("K")
```

</details>

#### returns L for 76

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(76)).to_equal("L")
```

</details>

#### uppercase codes N through Y

#### returns N for 78

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(78)).to_equal("N")
```

</details>

#### returns O for 79

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(79)).to_equal("O")
```

</details>

#### returns P for 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(80)).to_equal("P")
```

</details>

#### returns Q for 81

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(81)).to_equal("Q")
```

</details>

#### returns R for 82

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(82)).to_equal("R")
```

</details>

#### returns S for 83

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(83)).to_equal("S")
```

</details>

#### returns T for 84

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(84)).to_equal("T")
```

</details>

#### returns U for 85

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(85)).to_equal("U")
```

</details>

#### returns V for 86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(86)).to_equal("V")
```

</details>

#### returns W for 87

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(87)).to_equal("W")
```

</details>

#### returns X for 88

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(88)).to_equal("X")
```

</details>

#### returns Y for 89

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(89)).to_equal("Y")
```

</details>

### string_core - char_from_code_inline exhaustive lowercase

#### lowercase codes b through l

#### returns b for 98

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(98)).to_equal("b")
```

</details>

#### returns c for 99

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(99)).to_equal("c")
```

</details>

#### returns d for 100

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(100)).to_equal("d")
```

</details>

#### returns e for 101

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(101)).to_equal("e")
```

</details>

#### returns f for 102

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(102)).to_equal("f")
```

</details>

#### returns g for 103

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(103)).to_equal("g")
```

</details>

#### returns h for 104

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(104)).to_equal("h")
```

</details>

#### returns i for 105

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(105)).to_equal("i")
```

</details>

#### returns j for 106

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(106)).to_equal("j")
```

</details>

#### returns k for 107

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(107)).to_equal("k")
```

</details>

#### returns l for 108

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(108)).to_equal("l")
```

</details>

#### lowercase codes n through y

#### returns n for 110

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(110)).to_equal("n")
```

</details>

#### returns o for 111

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(111)).to_equal("o")
```

</details>

#### returns p for 112

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(112)).to_equal("p")
```

</details>

#### returns q for 113

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(113)).to_equal("q")
```

</details>

#### returns r for 114

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(114)).to_equal("r")
```

</details>

#### returns s for 115

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(115)).to_equal("s")
```

</details>

#### returns t for 116

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(116)).to_equal("t")
```

</details>

#### returns u for 117

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(117)).to_equal("u")
```

</details>

#### returns v for 118

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(118)).to_equal("v")
```

</details>

#### returns w for 119

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(119)).to_equal("w")
```

</details>

#### returns x for 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(120)).to_equal("x")
```

</details>

#### returns y for 121

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(char_from_code_inline(121)).to_equal("y")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 153 |
| Active scenarios | 153 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Text Helpers Specification

> Tests for text helper functions: P1 case conversions (to_kebab_case, to_pascal_case, to_screaming_snake), character transforms (chars_map, tr, gsub), tokenization (split_n, cut, contains_any), and P2 string predicates, character ops, search, replacement, radix parsing, quote.

<!-- sdn-diagram:id=text_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Helpers Specification

Tests for text helper functions: P1 case conversions (to_kebab_case, to_pascal_case, to_screaming_snake), character transforms (chars_map, tr, gsub), tokenization (split_n, cut, contains_any), and P2 string predicates, character ops, search, replacement, radix parsing, quote.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEXT-P1, #TEXT-P2 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/stdlib_helpers.md |
| Source | `test/01_unit/lib/std/common/text_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for text helper functions: P1 case conversions (to_kebab_case,
to_pascal_case, to_screaming_snake), character transforms (chars_map,
tr, gsub), tokenization (split_n, cut, contains_any), and P2 string
predicates, character ops, search, replacement, radix parsing, quote.

## Scenarios

### to_kebab_case

#### converts PascalCase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("HelloWorld")).to_equal("hello-world")
```

</details>

#### converts snake_case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("hello_world")).to_equal("hello-world")
```

</details>

#### converts camelCase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("helloWorld")).to_equal("hello-world")
```

</details>

#### handles SCREAMING_SNAKE

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("HELLO_WORLD")).to_equal("hello-world")
```

</details>

#### preserves existing kebab

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("already-kebab")).to_equal("already-kebab")
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("")).to_equal("")
```

</details>

### to_pascal_case

#### converts snake_case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("hello_world")).to_equal("HelloWorld")
```

</details>

#### converts kebab-case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("hello-world")).to_equal("HelloWorld")
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("")).to_equal("")
```

</details>

### to_screaming_snake

#### converts camelCase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("helloWorld")).to_equal("HELLO_WORLD")
```

</details>

#### converts PascalCase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("HelloWorld")).to_equal("HELLO_WORLD")
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("")).to_equal("")
```

</details>

### chars_map

#### maps each character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chars_map("hello", &:upper)).to_equal("HELLO")
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chars_map("", \c: c)).to_equal("")
```

</details>

### tr

#### transliterates characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("hello", "elo", "ELO")).to_equal("hELLO")
```

</details>

#### maps character by character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("aabbcc", "abc", "xyz")).to_equal("xxyyzz")
```

</details>

#### handles empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("", "a", "b")).to_equal("")
```

</details>

#### handles empty from

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("hello", "", "")).to_equal("hello")
```

</details>

### gsub

#### replaces with callback

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gsub("hello world", "o", &:upper)).to_equal("hellO wOrld")
```

</details>

#### handles no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gsub("hello", "x", \_: "Y")).to_equal("hello")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gsub("", "a", \_: "b")).to_equal("")
```

</details>

### split_n

#### splits into at most n parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_n("a,b,c,d", ",", 2)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b,c,d")
```

</details>

#### returns full split if fewer than n parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_n("hello", ",", 5)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("hello")
```

</details>

### cut

#### cuts at separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (before, after, found) = cut("hello=world", "=")
expect(before).to_equal("hello")
expect(after).to_equal("world")
expect(found).to_equal(true)
```

</details>

#### returns false when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (before, after, found) = cut("hello", "=")
expect(before).to_equal("hello")
expect(after).to_equal("")
expect(found).to_equal(false)
```

</details>

### contains_any

#### finds vowels

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("hello", "aeiou")).to_equal(true)
```

</details>

#### finds no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("xyz", "aeiou")).to_equal(false)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("", "abc")).to_equal(false)
```

</details>

#### handles empty chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("hello", "")).to_equal(false)
```

</details>

### is_ascii

#### returns true for ASCII

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_ascii("hello")).to_equal(true)
```

</details>

#### returns true for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_ascii("")).to_equal(true)
```

</details>

### is_upper

#### returns true for uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_upper("HELLO")).to_equal(true)
```

</details>

#### returns false for mixed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_upper("Hello")).to_equal(false)
```

</details>

#### ignores non-alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_upper("HELLO 123")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_upper("")).to_equal(false)
```

</details>

### is_lower

#### returns true for lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_lower("hello")).to_equal(true)
```

</details>

#### returns false for mixed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_lower("Hello")).to_equal(false)
```

</details>

#### ignores non-alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_lower("hello 123")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_lower("")).to_equal(false)
```

</details>

### is_printable

#### returns true for printable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_printable("hello world")).to_equal(true)
```

</details>

#### returns true for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_printable("")).to_equal(true)
```

</details>

### is_title

#### returns true for title case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_title("Hello World")).to_equal(true)
```

</details>

#### returns false for lowercase start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_title("hello World")).to_equal(false)
```

</details>

#### returns true for single word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_title("Hello")).to_equal(true)
```

</details>

#### returns false for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_title("")).to_equal(false)
```

</details>

### delete_chars

#### deletes specified characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(delete_chars("hello world", "lo")).to_equal("he wrd")
```

</details>

#### handles empty chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(delete_chars("abc", "")).to_equal("abc")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(delete_chars("", "abc")).to_equal("")
```

</details>

### index_of_any

#### finds first vowel

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(index_of_any("hello", "aeiou")).to_equal(1)
```

</details>

#### returns nil when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(index_of_any("xyz", "aeiou")).to_be_nil()
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(index_of_any("", "abc")).to_be_nil()
```

</details>

### index_of_func

#### finds by predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(index_of_func("hello", _1 == "l")).to_equal(2)
```

</details>

#### returns nil when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(index_of_func("hello", _1 == "z")).to_be_nil()
```

</details>

### last_index_of_func

#### finds last by predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(last_index_of_func("hello", _1 == "l")).to_equal(3)
```

</details>

#### returns nil when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(last_index_of_func("hello", _1 == "z")).to_be_nil()
```

</details>

### fields_func

#### splits by custom predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_func("hello world\tfoo", _1 == " " or _1 == "\t")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("hello")
expect(result[1]).to_equal("world")
expect(result[2]).to_equal("foo")
```

</details>

#### handles consecutive separators

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fields_func("a  b", _1 == " ")
expect(result.len()).to_equal(2)
```

</details>

### replace_n

#### replaces first n occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(replace_n("aaa", "a", "b", 2)).to_equal("bba")
```

</details>

#### replaces first only

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(replace_n("hello", "l", "r", 1)).to_equal("herlo")
```

</details>

#### handles no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(replace_n("hello", "x", "y", 5)).to_equal("hello")
```

</details>

### multi_replace

#### replaces multiple pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = multi_replace("hello world", [("hello", "hi"), ("world", "earth")])
expect(result).to_equal("hi earth")
```

</details>

#### handles no pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(multi_replace("hello", [])).to_equal("hello")
```

</details>

### text_insert

#### inserts at middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_insert("hello", 2, "XY")).to_equal("heXYllo")
```

</details>

#### inserts at beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_insert("hello", 0, "AB")).to_equal("ABhello")
```

</details>

#### inserts at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_insert("hello", 5, "!")).to_equal("hello!")
```

</details>

### hex_to_int

#### parses hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("ff")).to_equal(255)
```

</details>

#### parses with 0x prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("0xFF")).to_equal(255)
```

</details>

#### parses simple hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("10")).to_equal(16)
```

</details>

#### returns nil for invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(hex_to_int("xyz")).to_be_nil()
```

</details>

### oct_to_int

#### parses octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(oct_to_int("77")).to_equal(63)
```

</details>

#### parses with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(oct_to_int("0o77")).to_equal(63)
```

</details>

### to_int_radix

#### parses binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("1010", 2)).to_equal(10)
```

</details>

#### parses hex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("ff", 16)).to_equal(255)
```

</details>

#### parses octal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("77", 8)).to_equal(63)
```

</details>

#### parses base 36

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("z", 36)).to_equal(35)
```

</details>

#### returns nil for invalid base

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("10", 1)).to_be_nil()
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_int_radix("", 10)).to_be_nil()
```

</details>

### text_quote

#### quotes simple string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_quote("hello")).to_equal("\"hello\"")
```

</details>

### split_after

#### keeps separator at end of each part

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_after("a,b,c", ",")
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a,")
expect(result[1]).to_equal("b,")
expect(result[2]).to_equal("c")
```

</details>

#### handles no separator found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_after("hello", ",")
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("hello")
```

</details>

### expandtabs

#### expands tabs to spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expandtabs("a\tb", 4)).to_equal("a   b")
```

</details>

#### handles no tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expandtabs("hello", 4)).to_equal("hello")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/stdlib_helpers.md](doc/02_requirements/feature/stdlib_helpers.md)


</details>

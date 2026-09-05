# Text Helpers P1 Specification

> Text Helpers P1 adds 9 utility functions to the text standard library module. These cover case conversion (kebab, pascal, screaming snake), character-level mapping (chars_map, tr, gsub), splitting (split_n), searching (contains_any), and partitioning (cut).

<!-- sdn-diagram:id=text_helpers_p1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_helpers_p1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_helpers_p1_spec -> std
text_helpers_p1_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_helpers_p1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Helpers P1 Specification

Text Helpers P1 adds 9 utility functions to the text standard library module. These cover case conversion (kebab, pascal, screaming snake), character-level mapping (chars_map, tr, gsub), splitting (split_n), searching (contains_any), and partitioning (cut).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TEXT-P1-001 to #TEXT-P1-009 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/helpers/text_helpers_p1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Text Helpers P1 adds 9 utility functions to the text standard library module.
These cover case conversion (kebab, pascal, screaming snake), character-level
mapping (chars_map, tr, gsub), splitting (split_n), searching (contains_any),
and partitioning (cut).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Case conversion | Transform between naming conventions (kebab, pascal, screaming snake) |
| chars_map | Apply a function to each character and reassemble |
| tr | Character-level transliteration (like Unix tr) |
| split_n | Split into at most n parts |
| contains_any | Check if text contains any character from a set |
| cut | Partition text around first occurrence of separator |
| gsub | Global substitution with a callback function |

## Related Specifications

- [text_advanced](../../src/lib/common/text_advanced.spl) - Existing case conversion (snake, camel, title)

## Scenarios

### to_kebab_case

#### from PascalCase

#### converts HelloWorld to hello-world

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("HelloWorld")).to_equal("hello-world")
```

</details>

#### from snake_case

#### converts hello_world to hello-world

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("hello_world")).to_equal("hello-world")
```

</details>

#### from camelCase

#### converts helloWorld to hello-world

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("helloWorld")).to_equal("hello-world")
```

</details>

#### from SCREAMING_SNAKE

#### converts HELLO_WORLD to hello-world

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("HELLO_WORLD")).to_equal("hello-world")
```

</details>

#### when already kebab-case

#### returns already-kebab unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("already-kebab")).to_equal("already-kebab")
```

</details>

#### when empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_kebab_case("")).to_equal("")
```

</details>

### to_pascal_case

#### from snake_case

#### converts hello_world to HelloWorld

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("hello_world")).to_equal("HelloWorld")
```

</details>

#### from kebab-case

#### converts hello-world to HelloWorld

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("hello-world")).to_equal("HelloWorld")
```

</details>

#### from camelCase

#### converts helloWorld to HelloWorld

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("helloWorld")).to_equal("HelloWorld")
```

</details>

#### from SCREAMING_SNAKE

#### converts HELLO_WORLD to HelloWorld

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("HELLO_WORLD")).to_equal("HelloWorld")
```

</details>

#### when empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_pascal_case("")).to_equal("")
```

</details>

### to_screaming_snake

#### from camelCase

#### converts helloWorld to HELLO_WORLD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("helloWorld")).to_equal("HELLO_WORLD")
```

</details>

#### from kebab-case

#### converts hello-world to HELLO_WORLD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("hello-world")).to_equal("HELLO_WORLD")
```

</details>

#### from PascalCase

#### converts HelloWorld to HELLO_WORLD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("HelloWorld")).to_equal("HELLO_WORLD")
```

</details>

#### from snake_case

#### converts hello_world to HELLO_WORLD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("hello_world")).to_equal("HELLO_WORLD")
```

</details>

#### when empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(to_screaming_snake("")).to_equal("")
```

</details>

### chars_map

#### with to_upper transform

#### uppercases every character

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chars_map("hello", &:upper)).to_equal("HELLO")
```

</details>

#### with conditional replacement

#### replaces matching characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = chars_map("abc", \c: if c == "b": "X" else: c)
expect(result).to_equal("aXc")
```

</details>

#### when empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chars_map("", \c: c)).to_equal("")
```

</details>

### tr

#### with matching characters

#### transliterates elo to ELO

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("hello", "elo", "ELO")).to_equal("hELLO")
```

</details>

#### with full replacement

#### transliterates abc to xyz

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("aabbcc", "abc", "xyz")).to_equal("xxyyzz")
```

</details>

#### with empty from and to

#### returns text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("hello", "", "")).to_equal("hello")
```

</details>

#### when text is empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tr("", "a", "b")).to_equal("")
```

</details>

### split_n

#### when n is less than total parts

#### splits into exactly n parts

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

#### when n exceeds total parts

#### returns all available parts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_n("a,b,c", ",", 5)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("b")
expect(result[2]).to_equal("c")
```

</details>

#### when separator not found

#### returns single-element list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_n("hello", ",", 2)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("hello")
```

</details>

#### when text is empty

#### returns list with empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = split_n("", ",", 2)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("")
```

</details>

### contains_any

#### when text contains a matching character

#### returns true for vowels in hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("hello", "aeiou")).to_equal(true)
```

</details>

#### when no characters match

#### returns false for vowels in xyz

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("xyz", "aeiou")).to_equal(false)
```

</details>

#### when text is empty

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("", "abc")).to_equal(false)
```

</details>

#### when chars is empty

#### returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contains_any("hello", "")).to_equal(false)
```

</details>

### cut

#### when separator is found

#### splits at first occurrence

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

#### when separator appears multiple times

#### splits only at first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (before, after, found) = cut("hello=world=foo", "=")
expect(before).to_equal("hello")
expect(after).to_equal("world=foo")
expect(found).to_equal(true)
```

</details>

#### when separator is not found

#### returns full text with empty after and false

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

#### when text is empty

#### returns empty parts with false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (before, after, found) = cut("", "=")
expect(before).to_equal("")
expect(after).to_equal("")
expect(found).to_equal(false)
```

</details>

### gsub

#### with uppercase transform

#### uppercases matched characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = gsub("hello world", "o", &:upper)
expect(result).to_equal("hellO wOrld")
```

</details>

#### with constant replacement

#### replaces match with constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = gsub("abc", "b", \m: "BB")
expect(result).to_equal("aBBc")
```

</details>

#### when pattern has no match

#### returns text unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = gsub("hello", "x", \m: "Y")
expect(result).to_equal("hello")
```

</details>

#### when text is empty

#### returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = gsub("", "a", \m: "b")
expect(result).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

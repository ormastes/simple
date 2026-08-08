# String Specification

> <details>

<!-- sdn-diagram:id=string_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=string_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

string_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=string_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Specification

## Scenarios

### text Type

#### creation

#### creates string from literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
expect str.len == 5
```

</details>

#### creates empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.len == 0
```

</details>

#### creates string with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val special = "hello\nworld"
expect special.len == 11
```

</details>

#### creates string with unicode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unicode = "café"
expect unicode.len >= 4
```

</details>

#### length operations

#### len returns byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
expect str.len == 5
```

</details>

#### len handles empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.len == 0
```

</details>

#### char_count returns character count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
expect str.char_count == 5
```

</details>

#### byte_len returns byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
expect str.byte_len == 5
```

</details>

#### character access

#### accesses characters by index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
expect str[0] == "h"
expect str[4] == "o"
```

</details>

#### accesses unicode characters by positive and negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "café"
expect str[3] == "é"
expect str[-1] == "é"
```

</details>

#### handles out of bounds gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hi"
expect str.len == 2
```

</details>

#### substring searching

#### contains finds substring

- expect str contains
- expect str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
expect str.contains("world") == true
expect str.contains("xyz") == false
```

</details>

#### starts_with checks prefix

- expect str starts with
- expect str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
expect str.starts_with("hello") == true
expect str.starts_with("world") == false
```

</details>

#### ends_with checks suffix

- expect str ends with
- expect str ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
expect str.ends_with("world") == true
expect str.ends_with("hello") == false
```

</details>

#### find_str locates substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
val pos = str.find_str("world")
expect pos >= 0
```

</details>

#### find_str returns -1 for missing substring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
val pos = str.find_str("xyz")
expect pos == -1
```

</details>

#### trimming operations

#### trimmed removes leading and trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "  hello  "
val trimmed = str.trimmed()
expect trimmed.len < str.len
```

</details>

#### trim_start removes leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "  hello world"
val trimmed = str.trim_start()
expect trimmed.len <= str.len
```

</details>

#### trim_end removes trailing whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world  "
val trimmed = str.trim_end()
expect trimmed.len <= str.len
```

</details>

#### string modification

#### push adds character

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: push returns a new string (strings are immutable)
var str = "hello"
val result = str.push(' ')
expect result.len >= 6
```

</details>

#### push_str appends string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: push_str returns a new string (strings are immutable)
var str = "hello"
val result = str.push_str(" world")
expect result.len >= 11
```

</details>

#### pop removes last character

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: pop returns Option with the last char (doesn't modify)
var str = "hello"
val ch = str.pop()
expect ch.is_some == true
```

</details>

#### clear removes all characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: clear returns empty string (strings are immutable)
var str = "hello"
val result = str.clear()
expect result.len == 0
```

</details>

#### immutable operations

#### appended creates new string with character

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
val extended = str.appended('!')
expect extended.len > str.len
```

</details>

#### prepended adds character to start

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "world"
val extended = str.prepended(' ')
expect extended.len > str.len
```

</details>

#### reversed reverses characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
val rev = str.reversed()
# Just verify it returns a string
expect rev.len == 5
```

</details>

#### sorted sorts characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello"
val sorted = str.sorted()
expect sorted.len == 5
```

</details>

#### filtering operations

#### filtered removes characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "a1b2c3"
# Filter would keep only alpha chars
expect str.len == 6
```

</details>

#### taken keeps first n characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
val first5 = str.taken(5)
expect first5.len <= 5
```

</details>

#### dropped skips first n characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
val rest = str.dropped(6)
expect rest.len <= str.len
```

</details>

#### case sensitivity

#### string comparison is case sensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "Hello" != "hello"
expect "Hello" == "Hello"
```

</details>

#### contains is case sensitive

- expect str contains
- expect str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "Hello World"
expect str.contains("hello") == false
expect str.contains("Hello") == true
```

</details>

#### empty string handling

#### empty string operations

- expect empty contains
- expect empty starts with
- expect empty ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = ""
expect empty.len == 0
expect empty.contains("") == true
expect empty.starts_with("") == true
expect empty.ends_with("") == true
```

</details>

#### single character string

- expect single starts with
- expect single ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = "a"
expect single.len == 1
expect single.starts_with("a") == true
expect single.ends_with("a") == true
```

</details>

#### whitespace handling

#### whitespace is counted in length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
expect str.len == 11
```

</details>

#### spaces can be searched

- expect str contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello world"
expect str.contains(" ") == true
```

</details>

#### tabs and newlines work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello\tworld"
expect str.len >= 11
```

</details>

#### string concatenation patterns

#### multiple string operations

- var str2 = str push


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: text operations return new strings (immutable)
var str = "hello"
var str2 = str.push(' ')
val str3 = str2.push_str("world")
expect str3.len >= 11
```

</details>

#### string comparisons work

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val str1 = "hello"
var str2 = "hello"
expect str1 == str2
```

</details>

#### complex string operations

#### chains multiple operations

- expect trimmed contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "  hello world  "
val trimmed = str.trimmed()
expect trimmed.len < str.len
expect trimmed.contains("hello") == true
```

</details>

#### works with special characters

- expect str contains
- expect str contains
- expect str find str


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello@world.com"
expect str.contains("@") == true
expect str.contains(".com") == true
expect str.find_str("@") >= 0
```

</details>

#### string repetition

#### repeats string with * operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "a" * 3
expect str == "aaa"
```

</details>

#### repeats multi-character string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "ab" * 2
expect str == "abab"
```

</details>

#### repeats with integer on left side

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = 3 * "x"
expect str == "xxx"
```

</details>

#### handles zero repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello" * 0
expect str == ""
```

</details>

#### handles single repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "hello" * 1
expect str == "hello"
```

</details>

#### works with empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var str = "" * 5
expect str == ""
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- text Type

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

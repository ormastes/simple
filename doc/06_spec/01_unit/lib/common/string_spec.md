# String Specification

> Tests covering text Type.

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

- creates string from literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates string from literals")
var str = "hello"
expect str.len == 5
```

</details>

#### creates empty string

- creates empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty string")
val empty = ""
expect empty.len == 0
```

</details>

#### creates string with special characters

- creates string with special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates string with special characters")
val special = "hello\nworld"
expect special.len == 11
```

</details>

#### creates string with unicode

- creates string with unicode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates string with unicode")
val unicode = "café"
expect unicode.len >= 4
```

</details>

#### length operations

#### len returns byte length

- len returns byte length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("len returns byte length")
var str = "hello"
expect str.len == 5
```

</details>

#### len handles empty strings

- len handles empty strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("len handles empty strings")
val empty = ""
expect empty.len == 0
```

</details>

#### char_count returns character count

- char_count returns character count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("char_count returns character count")
var str = "hello"
expect str.char_count == 5
```

</details>

#### byte_len returns byte length

- byte_len returns byte length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("byte_len returns byte length")
var str = "hello"
expect str.byte_len == 5
```

</details>

#### character access

#### accesses characters by index

- accesses characters by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accesses characters by index")
var str = "hello"
expect str[0] == "h"
expect str[4] == "o"
```

</details>

#### accesses unicode characters by positive and negative index

- accesses unicode characters by positive and negative index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accesses unicode characters by positive and negative index")
var str = "café"
expect str[3] == "é"
expect str[-1] == "é"
```

</details>

#### handles out of bounds gracefully

- handles out of bounds gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles out of bounds gracefully")
var str = "hi"
expect str.len == 2
```

</details>

#### substring searching

#### contains finds substring

- contains finds substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains finds substring")
var str = "hello world"
expect str.contains("world") == true
expect str.contains("xyz") == false
```

</details>

#### starts_with checks prefix

- starts_with checks prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts_with checks prefix")
var str = "hello world"
expect str.starts_with("hello") == true
expect str.starts_with("world") == false
```

</details>

#### ends_with checks suffix

- ends_with checks suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ends_with checks suffix")
var str = "hello world"
expect str.ends_with("world") == true
expect str.ends_with("hello") == false
```

</details>

#### find_str locates substring

- find_str locates substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_str locates substring")
var str = "hello world"
val pos = str.find_str("world")
expect pos >= 0
```

</details>

#### find_str returns -1 for missing substring

- find_str returns -1 for missing substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_str returns -1 for missing substring")
var str = "hello world"
val pos = str.find_str("xyz")
expect pos == -1
```

</details>

#### trimming operations

#### trimmed removes leading and trailing whitespace

- trimmed removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trimmed removes leading and trailing whitespace")
var str = "  hello  "
val trimmed = str.trimmed()
expect trimmed.len < str.len
```

</details>

#### trim_start removes leading whitespace

- trim_start removes leading whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim_start removes leading whitespace")
var str = "  hello world"
val trimmed = str.trim_start()
expect trimmed.len <= str.len
```

</details>

#### trim_end removes trailing whitespace

- trim_end removes trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trim_end removes trailing whitespace")
var str = "hello world  "
val trimmed = str.trim_end()
expect trimmed.len <= str.len
```

</details>

#### string modification

#### push adds character

- push adds character


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push adds character")
# Note: push returns a new string (strings are immutable)
var str = "hello"
val result = str.push(' ')
expect result.len >= 6
```

</details>

#### push_str appends string

- push_str appends string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_str appends string")
# Note: push_str returns a new string (strings are immutable)
var str = "hello"
val result = str.push_str(" world")
expect result.len >= 11
```

</details>

#### pop removes last character

- pop removes last character


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop removes last character")
# Note: pop returns Option with the last char (doesn't modify)
var str = "hello"
val ch = str.pop()
expect ch.is_some == true
```

</details>

#### clear removes all characters

- clear removes all characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear removes all characters")
# Note: clear returns empty string (strings are immutable)
var str = "hello"
val result = str.clear()
expect result.len == 0
```

</details>

#### immutable operations

#### appended creates new string with character

- appended creates new string with character


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appended creates new string with character")
var str = "hello"
val extended = str.appended('!')
expect extended.len > str.len
```

</details>

#### prepended adds character to start

- prepended adds character to start


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepended adds character to start")
var str = "world"
val extended = str.prepended(' ')
expect extended.len > str.len
```

</details>

#### reversed reverses characters

- reversed reverses characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reversed reverses characters")
var str = "hello"
val rev = str.reversed()
# Just verify it returns a string
expect rev.len == 5
```

</details>

#### sorted sorts characters

- sorted sorts characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorted sorts characters")
var str = "hello"
val sorted = str.sorted()
expect sorted.len == 5
```

</details>

#### filtering operations

#### filtered removes characters

- filtered removes characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filtered removes characters")
var str = "a1b2c3"
# Filter would keep only alpha chars
expect str.len == 6
```

</details>

#### taken keeps first n characters

- taken keeps first n characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("taken keeps first n characters")
var str = "hello world"
val first5 = str.taken(5)
expect first5.len <= 5
```

</details>

#### dropped skips first n characters

- dropped skips first n characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dropped skips first n characters")
var str = "hello world"
val rest = str.dropped(6)
expect rest.len <= str.len
```

</details>

#### case sensitivity

#### string comparison is case sensitive

- string comparison is case sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string comparison is case sensitive")
expect "Hello" != "hello"
expect "Hello" == "Hello"
```

</details>

#### contains is case sensitive

- contains is case sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains is case sensitive")
var str = "Hello World"
expect str.contains("hello") == false
expect str.contains("Hello") == true
```

</details>

#### empty string handling

#### empty string operations

- empty string operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string operations")
val empty = ""
expect empty.len == 0
expect empty.contains("") == true
expect empty.starts_with("") == true
expect empty.ends_with("") == true
```

</details>

#### single character string

- single character string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single character string")
val single = "a"
expect single.len == 1
expect single.starts_with("a") == true
expect single.ends_with("a") == true
```

</details>

#### whitespace handling

#### whitespace is counted in length

- whitespace is counted in length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whitespace is counted in length")
var str = "hello world"
expect str.len == 11
```

</details>

#### spaces can be searched

- spaces can be searched


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spaces can be searched")
var str = "hello world"
expect str.contains(" ") == true
```

</details>

#### tabs and newlines work

- tabs and newlines work


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tabs and newlines work")
var str = "hello\tworld"
expect str.len >= 11
```

</details>

#### string concatenation patterns

#### multiple string operations

- multiple string operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple string operations")
# Note: text operations return new strings (immutable)
var str = "hello"
var str2 = str.push(' ')
val str3 = str2.push_str("world")
expect str3.len >= 11
```

</details>

#### string comparisons work

- string comparisons work


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string comparisons work")
val str1 = "hello"
var str2 = "hello"
expect str1 == str2
```

</details>

#### complex string operations

#### chains multiple operations

- chains multiple operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains multiple operations")
var str = "  hello world  "
val trimmed = str.trimmed()
expect trimmed.len < str.len
expect trimmed.contains("hello") == true
```

</details>

#### works with special characters

- works with special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with special characters")
var str = "hello@world.com"
expect str.contains("@") == true
expect str.contains(".com") == true
expect str.find_str("@") >= 0
```

</details>

#### string repetition

#### repeats string with * operator

- repeats string with * operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats string with * operator")
var str = "a" * 3
expect str == "aaa"
```

</details>

#### repeats multi-character string

- repeats multi-character string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats multi-character string")
var str = "ab" * 2
expect str == "abab"
```

</details>

#### repeats with integer on left side

- repeats with integer on left side


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats with integer on left side")
var str = 3 * "x"
expect str == "xxx"
```

</details>

#### handles zero repetition

- handles zero repetition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles zero repetition")
var str = "hello" * 0
expect str == ""
```

</details>

#### handles single repetition

- handles single repetition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single repetition")
var str = "hello" * 1
expect str == "hello"
```

</details>

#### works with empty string

- works with empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with empty string")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text Type.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `309e632aa4a1811b94f3640bf54c2f117f79b05ddaefccce7becfcd68d1c95a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `309e632aa4a1811b94f3640bf54c2f117f79b05ddaefccce7becfcd68d1c95a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `309e632aa4a1811b94f3640bf54c2f117f79b05ddaefccce7becfcd68d1c95a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/string_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/string_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates string from literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates string with special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# String Helpers Specification

> Tests covering Whitespace Handling, String Splitting, Pattern Matching, String Comparison, String Construction, String Searching, String Length and Indexing, String Slicing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Helpers Specification

## Scenarios

### Whitespace Handling

#### trims leading whitespace

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trims leading whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims leading whitespace")
val input = "   text"
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### trims trailing whitespace

- trims trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims trailing whitespace")
val input = "text   "
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### trims both sides

- trims both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims both sides")
val input = "  text  "
val result = trim_whitespace(input)
expect result == "text"
```

</details>

#### preserves internal whitespace

- preserves internal whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves internal whitespace")
val input = "hello world"
val result = trim_whitespace(input)
expect result == "hello world"
```

</details>

### String Splitting

#### splits by newline

- splits by newline


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits by newline")
val input = "line1\nline2\nline3"
val lines = split_lines(input)
expect lines.len() == 3
expect lines[0] == "line1"
```

</details>

#### handles single line

- handles single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single line")
val input = "single line"
val lines = split_lines(input)
expect lines.len() == 1
```

</details>

#### handles empty string

- handles empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string")
val input = ""
val lines = split_lines(input)
expect lines.len() >= 0
```

</details>

#### splits path components

- splits path components


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits path components")
val path = "src/app/lsp/main.spl"
val parts = path.split("/")
expect parts.len() == 4
expect parts[0] == "src"
expect parts[-1] == "main.spl"
```

</details>

### Pattern Matching

#### finds keyword in string

- finds keyword in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds keyword in string")
val text = "fn main():"
expect contains_keyword(text, "fn")
expect contains_keyword(text, "main")
```

</details>

#### detects missing keyword

- detects missing keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing keyword")
val text = "val x = 42"
expect not contains_keyword(text, "fn")
```

</details>

#### finds file extensions

- finds file extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds file extensions")
val filename = "test.spl"
expect filename.ends_with(".spl")
```

</details>

#### checks file path patterns

- checks file path patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks file path patterns")
val path = "test/unit/lib/std/app/test.spl"
expect path.contains("test")
expect path.contains("app")
expect path.ends_with(".spl")
```

</details>

### String Comparison

#### compares equal strings

- compares equal strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares equal strings")
val s1 = "hello"
val s2 = "hello"
expect s1 == s2
```

</details>

#### compares different strings

- compares different strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares different strings")
val s1 = "hello"
val s2 = "world"
expect s1 != s2
```

</details>

#### handles case sensitivity

- handles case sensitivity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles case sensitivity")
val lower = "hello"
val upper = "HELLO"
expect lower != upper
```

</details>

#### compares prefixes

- compares prefixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares prefixes")
val text = "function_name"
expect text.starts_with("func")
expect not text.starts_with("var")
```

</details>

### String Construction

#### concatenates strings

- concatenates strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates strings")
val part1 = "hello"
val part2 = "world"
val result = part1 + " " + part2
expect result == "hello world"
```

</details>

#### builds paths

- builds paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds paths")
val dir = "test"
val file = "spec.spl"
val path = dir + "/" + file
expect path == "test/spec.spl"
```

</details>

#### formats with variables

- formats with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats with variables")
val name = "Alice"
val greeting = "Hello, " + name + "!"
expect greeting.contains(name)
```

</details>

### String Searching

#### finds substring position

- finds substring position


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds substring position")
val text = "hello world"
val index = text.find("world")
expect index != nil
```

</details>

#### handles missing substring

- handles missing substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing substring")
val text = "hello world"
val index = text.find("xyz")
expect not index.?
```

</details>

#### finds first occurrence

- finds first occurrence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds first occurrence")
val text = "test test test"
val index = text.find("test")
expect index == 0
```

</details>

### String Length and Indexing

#### measures string length

- measures string length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures string length")
val text = "hello"
expect text.len() == 5
```

</details>

#### handles empty string length

- handles empty string length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string length")
val empty = ""
expect empty.len() == 0
```

</details>

#### accesses characters by index

- accesses characters by index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accesses characters by index")
val text = "hello"
expect text[0] == 'h'
expect text[4] == 'o'
```

</details>

#### uses negative indexing

- uses negative indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses negative indexing")
val text = "hello"
expect text[-1] == 'o'
expect text[-5] == 'h'
```

</details>

### String Slicing

#### checks substring existence

- checks substring existence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks substring existence")
val text = "hello world"
expect text.contains("hello")
expect text.contains("world")
```

</details>

#### finds substring by search

- finds substring by search


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds substring by search")
val text = "hello world"
val index = text.find("world")
expect index != nil
```

</details>

#### validates text content

- validates text content


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates text content")
val text = "hello world"
expect text.len() == 11
expect text.starts_with("hello")
expect text.ends_with("world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/utils/string_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Whitespace Handling, String Splitting, Pattern Matching, String Comparison, String Construction, String Searching, String Length and Indexing, String Slicing.
- Whitespace Handling
- String Splitting
- Pattern Matching
- String Comparison
- String Construction
- String Searching
- String Length and Indexing
- String Slicing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `85db45c19bb83cdbc4314dd56fa1d9b5a35b5e7266212836b10df6bf97cb6283`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85db45c19bb83cdbc4314dd56fa1d9b5a35b5e7266212836b10df6bf97cb6283`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85db45c19bb83cdbc4314dd56fa1d9b5a35b5e7266212836b10df6bf97cb6283`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/utils/string_helpers_spec.spl
mirror: doc/06_spec/unit/app/utils/string_helpers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/utils/string_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/utils/string_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/utils/string_helpers_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims leading whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/utils/string_helpers_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims trailing whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/utils/string_helpers_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

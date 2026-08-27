# String Builder Specification

> Tests covering StringBuilder, basic construction, push and to_text, len, is_empty, clear.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Builder Specification

## Scenarios

### StringBuilder

### basic construction

#### creates empty builder

- creates empty builder
   - Expected: sb.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates empty builder")
var sb = string_builder()
expect(sb.is_empty()).to_equal(true)
```

</details>

#### creates builder from text

- creates builder from text
   - Expected: sb.to_text() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates builder from text")
var sb = string_builder_from("hello")
expect(sb.to_text()).to_equal("hello")
```

</details>

### push and to_text

#### pushes a single part

- pushes a single part
   - Expected: sb.to_text() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pushes a single part")
var sb = string_builder()
sb.push("hello")
expect(sb.to_text()).to_equal("hello")
```

</details>

#### pushes multiple parts

- pushes multiple parts
   - Expected: sb.to_text() equals `Hello, World!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pushes multiple parts")
var sb = string_builder()
sb.push("Hello, ")
sb.push("World!")
expect(sb.to_text()).to_equal("Hello, World!")
```

</details>

#### push_line appends newline

- push_line appends newline
   - Expected: sb.to_text() equals `first\nsecond`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("push_line appends newline")
var sb = string_builder()
sb.push_line("first")
sb.push("second")
expect(sb.to_text()).to_equal("first\nsecond")
```

</details>

### len

#### returns zero for empty

- returns zero for empty
   - Expected: sb.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero for empty")
var sb = string_builder()
expect(sb.len()).to_equal(0)
```

</details>

#### returns total character count

- returns total character count
   - Expected: sb.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns total character count")
var sb = string_builder()
sb.push("abc")
sb.push("de")
expect(sb.len()).to_equal(5)
```

</details>

### is_empty

#### true for new builder

- true for new builder
   - Expected: sb.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("true for new builder")
var sb = string_builder()
expect(sb.is_empty()).to_equal(true)
```

</details>

#### false after push

- false after push
   - Expected: sb.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("false after push")
var sb = string_builder()
sb.push("x")
expect(sb.is_empty()).to_equal(false)
```

</details>

### clear

#### clears all parts

- clears all parts
   - Expected: sb.is_empty() is true
   - Expected: sb.to_text() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears all parts")
var sb = string_builder()
sb.push("data")
sb.clear()
expect(sb.is_empty()).to_equal(true)
expect(sb.to_text()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StringBuilder, basic construction, push and to_text, len, is_empty, clear.
- StringBuilder
- basic construction
- push and to_text
- len
- is_empty
- clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0660ec9a25ec64293e0558420e9a053536639bedf26151ed2297bd6a367dde35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0660ec9a25ec64293e0558420e9a053536639bedf26151ed2297bd6a367dde35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0660ec9a25ec64293e0558420e9a053536639bedf26151ed2297bd6a367dde35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/string_builder_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_builder_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/string_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_builder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/string_builder_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty builder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_builder_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates builder from text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_builder_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes a single part' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# String Builder Enhanced Specification

> Tests covering StringBuilder push_all, StringBuilder push_sep, StringBuilder to_text_sep, StringBuilder from_parts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Builder Enhanced Specification

## Scenarios

### StringBuilder push_all

#### pushes multiple parts at once

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pushes multiple parts at once
   - Expected: sb.to_text() equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pushes multiple parts at once")
val sb = string_builder()
sb.push_all(["hello", " ", "world"])
expect(sb.to_text()).to_equal("hello world")
```

</details>

#### handles empty array

- handles empty array
   - Expected: sb.to_text() equals `start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
val sb = string_builder()
sb.push("start")
sb.push_all([])
expect(sb.to_text()).to_equal("start")
```

</details>

#### handles single element array

- handles single element array
   - Expected: sb.to_text() equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single element array")
val sb = string_builder()
sb.push_all(["only"])
expect(sb.to_text()).to_equal("only")
```

</details>

### StringBuilder push_sep

#### adds separator between parts

- adds separator between parts
   - Expected: sb.to_text() equals `a, b, c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds separator between parts")
val sb = string_builder()
sb.push_sep("a", ", ")
sb.push_sep("b", ", ")
sb.push_sep("c", ", ")
expect(sb.to_text()).to_equal("a, b, c")
```

</details>

#### does not add separator before first part

- does not add separator before first part
   - Expected: sb.to_text() equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not add separator before first part")
val sb = string_builder()
sb.push_sep("first", ", ")
expect(sb.to_text()).to_equal("first")
```

</details>

#### works with newline separator

- works with newline separator
   - Expected: sb.to_text() equals `line1\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with newline separator")
val sb = string_builder()
sb.push_sep("line1", "\n")
sb.push_sep("line2", "\n")
expect(sb.to_text()).to_equal("line1\nline2")
```

</details>

### StringBuilder to_text_sep

#### joins parts with separator

- joins parts with separator
   - Expected: sb.to_text_sep(", ") equals `x, y, z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("joins parts with separator")
val sb = string_builder()
sb.push("x")
sb.push("y")
sb.push("z")
expect(sb.to_text_sep(", ")).to_equal("x, y, z")
```

</details>

#### returns empty string for empty builder

- returns empty string for empty builder
   - Expected: sb.to_text_sep(", ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for empty builder")
val sb = string_builder()
expect(sb.to_text_sep(", ")).to_equal("")
```

</details>

#### returns single part without separator

- returns single part without separator
   - Expected: sb.to_text_sep(", ") equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns single part without separator")
val sb = string_builder()
sb.push("only")
expect(sb.to_text_sep(", ")).to_equal("only")
```

</details>

### StringBuilder from_parts

#### creates builder from parts list

- creates builder from parts list
   - Expected: sb.to_text() equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates builder from parts list")
val sb = StringBuilder.from_parts(["a", "b", "c"])
expect(sb.to_text()).to_equal("abc")
```

</details>

#### creates builder from empty list

- creates builder from empty list
   - Expected: sb.to_text() equals ``
   - Expected: sb.is_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates builder from empty list")
val sb = StringBuilder.from_parts([])
expect(sb.to_text()).to_equal("")
expect(sb.is_empty()).to_equal(true)
```

</details>

#### allows further pushes after from_parts

- allows further pushes after from_parts
   - Expected: sb.to_text() equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows further pushes after from_parts")
val sb = StringBuilder.from_parts(["hello"])
sb.push(" world")
expect(sb.to_text()).to_equal("hello world")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_builder_enhanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering StringBuilder push_all, StringBuilder push_sep, StringBuilder to_text_sep, StringBuilder from_parts.
- StringBuilder push_all
- StringBuilder push_sep
- StringBuilder to_text_sep
- StringBuilder from_parts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `f098ef12089c539850f263ee3e5ab4557f3528a7e51e74d7a44a224ee212d8e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f098ef12089c539850f263ee3e5ab4557f3528a7e51e74d7a44a224ee212d8e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f098ef12089c539850f263ee3e5ab4557f3528a7e51e74d7a44a224ee212d8e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/string_builder_enhanced_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_builder_enhanced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/string_builder_enhanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_builder_enhanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_builder_enhanced_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes multiple parts at once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_builder_enhanced_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_builder_enhanced_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles single element array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

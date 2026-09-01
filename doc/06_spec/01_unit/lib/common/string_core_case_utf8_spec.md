# String Core Case Utf8 Specification

> Tests covering str_to_lower / str_to_upper — multibyte UTF-8 safety, same defect class — sibling s[i]-vs-byte-len functions in string_core.spl.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Core Case Utf8 Specification

## Scenarios

### str_to_lower / str_to_upper — multibyte UTF-8 safety

#### lowercases an accented word without crashing (reproduces the bug)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowercases an accented word without crashing (reproduces the bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lowercases an accented word without crashing (reproduces the bug)")
assert_equal(str_to_lower("CAF\u{e9}"), "caf\u{e9}")
```

</details>

#### uppercases an accented word without crashing

- uppercases an accented word without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uppercases an accented word without crashing")
assert_equal(str_to_upper("caf\u{e9}"), "CAF\u{e9}")
```

</details>

#### passes an emoji (4-byte codepoint) through str_to_lower untouched

- passes an emoji (4-byte codepoint) through str_to_lower untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes an emoji (4-byte codepoint) through str_to_lower untouched")
assert_equal(str_to_lower("HI\u{1F600}BYE"), "hi\u{1F600}bye")
```

</details>

#### passes an emoji through str_to_upper untouched

- passes an emoji through str_to_upper untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes an emoji through str_to_upper untouched")
assert_equal(str_to_upper("hi\u{1F600}bye"), "HI\u{1F600}BYE")
```

</details>

#### handles multibyte at position 0

- handles multibyte at position 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at position 0")
assert_equal(str_to_lower("\u{e9}ABC"), "\u{e9}abc")
assert_equal(str_to_upper("\u{e9}abc"), "\u{e9}ABC")
```

</details>

#### handles multibyte at the last position

- handles multibyte at the last position


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multibyte at the last position")
assert_equal(str_to_lower("ABC\u{e9}"), "abc\u{e9}")
assert_equal(str_to_upper("abc\u{e9}"), "ABC\u{e9}")
```

</details>

#### handles a pure-multibyte string

- handles a pure-multibyte string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles a pure-multibyte string")
assert_equal(str_to_lower("\u{e9}\u{e8}\u{ea}"), "\u{e9}\u{e8}\u{ea}")
assert_equal(str_to_upper("\u{e9}\u{e8}\u{ea}"), "\u{e9}\u{e8}\u{ea}")
```

</details>

#### handles mixed ASCII+multibyte with case letters both before and after

- handles mixed ASCII+multibyte with case letters both before and after


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles mixed ASCII+multibyte with case letters both before and after")
assert_equal(str_to_lower("A\u{e9}B\u{e8}C"), "a\u{e9}b\u{e8}c")
assert_equal(str_to_upper("a\u{e9}b\u{e8}c"), "A\u{e9}B\u{e8}C")
```

</details>

#### handles the empty string

- handles the empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles the empty string")
assert_equal(str_to_lower(""), "")
assert_equal(str_to_upper(""), "")
```

</details>

### same defect class — sibling s[i]-vs-byte-len functions in string_core.spl

#### str_trim no longer crashes on leading/trailing multibyte-adjacent whitespace

- str_trim no longer crashes on leading/trailing multibyte-adjacent whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("str_trim no longer crashes on leading/trailing multibyte-adjacent whitespace")
assert_equal(str_trim("  caf\u{e9}  "), "caf\u{e9}")
```

</details>

#### str_replace_all no longer crashes walking a multibyte subject

- str_replace_all no longer crashes walking a multibyte subject


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("str_replace_all no longer crashes walking a multibyte subject")
assert_equal(str_replace_all("caf\u{e9} caf\u{e9}", "caf", "COFFEE"), "COFFEE\u{e9} COFFEE\u{e9}")
```

</details>

#### str_reverse no longer crashes on multibyte content

- str_reverse no longer crashes on multibyte content


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("str_reverse no longer crashes on multibyte content")
# Byte-level reversal of a multibyte codepoint does not produce a
# readable result (the codepoint's bytes get re-ordered relative to
# the rest of the string) -- that reordering is a pre-existing,
# documented limitation of this byte-oriented helper, not something
# this fix is responsible for. What the fix guarantees is: no crash,
# and byte-length is preserved.
val r = str_reverse("caf\u{e9}")
assert_equal(r.len(), 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/string_core_case_utf8_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering str_to_lower / str_to_upper — multibyte UTF-8 safety, same defect class — sibling s[i]-vs-byte-len functions in string_core.spl.
- str_to_lower / str_to_upper — multibyte UTF-8 safety
- same defect class — sibling s[i]-vs-byte-len functions in string_core.spl

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
- `REQ-BUG-STR-TO-LOWER-UPPER-UTF8`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b0ac64bf794c85ce2f794a648ba9c8f26eebf76babc0e705f88790f617a9c2d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0ac64bf794c85ce2f794a648ba9c8f26eebf76babc0e705f88790f617a9c2d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0ac64bf794c85ce2f794a648ba9c8f26eebf76babc0e705f88790f617a9c2d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/string_core_case_utf8_spec.spl
mirror: doc/06_spec/01_unit/lib/common/string_core_case_utf8_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/string_core_case_utf8_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/string_core_case_utf8_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/string_core_case_utf8_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/string_core_case_utf8_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowercases an accented word without crashing (reproduces the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_case_utf8_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uppercases an accented word without crashing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/string_core_case_utf8_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes an emoji (4-byte codepoint) through str_to_lower untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

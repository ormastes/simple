# Grep Specification

> Tests covering grep tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Grep Specification

## Scenarios

### grep tool

#### basic matching

#### matches simple substring

- matches simple substring
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches simple substring")
val result = line_matches("hello world", "world", false, false, false)
expect(result).to_equal(true)
```

</details>

#### rejects non-matching line

- rejects non-matching line
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-matching line")
val result = line_matches("hello world", "foo", false, false, false)
expect(result).to_equal(false)
```

</details>

#### case insensitive

#### matches ignoring case

- matches ignoring case
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches ignoring case")
val result = line_matches("Hello World", "hello", true, false, false)
expect(result).to_equal(true)
```

</details>

#### matches uppercase pattern against lowercase text

- matches uppercase pattern against lowercase text
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches uppercase pattern against lowercase text")
val result = line_matches("hello world", "HELLO", true, false, false)
expect(result).to_equal(true)
```

</details>

#### whole word matching

#### matches whole word

- matches whole word
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches whole word")
val result = line_matches("hello world", "hello", false, true, false)
expect(result).to_equal(true)
```

</details>

#### rejects partial word match

- rejects partial word match
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects partial word match")
val result = line_matches("helloworld", "hello", false, true, false)
expect(result).to_equal(false)
```

</details>

#### whole line matching

#### matches entire line

- matches entire line
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches entire line")
val result = line_matches("hello", "hello", false, false, true)
expect(result).to_equal(true)
```

</details>

#### rejects partial line match

- rejects partial line match
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects partial line match")
val result = line_matches("hello world", "hello", false, false, true)
expect(result).to_equal(false)
```

</details>

#### word character detection

#### detects letter as word char

- detects letter as word char
   - Expected: is_word_char("a") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects letter as word char")
expect(is_word_char("a")).to_equal(true)
```

</details>

#### detects digit as word char

- detects digit as word char
   - Expected: is_word_char("5") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects digit as word char")
expect(is_word_char("5")).to_equal(true)
```

</details>

#### detects underscore as word char

- detects underscore as word char
   - Expected: is_word_char("_") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects underscore as word char")
expect(is_word_char("_")).to_equal(true)
```

</details>

#### rejects space as non-word char

- rejects space as non-word char
   - Expected: is_word_char(" ") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects space as non-word char")
expect(is_word_char(" ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/grep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering grep tool.
- grep tool

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

- Canonical SPipe generation for source `1c5ae0dad41e6854d58673b53fbc900c4531cc223cb495bd7c4ed001379dc879`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c5ae0dad41e6854d58673b53fbc900c4531cc223cb495bd7c4ed001379dc879`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c5ae0dad41e6854d58673b53fbc900c4531cc223cb495bd7c4ed001379dc879`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/grep_spec.spl
mirror: doc/06_spec/unit/tools/grep_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/grep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/grep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/grep_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches simple substring' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/grep_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-matching line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/grep_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches ignoring case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

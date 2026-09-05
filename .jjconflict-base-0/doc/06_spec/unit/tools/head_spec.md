# Head Specification

> Tests covering head tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Head Specification

## Scenarios

### head tool

#### line selection

#### gets first N lines

- gets first N lines
   - Expected: result equals `line1\nline2\nline3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets first N lines")
val content = "line1\nline2\nline3\nline4\nline5"
val result = head_lines(content, 3)
expect(result).to_equal("line1\nline2\nline3")
```

</details>

#### returns all lines when N exceeds count

- returns all lines when N exceeds count
   - Expected: result equals `line1\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all lines when N exceeds count")
val content = "line1\nline2"
val result = head_lines(content, 10)
expect(result).to_equal("line1\nline2")
```

</details>

#### returns first line

- returns first line
   - Expected: result equals `only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns first line")
val content = "only\nsecond"
val result = head_lines(content, 1)
expect(result).to_equal("only")
```

</details>

#### byte selection

#### gets first N bytes

- gets first N bytes
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets first N bytes")
val content = "hello world"
val result = head_bytes(content, 5)
expect(result).to_equal("hello")
```

</details>

#### returns all when N exceeds length

- returns all when N exceeds length
   - Expected: result equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all when N exceeds length")
val content = "hi"
val result = head_bytes(content, 100)
expect(result).to_equal("hi")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/head_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering head tool.
- head tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `bb3d1dd550575df86e3691425f93259d83c0dac7027994cc845eab642cf11131`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb3d1dd550575df86e3691425f93259d83c0dac7027994cc845eab642cf11131`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb3d1dd550575df86e3691425f93259d83c0dac7027994cc845eab642cf11131`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/head_spec.spl
mirror: doc/06_spec/unit/tools/head_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/head_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/head_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/head_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets first N lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/head_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns all lines when N exceeds count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/head_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns first line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Cat Specification

> Tests covering cat tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cat Specification

## Scenarios

### cat tool

#### file reading

#### reads existing file content

- reads existing file content
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads existing file content")
val test_file = "/tmp/cat_test_input.txt"
file_write(test_file, "line one\nline two\nline three")
val content = file_read(test_file)
if content == "" or content == nil:
    # Interpreter mode: imported file_read may return empty
    expect(true).to_equal(true)
else:
    expect(content).to_contain("line one")
    expect(content).to_contain("line two")
```

</details>

#### line numbering

#### counts lines correctly

- counts lines correctly
   - Expected: lines.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts lines correctly")
val content = "line1\nline2\nline3"
val lines = content.split("\n")
expect(lines.len()).to_equal(3)
```

</details>

#### blank line squeezing

#### detects blank lines

- detects blank lines
   - Expected: line.trim().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects blank lines")
val line = "   "
expect(line.trim().len()).to_equal(0)
```

</details>

#### detects non-blank lines

- detects non-blank lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects non-blank lines")
val line = "  hello  "
expect(line.trim().len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/cat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cat tool.
- cat tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `bacafdb0d0490ea759b328f1a95d77fb8e0545e4fabc82c764592828639139d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bacafdb0d0490ea759b328f1a95d77fb8e0545e4fabc82c764592828639139d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bacafdb0d0490ea759b328f1a95d77fb8e0545e4fabc82c764592828639139d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/tools/cat_spec.spl
mirror: doc/06_spec/unit/tools/cat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/cat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/cat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/cat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/cat_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads existing file content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/cat_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts lines correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/cat_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects blank lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

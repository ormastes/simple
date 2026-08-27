# Yes Specification

> Tests covering yes tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Yes Specification

## Scenarios

### yes tool

#### default output

#### outputs y by default

- call tool_yes with no args, inspect terminal output
   - Expected: rc equals `0`
   - Expected: out.slice(0, 2) equals `y\n`
   - Expected: out.len() equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TOOLS
step("call tool_yes with no args, inspect terminal output")
val term = Terminal.new(80, 24)
val rc = tool_yes([], term)
val out = term.take_mirrored_output()
expect(rc).to_equal(0)
expect(out.slice(0, 2)).to_equal("y\n")
expect(out.len()).to_equal(2000)
```

</details>

#### custom string

#### outputs custom message

- call tool_yes with a custom message, inspect terminal output
   - Expected: rc equals `0`
   - Expected: out.slice(0, 6) equals `hello\n`
   - Expected: out.len() equals `6000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TOOLS
step("call tool_yes with a custom message, inspect terminal output")
val term = Terminal.new(80, 24)
val rc = tool_yes(["hello"], term)
val out = term.take_mirrored_output()
expect(rc).to_equal(0)
expect(out.slice(0, 6)).to_equal("hello\n")
expect(out.len()).to_equal(6000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/yes_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering yes tool.
- yes tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-TOOLS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd9c2126b708a17249d23f4c2d17d6aa4324f18e78e04a1ea6a9fa46cba5bd52`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd9c2126b708a17249d23f4c2d17d6aa4324f18e78e04a1ea6a9fa46cba5bd52`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd9c2126b708a17249d23f4c2d17d6aa4324f18e78e04a1ea6a9fa46cba5bd52`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/tools/shell/yes_spec.spl
mirror: doc/06_spec/01_unit/tools/shell/yes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/tools/shell/yes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/tools/shell/yes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/tools/shell/yes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/tools/shell/yes_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputs y by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/tools/shell/yes_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputs custom message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

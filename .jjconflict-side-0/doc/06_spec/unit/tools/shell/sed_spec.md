# Sed Specification

> Tests covering sed tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sed Specification

## Scenarios

### sed tool

#### substitution

#### replaces first occurrence

- replaces first occurrence
   - Expected: result equals `goodbye world hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces first occurrence")
val line = "hello world hello"
val idx = line.find("hello")
val before = line.slice(0, idx)
val after = line.slice(idx + 5, line.len())
val result = "{before}goodbye{after}"
expect(result).to_equal("goodbye world hello")
```

</details>

#### replaces all occurrences with g flag

- replaces all occurrences with g flag
   - Expected: result equals `xxx bbb xxx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces all occurrences with g flag")
val line = "aaa bbb aaa"
val result = line.replace("aaa", "xxx")
expect(result).to_equal("xxx bbb xxx")
```

</details>

#### deletion

#### deletes lines matching pattern

- deletes lines matching pattern
   - Expected: result.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes lines matching pattern")
val lines = ["keep", "remove this", "keep"]
var result: [text] = []
for line in lines:
    if not line.contains("remove"):
        result = result.push(line)
expect(result.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/sed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sed tool.
- sed tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `be2ca4de57d58459a3d3de32102743c40d92d205e576d806aaebca56ea38ec71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be2ca4de57d58459a3d3de32102743c40d92d205e576d806aaebca56ea38ec71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be2ca4de57d58459a3d3de32102743c40d92d205e576d806aaebca56ea38ec71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/tools/shell/sed_spec.spl
mirror: doc/06_spec/unit/tools/shell/sed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/sed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/sed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/sed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/shell/sed_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces first occurrence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/sed_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces all occurrences with g flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/sed_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'deletes lines matching pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

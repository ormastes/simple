# Basename Specification

> Tests covering basename tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basename Specification

## Scenarios

### basename tool

#### path stripping

#### strips directory from path

- strips directory from path
   - Expected: name equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips directory from path")
val path = "/usr/local/bin/simple"
# basename should return "simple"
var last_slash = -1
var i = 0
for ch in path:
    if ch == "/":
        last_slash = i
    i = i + 1
val name = path.slice(last_slash + 1, path.len())
expect(name).to_equal("simple")
```

</details>

#### handles root path

- handles root path
   - Expected: path equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles root path")
val path = "/"
expect(path).to_equal("/")
```

</details>

#### handles no directory

- handles no directory
   - Expected: name equals `file.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles no directory")
val path = "file.txt"
var last_slash = -1
var i = 0
for ch in path:
    if ch == "/":
        last_slash = i
    i = i + 1
val name = if last_slash >= 0: path.slice(last_slash + 1, path.len()) else: path
expect(name).to_equal("file.txt")
```

</details>

#### suffix stripping

#### strips suffix from filename

- strips suffix from filename
   - Expected: result equals `file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips suffix from filename")
val name = "file.spl"
val suffix = ".spl"
val result = name.slice(0, name.len() - suffix.len())
expect(result).to_equal("file")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/basename_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering basename tool.
- basename tool

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

- Canonical SPipe generation for source `1e9434cb056b7a2a3b78f4341b5a147ada01023e05b67856addb579e2cf0ed9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e9434cb056b7a2a3b78f4341b5a147ada01023e05b67856addb579e2cf0ed9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e9434cb056b7a2a3b78f4341b5a147ada01023e05b67856addb579e2cf0ed9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/tools/shell/basename_spec.spl
mirror: doc/06_spec/unit/tools/shell/basename_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/basename_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/basename_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/basename_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips directory from path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/basename_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles root path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/basename_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles no directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

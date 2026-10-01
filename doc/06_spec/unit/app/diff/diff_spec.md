# Diff Specification

> Tests covering Line Diff, Diff Output Format, Diff Hunk, AST Diff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diff Specification

## Scenarios

### Line Diff

#### identical files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identical files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identical files")
val changes = 0
check(changes == 0)
```

</details>

#### single line addition

- single line addition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single line addition")
val additions = 1
check(additions == 1)
```

</details>

#### single line deletion

- single line deletion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single line deletion")
val deletions = 1
check(deletions == 1)
```

</details>

#### single line modification

- single line modification


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single line modification")
val modifications = 1
check(modifications == 1)
```

</details>

#### multiple changes

- multiple changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple changes")
val additions = 3
val deletions = 2
val total = additions + deletions
check(total == 5)
```

</details>

### Diff Output Format

#### unified diff format

- unified diff format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unified diff format")
val format = "unified"
check(format == "unified")
```

</details>

#### context diff format

- context diff format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("context diff format")
val format = "context"
check(format == "context")
```

</details>

#### side-by-side format

- side-by-side format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("side-by-side format")
val format = "side-by-side"
check(format == "side-by-side")
```

</details>

#### stat format

- stat format


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stat format")
val format = "stat"
check(format == "stat")
```

</details>

### Diff Hunk

#### hunk has start line

- hunk has start line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hunk has start line")
val start = 10
check(start > 0)
```

</details>

#### hunk has line count

- hunk has line count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hunk has line count")
val count = 5
check(count > 0)
```

</details>

#### hunk has context lines

- hunk has context lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hunk has context lines")
val context = 3
check(context >= 0)
```

</details>

#### adjacent hunks merged

- adjacent hunks merged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adjacent hunks merged")
val merged = true
check(merged)
```

</details>

### AST Diff

#### function added

- function added


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function added")
val change = "add_function"
check(change == "add_function")
```

</details>

#### function removed

- function removed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function removed")
val change = "remove_function"
check(change == "remove_function")
```

</details>

#### function signature changed

- function signature changed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function signature changed")
val change = "change_signature"
check(change == "change_signature")
```

</details>

#### function body changed

- function body changed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function body changed")
val change = "change_body"
check(change == "change_body")
```

</details>

#### class field added

- class field added


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("class field added")
val change = "add_field"
check(change == "add_field")
```

</details>

#### import added

- import added


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("import added")
val change = "add_import"
check(change == "add_import")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/diff/diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Line Diff, Diff Output Format, Diff Hunk, AST Diff.
- Line Diff
- Diff Output Format
- Diff Hunk
- AST Diff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `2efa5b74c7ee3f934834516d1945993d3d0fd8ee899b200aeefa0f0f0586d343`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2efa5b74c7ee3f934834516d1945993d3d0fd8ee899b200aeefa0f0f0586d343`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2efa5b74c7ee3f934834516d1945993d3d0fd8ee899b200aeefa0f0f0586d343`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/diff/diff_spec.spl
mirror: doc/06_spec/unit/app/diff/diff_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/diff/diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/diff/diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/diff/diff_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/diff/diff_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single line addition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/diff/diff_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single line deletion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

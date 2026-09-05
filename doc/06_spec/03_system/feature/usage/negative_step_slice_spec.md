# Negative Slice Step Is Not Supported

> Negative slice **step** (Python-style `s[::-1]`, `s[9:0:-1]`) is deliberately **not** part of the language. Reversal is always the explicit `.reversed()` method call, never an index trick -- this repo follows Ruby's model, not Python's. Negative slice **indices** (Ruby-style, count from the end, e.g. `s[-3:]`, `s[0:-1]`) remain a completely different, fully-supported feature and are unaffected by this decision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Negative Slice Step Is Not Supported

Negative slice **step** (Python-style `s[::-1]`, `s[9:0:-1]`) is deliberately **not** part of the language. Reversal is always the explicit `.reversed()` method call, never an index trick -- this repo follows Ruby's model, not Python's. Negative slice **indices** (Ruby-style, count from the end, e.g. `s[-3:]`, `s[0:-1]`) remain a completely different, fully-supported feature and are unaffected by this decision.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RANGE-STEP-NEGATIVE-ERROR |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/negative_step_slice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Negative slice **step** (Python-style `s[::-1]`, `s[9:0:-1]`) is
deliberately **not** part of the language. Reversal is always the explicit
`.reversed()` method call, never an index trick -- this repo follows
Ruby's model, not Python's. Negative slice **indices** (Ruby-style, count
from the end, e.g. `s[-3:]`, `s[0:-1]`) remain a completely different,
fully-supported feature and are unaffected by this decision.

## Design

**ADR:** doc/04_architecture/language/slicing/+adr/negative_step_not_supported_2026-07-30.md

## Syntax

```simple
s[9:0:-1]   # errors: use .reversed()
s[::-1]     # errors: use .reversed()
s.reversed() # correct way to reverse
s[-3:]      # still legal -- negative INDEX, not step
```

## Traceability Expectations

- Every negative-step slice form (bare `[::-1]`, bounded `[9:0:-1]`,
  step -1 and other negative steps, negative step combined with negative
  indices) must produce a real, non-zero-exit, diagnosable error naming
  `.reversed()` under BOTH the default (JIT/native) engine and the
  interpreter -- a divergence where one engine errors and the other
  silently returns something is treated as a bug, not an acceptable gap.
- Negative-index-only slices (no step, or step omitted) must keep working
  identically to before this change under both engines.

## Scenarios

### Negative slice step is a hard error in both engines

#### errors on bare negative step s[::-1]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- errors on bare negative step s[::-1]


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("errors on bare negative step s[::-1]")
expect_negative_step_error("bare_reverse.spl")
```

</details>

#### errors on bounded negative step s[9:0:-1]

- errors on bounded negative step s[9:0:-1]


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("errors on bounded negative step s[9:0:-1]")
expect_negative_step_error("bounded_reverse.spl")
```

</details>

#### errors on step -1 via s[::-1] on a string

- errors on step -1 via s[::-1] on a string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("errors on step -1 via s[::-1] on a string")
expect_negative_step_error("string_bare_reverse.spl")
```

</details>

#### errors on step other than -1 (e.g. s[::-2])

- errors on step other than -1 (e.g. s[::-2])


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("errors on step other than -1 (e.g. s[::-2])")
expect_negative_step_error("step_negative_two.spl")
```

</details>

#### errors when negative step is combined with negative indices

- errors when negative step is combined with negative indices


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("errors when negative step is combined with negative indices")
# The most confusable case: negative INDICES remain legal
# (`s[-1:-5:...]` alone would be fine), but the STEP of -1 here
# must still be rejected.
expect_negative_step_error("negative_index_and_negative_step.spl")
```

</details>

#### keeps negative-index-only slices (no negative step) working

- keeps negative-index-only slices (no negative step) working


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps negative-index-only slices (no negative step) working")
expect_no_error("negative_index_only.spl", "OK:789:012345678:World")
```

</details>

### Negative index specs still pass unmodified (regression guard)

#### runs the existing negative-index coverage end to end

- runs the existing negative-index coverage end to end
- Confirm advanced_indexing_spec.spl's negative-index cases were not touched by this change
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the existing negative-index coverage end to end")
step("Confirm advanced_indexing_spec.spl's negative-index cases were not touched by this change")
val (source, _stderr, code) = process_run("/bin/sh", ["-c", "cat test/03_system/feature/usage/advanced_indexing_spec.spl"])
expect(code).to_equal(0)
expect(source).to_contain("arr[-3:]")
expect(source).to_contain("arr[:-2]")
expect(source).to_contain("arr[-4:-1]")
expect(source).to_contain("s[-5:-1]")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a164e2f502f1a4c7b36f8f054fc33320f6e8046f914c8e5b1f842119afa5770`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a164e2f502f1a4c7b36f8f054fc33320f6e8046f914c8e5b1f842119afa5770`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a164e2f502f1a4c7b36f8f054fc33320f6e8046f914c8e5b1f842119afa5770`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/usage/negative_step_slice_spec.spl
mirror: doc/06_spec/03_system/feature/usage/negative_step_slice_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/negative_step_slice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/negative_step_slice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/negative_step_slice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/negative_step_slice_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors on bare negative step s[::-1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/negative_step_slice_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors on bounded negative step s[9:0:-1]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/negative_step_slice_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'errors on step -1 via s[::-1] on a string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

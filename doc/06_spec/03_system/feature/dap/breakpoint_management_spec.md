# DAP Breakpoint Management

> Tests the Debug Adapter Protocol breakpoint management including setting, removing, and hit-count breakpoints. Verifies that breakpoints are correctly tracked across source locations and that conditional breakpoints evaluate their expressions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Breakpoint Management

Tests the Debug Adapter Protocol breakpoint management including setting, removing, and hit-count breakpoints. Verifies that breakpoints are correctly tracked across source locations and that conditional breakpoints evaluate their expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/breakpoint_management_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol breakpoint management including setting, removing,
and hit-count breakpoints. Verifies that breakpoints are correctly tracked across
source locations and that conditional breakpoints evaluate their expressions.

## Scenarios

### Breakpoint Management

### Adding breakpoints

#### adds a single breakpoint

- adds a single breakpoint
   - Expected: has_bp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds a single breakpoint")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)

val has_bp = debug_has_breakpoint("test.spl", 10)
expect(has_bp).to_equal(true)
```

</details>

#### adds multiple breakpoints in same file

- adds multiple breakpoints in same file
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 20) is true
   - Expected: debug_has_breakpoint("test.spl", 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds multiple breakpoints in same file")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 20, 2)
debug_add_breakpoint("test.spl", 30, 3)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 20)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 30)).to_equal(true)
```

</details>

#### adds breakpoints in different files

- adds breakpoints in different files
   - Expected: debug_has_breakpoint("file1.spl", 10) is true
   - Expected: debug_has_breakpoint("file2.spl", 15) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds breakpoints in different files")
debug_set_active(true)
debug_add_breakpoint("file1.spl", 10, 1)
debug_add_breakpoint("file2.spl", 15, 2)

expect(debug_has_breakpoint("file1.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("file2.spl", 15)).to_equal(true)
```

</details>

#### allows duplicate breakpoints with different IDs

- allows duplicate breakpoints with different IDs
   - Expected: has_bp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows duplicate breakpoints with different IDs")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 10, 2)  # Same location, different ID

val has_bp = debug_has_breakpoint("test.spl", 10)
expect(has_bp).to_equal(true)
```

</details>

### Removing breakpoints

#### removes a breakpoint

- removes a breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes a breakpoint")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)

debug_remove_breakpoint("test.spl", 10)
expect(debug_has_breakpoint("test.spl", 10)).to_equal(false)
```

</details>

#### removes specific breakpoint from multiple

- removes specific breakpoint from multiple
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 20) is false
   - Expected: debug_has_breakpoint("test.spl", 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes specific breakpoint from multiple")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 20, 2)
debug_add_breakpoint("test.spl", 30, 3)

debug_remove_breakpoint("test.spl", 20)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 20)).to_equal(false)
expect(debug_has_breakpoint("test.spl", 30)).to_equal(true)
```

</details>

#### handles removing non-existent breakpoint

- handles removing non-existent breakpoint
   - Expected: debug_has_breakpoint("test.spl", 999) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles removing non-existent breakpoint")
debug_set_active(true)
# Should not crash
debug_remove_breakpoint("test.spl", 999)
expect(debug_has_breakpoint("test.spl", 999)).to_equal(false)
```

</details>

### Checking breakpoint existence

#### returns false for non-existent breakpoint

- returns false for non-existent breakpoint
   - Expected: has_bp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for non-existent breakpoint")
debug_set_active(true)
val has_bp = debug_has_breakpoint("nonexistent.spl", 100)
expect(has_bp).to_equal(false)
```

</details>

#### checks breakpoint in correct file only

- checks breakpoint in correct file only
   - Expected: debug_has_breakpoint("file1.spl", 10) is true
   - Expected: debug_has_breakpoint("file2.spl", 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks breakpoint in correct file only")
debug_set_active(true)
debug_add_breakpoint("file1.spl", 10, 1)

expect(debug_has_breakpoint("file1.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("file2.spl", 10)).to_equal(false)
```

</details>

#### checks breakpoint at correct line only

- checks breakpoint at correct line only
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 9) is false
   - Expected: debug_has_breakpoint("test.spl", 11) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks breakpoint at correct line only")
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 9)).to_equal(false)
expect(debug_has_breakpoint("test.spl", 11)).to_equal(false)
```

</details>

### Breakpoint hit detection

#### should break when at breakpoint location

- should break when at breakpoint location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should break when at breakpoint location")
debug_set_active(true)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 42, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### should not break when not at breakpoint

- should not break when not at breakpoint
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not break when not at breakpoint")
debug_set_active(true)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 43, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

#### should not break when debug inactive

- should not break when debug inactive
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not break when debug inactive")
debug_set_active(false)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 42, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

### Edge cases

#### handles line number 0

- handles line number 0
   - Expected: debug_has_breakpoint("test.spl", 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles line number 0")
debug_set_active(true)
debug_add_breakpoint("test.spl", 0, 1)
expect(debug_has_breakpoint("test.spl", 0)).to_equal(true)
```

</details>

#### handles large line numbers

- handles large line numbers
   - Expected: debug_has_breakpoint("test.spl", 999999) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles large line numbers")
debug_set_active(true)
debug_add_breakpoint("test.spl", 999999, 1)
expect(debug_has_breakpoint("test.spl", 999999)).to_equal(true)
```

</details>

#### handles empty file path

- handles empty file path
   - Expected: debug_has_breakpoint("", 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty file path")
debug_set_active(true)
debug_add_breakpoint("", 10, 1)
expect(debug_has_breakpoint("", 10)).to_equal(true)
```

</details>

#### handles special characters in file path

- handles special characters in file path
   - Expected: debug_has_breakpoint("path/to/my-file_v2.spl", 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles special characters in file path")
debug_set_active(true)
debug_add_breakpoint("path/to/my-file_v2.spl", 10, 1)
expect(debug_has_breakpoint("path/to/my-file_v2.spl", 10)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `c290e67d8816bf832adbf720802259a883dad5786df023b9bdbbed5fab756b5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c290e67d8816bf832adbf720802259a883dad5786df023b9bdbbed5fab756b5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c290e67d8816bf832adbf720802259a883dad5786df023b9bdbbed5fab756b5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/dap/breakpoint_management_spec.spl
mirror: doc/06_spec/03_system/feature/dap/breakpoint_management_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/dap/breakpoint_management_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/dap/breakpoint_management_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/dap/breakpoint_management_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds a single breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/breakpoint_management_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds multiple breakpoints in same file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/breakpoint_management_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds breakpoints in different files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/breakpoint_management_spec.spl:193:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should break when at breakpoint location' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/dap/breakpoint_management_spec.spl:203:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not break when not at breakpoint' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/dap/breakpoint_management_spec.spl:213:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not break when debug inactive' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

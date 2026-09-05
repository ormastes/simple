# Global Array Push Visible To Len Specification

> Tests covering module-global array mutation is visible to later reads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Global Array Push Visible To Len Specification

## Scenarios

### module-global array mutation is visible to later reads

<details>
<summary>Advanced: push in a while body terminates the loop that reads len in its condition</summary>

#### push in a while body terminates the loop that reads len in its condition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- push in a while body terminates the loop that reads len in its condition
- Fill a module-global array by pushing until its len() reaches 3
- The loop terminated and the global holds exactly 3 elements
   - Expected: pushed_len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("push in a while body terminates the loop that reads len in its condition")
step("Fill a module-global array by pushing until its len() reaches 3")
reset_pushed()
fill_by_push(3)

step("The loop terminated and the global holds exactly 3 elements")
expect(pushed_len()).to_equal(3)
```

</details>


</details>

#### an already-full global is left alone (the condition is false on entry)

- an already-full global is left alone (the condition is false on entry)
- Refill to 4, then ask for only 2 more
- No further pushes happened; the length stays 4
   - Expected: pushed_len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("an already-full global is left alone (the condition is false on entry)")
step("Refill to 4, then ask for only 2 more")
reset_pushed()
fill_by_push(4)
fill_by_push(2)

step("No further pushes happened; the length stays 4")
expect(pushed_len()).to_equal(4)
```

</details>

#### whole-array assignment to a global still propagates

- whole-array assignment to a global still propagates
- Build the values in a local vec and assign the global once
- The global reports the assigned length
   - Expected: assigned_len() equals `5`
- And the assigned contents are intact
   - Expected: assigned_at(0) equals `0`
   - Expected: assigned_at(4) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("whole-array assignment to a global still propagates")
step("Build the values in a local vec and assign the global once")
fill_by_whole_assign(5)

step("The global reports the assigned length")
expect(assigned_len()).to_equal(5)

step("And the assigned contents are intact")
expect(assigned_at(0)).to_equal(0)
expect(assigned_at(4)).to_equal(4)
```

</details>

#### indexed store into a global still propagates

- indexed store into a global still propagates
- Assign a 5-element global, then overwrite one slot in place
- The indexed write is visible and nothing else moved
   - Expected: assigned_at(2) equals `99`
   - Expected: assigned_at(3) equals `3`
   - Expected: assigned_len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("indexed store into a global still propagates")
step("Assign a 5-element global, then overwrite one slot in place")
fill_by_whole_assign(5)
store_at(2, 99)

step("The indexed write is visible and nothing else moved")
expect(assigned_at(2)).to_equal(99)
expect(assigned_at(3)).to_equal(3)
expect(assigned_len()).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module-global array mutation is visible to later reads.
- module-global array mutation is visible to later reads

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `375570b11ada5b1fdcf6414056ca7f21968a0e4632a31599e2b125e3a3fbbc1a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `375570b11ada5b1fdcf6414056ca7f21968a0e4632a31599e2b125e3a3fbbc1a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `375570b11ada5b1fdcf6414056ca7f21968a0e4632a31599e2b125e3a3fbbc1a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'push in a while body terminates the loop that reads len in its condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an already-full global is left alone (the condition is false on entry)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/global_array_push_visible_to_len_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'whole-array assignment to a global still propagates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

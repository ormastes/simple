# Game2d Input Facade Specification

> Tests covering gc_async_mut game2d input facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Input Facade Specification

## Scenarios

### gc_async_mut game2d input facade

#### re-exports key constructors, snapshots, and current input accessors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports key constructors, snapshots, and current input accessors
   - Expected: jump.code equals `32`
   - Expected: left.code equals `1`
   - Expected: right.code equals `3`
   - Expected: empty.key_down(jump) is false
   - Expected: snap.key_down(jump) is true
   - Expected: snap.key_pressed_this_frame(jump) is true
   - Expected: snap.mouse_down(left) is true
   - Expected: snap.mouse_position().x equals `12.0`
   - Expected: current().key_down(jump) is true
   - Expected: key_down(jump) is true
   - Expected: key_pressed_this_frame(jump) is true
   - Expected: mouse_down(left) is true
   - Expected: mouse_pos().y equals `24.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports key constructors, snapshots, and current input accessors")
val jump = Key(32)
val left = mouse_left()
val right = mouse_right()
expect(jump.code).to_equal(32)
expect(left.code).to_equal(1)
expect(right.code).to_equal(3)

val empty = InputSnapshot.create()
expect(empty.key_down(jump)).to_equal(false)

val snap = freeze_from([jump], [jump], Vec2(x: 12.0, y: 24.0), [left])
expect(snap.key_down(jump)).to_equal(true)
expect(snap.key_pressed_this_frame(jump)).to_equal(true)
expect(snap.mouse_down(left)).to_equal(true)
expect(snap.mouse_position().x).to_equal(12.0)

set_current(snap)
expect(current().key_down(jump)).to_equal(true)
expect(key_down(jump)).to_equal(true)
expect(key_pressed_this_frame(jump)).to_equal(true)
expect(mouse_down(left)).to_equal(true)
expect(mouse_pos().y).to_equal(24.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut game2d input facade.
- gc_async_mut game2d input facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `95e61250f265c582f3bc8a273fbba7bb6aca549157ff55dfdf57fa5caf1589c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95e61250f265c582f3bc8a273fbba7bb6aca549157ff55dfdf57fa5caf1589c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95e61250f265c582f3bc8a273fbba7bb6aca549157ff55dfdf57fa5caf1589c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/game2d/input/game2d_input_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports key constructors, snapshots, and current input accessors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

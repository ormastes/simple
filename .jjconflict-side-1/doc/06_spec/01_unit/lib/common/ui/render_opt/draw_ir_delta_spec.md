# Draw Ir Delta Specification

> Tests covering O5 DrawIR delta: only affected components rebuilt, replay matches full rebuild.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Delta Specification

## Scenarios

### O5 DrawIR delta: only affected components rebuilt, replay matches full rebuild

#### 1 of 4 components dirty: delta has exactly 1 command, replay == full rebuild

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- 1 of 4 components dirty: delta has exactly 1 command, replay == full rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1 of 4 components dirty: delta has exactly 1 command, replay == full rebuild")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)

# Frame 1 (bootstrap): every node starts dirty, so the delta
# legitimately covers all 4. Consume it as the baseline "prev frame",
# then clear dirty flags the way a real frame boundary would.
mark_all_dirty(revs, 4)
val delta1 = draw_ir_delta_build(chunks, rects, revs, ids)
assert_true(delta1.built_count == 4)
var prev: [DrawIrCommand] = []
var i0: i64 = 0
while i0 < 4:
    prev.push(draw_ir_rect("", 0, 0, 0, 0, 0u32))
    i0 = i0 + 1
prev = draw_ir_delta_replay(prev, delta1)
assert_true(lists_equal(prev, full_rebuild(rects, ids)))
revs.clear_dirty()

# Frame 2: mark ONLY component 2's PAINT revision.
assert_true(revs.mark(2, REV_PAINT) == 0)
val delta2 = draw_ir_delta_build(chunks, rects, revs, ids)

# PROPORTIONALITY: exactly 1 of 4 rebuilt, not all 4.
assert_true(delta2.built_count == 1)
assert_true(delta2.reused_count == 3)
assert_true(delta2.total_count == 4)
assert_true(delta2.changed_indices[0] == 2)
assert_true(delta2.changed_commands[0].component_id == "comp2")

# CORRECTNESS: replay(prev, delta2) must equal a fresh full rebuild
# of the (unchanged) scene, field-for-field, even though only 1 of 4
# commands was actually reconstructed this frame.
val replayed = draw_ir_delta_replay(prev, delta2)
val fresh = full_rebuild(rects, ids)
assert_true(lists_equal(replayed, fresh))
# And the untouched 3 commands in `replayed` are the SAME values as
# in `prev` -- proving they were reused, not rebuilt.
assert_true(commands_equal(replayed[0], prev[0]))
assert_true(commands_equal(replayed[1], prev[1]))
assert_true(commands_equal(replayed[3], prev[3]))
```

</details>

#### identical frames (fresh revs, nothing ever marked) produce an empty delta with no bootstrap step

- identical frames (fresh revs, nothing ever marked) produce an empty delta with no bootstrap step


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identical frames (fresh revs, nothing ever marked) produce an empty delta with no bootstrap step")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)
# No mark_all_dirty, no clear_dirty -- a genuinely brand-new
# RenderRevisions where nothing has EVER been marked is the
# "identical frames" case: there is no diff to report.
val delta = draw_ir_delta_build(chunks, rects, revs, ids)
assert_true(delta.built_count == 0)
assert_true(delta.changed_indices.len() == 0)
assert_true(delta.changed_commands.len() == 0)
assert_true(delta.reused_count == 4)
assert_true(delta.total_count == 4)
```

</details>

#### 0 of 4 components dirty after clear_dirty: delta is empty, replay == prev unchanged

- 0 of 4 components dirty after clear_dirty: delta is empty, replay == prev unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0 of 4 components dirty after clear_dirty: delta is empty, replay == prev unchanged")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)
mark_all_dirty(revs, 4)
val delta1 = draw_ir_delta_build(chunks, rects, revs, ids)
var prev: [DrawIrCommand] = []
var i0: i64 = 0
while i0 < 4:
    prev.push(draw_ir_rect("", 0, 0, 0, 0, 0u32))
    i0 = i0 + 1
prev = draw_ir_delta_replay(prev, delta1)
revs.clear_dirty()

val delta2 = draw_ir_delta_build(chunks, rects, revs, ids)
assert_true(delta2.built_count == 0)
assert_true(delta2.reused_count == 4)
val replayed = draw_ir_delta_replay(prev, delta2)
assert_true(lists_equal(replayed, prev))
assert_true(lists_equal(replayed, full_rebuild(rects, ids)))
```

</details>

#### prev is not mutated by replay (Simple arrays are value types)

- prev is not mutated by replay (Simple arrays are value types)


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prev is not mutated by replay (Simple arrays are value types)")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)
mark_all_dirty(revs, 4)
val delta1 = draw_ir_delta_build(chunks, rects, revs, ids)
var prev: [DrawIrCommand] = []
var i0: i64 = 0
while i0 < 4:
    prev.push(draw_ir_rect("", 0, 0, 0, 0, 0u32))
    i0 = i0 + 1
prev = draw_ir_delta_replay(prev, delta1)
val prev_before = prev[0].component_id
revs.clear_dirty()

assert_true(revs.mark(0, REV_PAINT) == 0)
val delta2 = draw_ir_delta_build(chunks, rects, revs, ids)
val _replayed = draw_ir_delta_replay(prev, delta2)
assert_true(prev[0].component_id == prev_before)
```

</details>

#### SABOTAGE (proportionality): an unconditional full rebuild every frame breaks the exact-count invariant the real path guarantees

- SABOTAGE (proportionality): an unconditional full rebuild every frame breaks the exact-count invariant the real path guarantees


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE (proportionality): an unconditional full rebuild every frame breaks the exact-count invariant the real path guarantees")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)
mark_all_dirty(revs, 4)
val delta1 = draw_ir_delta_build(chunks, rects, revs, ids)
var prev: [DrawIrCommand] = []
var i0: i64 = 0
while i0 < 4:
    prev.push(draw_ir_rect("", 0, 0, 0, 0, 0u32))
    i0 = i0 + 1
prev = draw_ir_delta_replay(prev, delta1)
revs.clear_dirty()

assert_true(revs.mark(2, REV_PAINT) == 0)
# Sabotage: bypass selection entirely and rebuild ALL 4, exactly what
# a broken/no-skip delta generator would do regardless of marks.
val sabotaged = full_rebuild(rects, ids)
# The real path's invariant (exactly 1 rebuilt) does NOT hold for the
# sabotaged unconditional rebuild -- assert the failure explicitly.
assert_true(sabotaged.len() != 1)
assert_true(sabotaged.len() == 4)

# The real (non-sabotaged) path is unaffected and still selective.
val real_delta = draw_ir_delta_build(chunks, rects, revs, ids)
assert_true(real_delta.built_count == 1)
```

</details>

#### SABOTAGE (correctness): building the delta from stale geometry produces a replay that diverges from a full rebuild

- SABOTAGE (correctness): building the delta from stale geometry produces a replay that diverges from a full rebuild


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE (correctness): building the delta from stale geometry produces a replay that diverges from a full rebuild")
val chunks = make_chunks()
val rects = make_rects()
val ids = make_ids()
val revs = RenderRevisions.create(4)
mark_all_dirty(revs, 4)
val delta1 = draw_ir_delta_build(chunks, rects, revs, ids)
var prev: [DrawIrCommand] = []
var i0: i64 = 0
while i0 < 4:
    prev.push(draw_ir_rect("", 0, 0, 0, 0, 0u32))
    i0 = i0 + 1
prev = draw_ir_delta_replay(prev, delta1)
revs.clear_dirty()

# Mutate the geometry source a real caller would rebuild from:
# component 2 grows from 10x10 to 20x20, and is marked dirty.
val grown_rects = PaintChunkRects.create()
grown_rects.add_rect(0, 0, 10, 10, 0xFFFF0000)
grown_rects.add_rect(10, 0, 10, 10, 0xFF00FF00)
grown_rects.add_rect(20, 0, 20, 20, 0xFF0000FF)
grown_rects.add_rect(30, 0, 10, 10, 0xFFFFFF00)
assert_true(revs.mark(2, REV_PAINT) == 0)

# Sabotage: build the delta against the OLD (stale) rects, as if the
# generator forgot to consult fresh geometry for the dirty component
# -- "marked dirty but rebuilt from stale data" is a real bug class.
val stale_delta = draw_ir_delta_build(chunks, rects, revs, ids)
val stale_replay = draw_ir_delta_replay(prev, stale_delta)
val correct_fresh = full_rebuild(grown_rects, ids)
# Diverges from the real fresh rebuild: proves this spec's oracle
# actually distinguishes correct from incorrect deltas.
assert_true(not lists_equal(stale_replay, correct_fresh))
assert_true(stale_replay[2].width == 10)
assert_true(correct_fresh[2].width == 20)

# The real path, given the fresh geometry, matches.
val real_delta = draw_ir_delta_build(chunks, grown_rects, revs, ids)
val real_replay = draw_ir_delta_replay(prev, real_delta)
assert_true(lists_equal(real_replay, correct_fresh))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering O5 DrawIR delta: only affected components rebuilt, replay matches full rebuild.
- O5 DrawIR delta: only affected components rebuilt, replay matches full rebuild

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `228be1bb5be0c7d173f0664e33a867face511259332db679d7aa0886f7bb32cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `228be1bb5be0c7d173f0664e33a867face511259332db679d7aa0886f7bb32cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `228be1bb5be0c7d173f0664e33a867face511259332db679d7aa0886f7bb32cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '1 of 4 components dirty: delta has exactly 1 command, replay == full rebuild' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical frames (fresh revs, nothing ever marked) produce an empty delta with no bootstrap step' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/draw_ir_delta_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0 of 4 components dirty after clear_dirty: delta is empty, replay == prev unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Damage Tiles Specification

> Tests covering O2 multiscale damage tiles, SABOTAGE: O2 damage gates reject force-full and dropped-tile behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Damage Tiles Specification

## Scenarios

### O2 multiscale damage tiles

#### REQ-003 REQ-005 builds exact 8K grids including ragged bottom edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
expect(d.level_count).to_equal(3)
expect(d.cols[0]).to_equal(30u32)
expect(d.rows[0]).to_equal(17u32)
expect(d.level_capacity[0]).to_equal(510u32)
assert_true(d.cols[1] == 120)
assert_true(d.rows[1] == 68)
assert_true(d.level_capacity[1] == 8160)
assert_true(d.cols[2] == 240)
assert_true(d.rows[2] == 135)
```

</details>

#### REQ-001 REQ-003 REQ-005 marks one bottom-right pixel at every configured scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(7679, 4319, 1, 1)
assert_true(d.dirty_count(0) == 1)
assert_true(d.dirty_count(1) == 1)
assert_true(d.dirty_count(2) == 1)
assert_true(d.is_dirty(0, 29, 16))
assert_true(d.is_dirty(1, 119, 67))
assert_true(d.is_dirty(2, 239, 134))
# Ragged 8K bottom row: 256x224 and 64x32, not padded beyond 4320.
assert_true(d.dirty_pixels(0) == 57344)
assert_true(d.dirty_pixels(1) == 2048)
assert_true(d.dirty_pixels(2) == 1024)
assert_true(d.damage_class(1, 60) == DAMAGE_LOCAL)
```

</details>

#### REQ-002 deduplicates overlapping damage within a frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(10, 10, 20, 20)
d.mark_rect(12, 12, 4, 4)
assert_true(d.dirty_count(0) == 1)
assert_true(d.dirty_count(1) == 1)
assert_true(d.dirty_count(2) == 1)
```

</details>

#### REQ-004 marks old and new transform bounds without forcing full damage

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(64, 64, 64, 64)
d.mark_rect(640, 64, 64, 64)
assert_true(d.dirty_count(1) == 2)
assert_true(d.dirty_pixels(1) == 8192)
assert_true(d.damage_class(1, 60) == DAMAGE_LOCAL)
```

</details>

#### REQ-004 REQ-006 bridges PropertyTrees old and new transform damage

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trees = PropertyTrees.create()
val node = trees.add_node(PT_TRANSFORM, -1, 64, 64, 64, 64)
expect(trees.set_translate(node, 640, 64)).to_equal(PT_OK)
val d = make_8k_damage()
expect(damage_tiles_mark_property_damage(d, trees)).to_equal(2)
expect(d.dirty_count(1)).to_equal(2)
assert_true(d.is_dirty(1, 1, 1))
assert_true(d.is_dirty(1, 10, 1))
# The bridge does not steal frame ownership from PropertyTrees.
expect(trees.damage_len).to_equal(2)
```

</details>

#### REQ-005 REQ-007 emits exact clipped rectangles for CPU and Vulkan planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(7679, 4319, 1, 1)
val coarse = d.dirty_rects(0)
expect(coarse.len()).to_equal(4)
expect(coarse[0]).to_equal(7424)
expect(coarse[1]).to_equal(4096)
expect(coarse[2]).to_equal(256)
expect(coarse[3]).to_equal(224)
val cpu = d.dirty_rects(1)
expect(cpu[0]).to_equal(7616)
expect(cpu[1]).to_equal(4288)
expect(cpu[2]).to_equal(64)
expect(cpu[3]).to_equal(32)
```

</details>

#### clamps negative and outside rects before tile math

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(-10, -10, 20, 20)
d.mark_rect(9000, 5000, 20, 20)
d.mark_rect(1, 1, 0, 10)
assert_true(d.dirty_count(1) == 1)
assert_true(d.is_dirty(1, 0, 0))
```

</details>

#### starts the next frame without scanning or retaining old dirty tiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(0, 0, 64, 64)
assert_true(d.damage_class(1, 60) == DAMAGE_LOCAL)
d.begin_frame()
assert_true(d.dirty_count(1) == 0)
assert_true(d.damage_class(1, 60) == DAMAGE_NONE)
assert_true(d.is_dirty(1, 0, 0) == false)
```

</details>

#### classifies a full 8K frame with overflow-safe i64 area math

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(0, 0, 7680, 4320)
assert_true(d.dirty_count(1) == 8160)
assert_true(d.dirty_pixels(1) == 33177600)
assert_true(d.damage_class(1, 60) == DAMAGE_FULL)
```

</details>

### SABOTAGE: O2 damage gates reject force-full and dropped-tile behavior

#### exact local counts differ from a force-full redraw

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(1, 1, 1, 1)
assert_true(d.dirty_count(1) == 1)
assert_true(d.dirty_count(1) != d.level_capacity[1] as i64)
assert_true(d.dirty_pixels(1) != 33177600)
```

</details>

#### old plus new bounds cannot silently drop either tile

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = make_8k_damage()
d.mark_rect(0, 0, 64, 64)
d.mark_rect(128, 0, 64, 64)
assert_true(d.dirty_count(1) == 2)
assert_true(d.is_dirty(1, 0, 0))
assert_true(d.is_dirty(1, 2, 0))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering O2 multiscale damage tiles, SABOTAGE: O2 damage gates reject force-full and dropped-tile behavior.
- O2 multiscale damage tiles
- SABOTAGE: O2 damage gates reject force-full and dropped-tile behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f36c17f7a3ae97f701a76d9236c9736c7930e3324239b5505a08acf45b812839`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f36c17f7a3ae97f701a76d9236c9736c7930e3324239b5505a08acf45b812839`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f36c17f7a3ae97f701a76d9236c9736c7930e3324239b5505a08acf45b812839`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **79/100**; blockers: **0**.

SSpec documentization score: 79/100
source: test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/damage_tiles_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/damage_tiles_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/damage_tiles_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-003 REQ-005 builds exact 8K grids including ragged bottom edges' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-001 REQ-003 REQ-005 marks one bottom-right pixel at every configured scale' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-002 deduplicates overlapping damage within a frame' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl:58:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'REQ-004 marks old and new transform bounds without forcing full damage' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->

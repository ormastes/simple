# WM Retained Old/New Damage — Behavioral Specification

> Behavioral companion to the source-text contract specs: drives `Engine2dWmFrameExecutor.retained_scene_damage_plan` / `record_successful_scene` directly and asserts SEMANTICS, not substrings — a moved window must dirty BOTH its vacated (old) extents and its current extents; no prior frame or a changed background identity must fail closed to a full-frame plan with an explicit invalid fallback reason.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Retained Old/New Damage — Behavioral Specification

Behavioral companion to the source-text contract specs: drives `Engine2dWmFrameExecutor.retained_scene_damage_plan` / `record_successful_scene` directly and asserts SEMANTICS, not substrings — a moved window must dirty BOTH its vacated (old) extents and its current extents; no prior frame or a changed background identity must fail closed to a full-frame plan with an explicit invalid fallback reason.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Behavioral companion to the source-text contract specs: drives
`Engine2dWmFrameExecutor.retained_scene_damage_plan` /
`record_successful_scene` directly and asserts SEMANTICS, not substrings —
a moved window must dirty BOTH its vacated (old) extents and its current
extents; no prior frame or a changed background identity must fail closed
to a full-frame plan with an explicit invalid fallback reason.

Added per external (Codex) review finding #2, 2026-08-15.

## Scenarios

### retained old/new damage plan semantics

#### fails closed to a full invalid-reason plan without a prior frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed to a full invalid-reason plan without a prior frame
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.fallback_reason equals `DAMAGE_FALLBACK_INVALID`
   - Expected: plan.planned_pixels equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to a full invalid-reason plan without a prior frame")
var executor = _executor()
val bg = shared_wm_background_color(0xff101010u32)
val plan = executor.retained_scene_damage_plan(
    _scene(10, 10, bg), engine2d_wm_background_key(_scene(10, 10, bg)), 1)
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
expect(plan.planned_pixels).to_equal(W * H)
```

</details>

#### marks both vacated and current extents for a moved window

- marks both vacated and current extents for a moved window


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks both vacated and current extents for a moved window")
var executor = _executor()
val bg = shared_wm_background_color(0xff101010u32)
val first = _scene(10, 10, bg)
executor.record_successful_scene(
    first, engine2d_wm_background_key(first), 1)
# window moved far away; revision changed
val moved = _scene(150, 150, bg)
val plan = executor.retained_scene_damage_plan(
    moved, engine2d_wm_background_key(moved), 2)
# the plan must cover pixels at BOTH the old and the new location;
# a correct old/new plan needs at least both window areas' pixels
# (window content rect is 64x48 plus titlebar band)
expect(plan.planned_pixels).to_be_greater_than((64 * 48 * 2 - 1).to_i64())
# and must NOT be a blind full-frame fallback
expect(plan.planned_pixels).to_be_less_than(W * H)
```

</details>

#### covers the full window bounds including chrome for a moved window

- covers the full window bounds including chrome for a moved window


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("covers the full window bounds including chrome for a moved window")
var executor = _executor()
val bg = shared_wm_background_color(0xff101010u32)
val first = _scene(10, 10, bg)
executor.record_successful_scene(
    first, engine2d_wm_background_key(first), 1)
val moved = _scene(150, 150, bg)
val plan = executor.retained_scene_damage_plan(
    moved, engine2d_wm_background_key(moved), 2)
# The old titlebar/border chrome starts at the window ORIGIN (10,10),
# which the titlebar-inset content rect excluded. The plan must cover
# both the vacated origin and the new origin, or moves leave stale
# chrome behind (external review F3).
var covers_old = false
var covers_new = false
var i: i64 = 0
while i + 3 < plan.rects.len():
    val x = plan.rects[i]
    val y = plan.rects[i + 1]
    val w = plan.rects[i + 2]
    val h = plan.rects[i + 3]
    if x <= 10 and y <= 10 and x + w > 10 and y + h > 10:
        covers_old = true
    if x <= 150 and y <= 150 and x + w > 150 and y + h > 150:
        covers_new = true
    i = i + 4
assert_true(covers_old)
assert_true(covers_new)
```

</details>

#### fails closed to full when the taskbar revision changes

- fails closed to full when the taskbar revision changes
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.fallback_reason equals `DAMAGE_FALLBACK_INVALID`
   - Expected: plan.planned_pixels equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to full when the taskbar revision changes")
var executor = _executor()
val bg = shared_wm_background_color(0xff101010u32)
val first = _scene(10, 10, bg)
executor.record_successful_scene(
    first, engine2d_wm_background_key(first), 1, 7, "09:41")
val plan = executor.retained_scene_damage_plan(
    first, engine2d_wm_background_key(first), 2, 8, "09:41")
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.fallback_reason).to_equal(DAMAGE_FALLBACK_INVALID)
expect(plan.planned_pixels).to_equal(W * H)
```

</details>

#### fails closed to full when only the clock label changes

- fails closed to full when only the clock label changes
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.planned_pixels equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to full when only the clock label changes")
var executor = _executor()
val bg = shared_wm_background_color(0xff101010u32)
val first = _scene(10, 10, bg)
executor.record_successful_scene(
    first, engine2d_wm_background_key(first), 1, 7, "09:41")
val plan = executor.retained_scene_damage_plan(
    first, engine2d_wm_background_key(first), 2, 7, "09:42")
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.planned_pixels).to_equal(W * H)
```

</details>

#### fails closed to full when the background identity changes

- fails closed to full when the background identity changes
   - Expected: plan.mode equals `DAMAGE_PLAN_FULL`
   - Expected: plan.planned_pixels equals `W * H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed to full when the background identity changes")
var executor = _executor()
val bg1 = shared_wm_background_color(0xff101010u32)
val first = _scene(10, 10, bg1)
executor.record_successful_scene(
    first, engine2d_wm_background_key(first), 1)
val bg2 = shared_wm_background_color(0xff2020ffu32)
val changed = _scene(10, 10, bg2)
val plan = executor.retained_scene_damage_plan(
    changed, engine2d_wm_background_key(changed), 2)
expect(plan.mode).to_equal(DAMAGE_PLAN_FULL)
expect(plan.planned_pixels).to_equal(W * H)
```

</details>

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

- Canonical SPipe generation for source `3e0591eea945fd2732bd23bc636740d118e7d4fb2efb822ce475575bf2a13280`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3e0591eea945fd2732bd23bc636740d118e7d4fb2efb822ce475575bf2a13280`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3e0591eea945fd2732bd23bc636740d118e7d4fb2efb822ce475575bf2a13280`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/wm_retained_damage_behavior_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/wm_retained_damage_behavior_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/wm_retained_damage_behavior_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed to a full invalid-reason plan without a prior frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks both vacated and current extents for a moved window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/wm_retained_damage_behavior_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers the full window bounds including chrome for a moved window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

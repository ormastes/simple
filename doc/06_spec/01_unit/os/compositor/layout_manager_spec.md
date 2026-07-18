# Layout Manager Specification

> <details>

<!-- sdn-diagram:id=layout_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layout_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layout_manager_spec -> os
layout_manager_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layout_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Manager Specification

## Scenarios

### LayoutManager

#### creates with correct screen dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lm = _make_lm(1920, 1080, 48)
expect(lm.screen_width).to_equal(1920)
expect(lm.screen_height).to_equal(1080)
expect(lm.taskbar_height).to_equal(48)
```

</details>

#### starts with no slide over

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lm = _make_lm(1920, 1080, 48)
expect(lm.slide_over_id).to_equal(-1)
```

</details>

#### starts with no pip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lm = _make_lm(1920, 1080, 48)
expect(lm.pip_id).to_equal(-1)
```

</details>

#### defaults to FullScreen mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lm = _make_lm(1920, 1080, 48)
# Default for unknown window is FullScreen
val layout = lm.compute_layout(1)
expect(layout.x).to_equal(0)
expect(layout.y).to_equal(0)
expect(layout.width).to_equal(1920)
expect(layout.height).to_equal(1032)
```

</details>

### LayoutManager compute_layout FullScreen

#### fills entire usable area

1. var lm =  make lm
2. lm set mode
   - Expected: layout.x equals `0`
   - Expected: layout.y equals `0`
   - Expected: layout.width equals `1024`
   - Expected: layout.height equals `720`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1024, 768, 48)
lm.set_mode(1, WindowMode.FullScreen)
val layout = lm.compute_layout(1)
expect(layout.x).to_equal(0)
expect(layout.y).to_equal(0)
expect(layout.width).to_equal(1024)
expect(layout.height).to_equal(720)
```

</details>

### LayoutManager compute_layout Split

#### computes SplitLeft at 50% ratio

1. var lm =  make lm
2. lm apply split view
   - Expected: left.x equals `0`
   - Expected: left.y equals `0`
   - Expected: left.width equals `960`
   - Expected: left.height equals `1032`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.apply_split_view(1, 2, 0.5)
val left = lm.compute_layout(1)
expect(left.x).to_equal(0)
expect(left.y).to_equal(0)
expect(left.width).to_equal(960)
expect(left.height).to_equal(1032)
```

</details>

#### computes SplitRight at 50% ratio

1. var lm =  make lm
2. lm apply split view
   - Expected: right.x equals `960`
   - Expected: right.y equals `0`
   - Expected: right.width equals `960`
   - Expected: right.height equals `1032`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.apply_split_view(1, 2, 0.5)
val right = lm.compute_layout(2)
expect(right.x).to_equal(960)
expect(right.y).to_equal(0)
expect(right.width).to_equal(960)
expect(right.height).to_equal(1032)
```

</details>

#### computes SplitLeft at 33% ratio

1. var lm =  make lm
2. lm apply split view
   - Expected: left.x equals `0`
   - Expected: left.width equals `396`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1200, 800, 40)
lm.apply_split_view(10, 20, 0.33)
val left = lm.compute_layout(10)
# 1200 * 0.33 = 396
expect(left.x).to_equal(0)
expect(left.width).to_equal(396)
```

</details>

#### computes SplitRight at 67% ratio

1. var lm =  make lm
2. lm apply split view
   - Expected: right.x equals `804`
   - Expected: right.width equals `396`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1200, 800, 40)
lm.apply_split_view(10, 20, 0.67)
val right = lm.compute_layout(20)
# left_w = 1200 * 0.67 = 804
expect(right.x).to_equal(804)
expect(right.width).to_equal(396)
```

</details>

### LayoutManager compute_layout SlideOver

#### places slide-over panel at right edge

1. var lm =  make lm
2. lm set slide over
   - Expected: layout.width equals `320`
   - Expected: layout.x equals `1590`
   - Expected: layout.y equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_slide_over(5)
val layout = lm.compute_layout(5)
expect(layout.width).to_equal(320)
expect(layout.x).to_equal(1590)
expect(layout.y).to_equal(20)
```

</details>

#### tracks slide_over_id

1. var lm =  make lm
2. lm set slide over
   - Expected: lm.slide_over_id equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_slide_over(7)
expect(lm.slide_over_id).to_equal(7)
```

</details>

### LayoutManager compute_layout PiP

#### places PiP at bottom-right corner

1. var lm =  make lm
2. lm set pip
   - Expected: layout.width equals `260`
   - Expected: layout.height equals `160`
   - Expected: layout.x equals `1640`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_pip(3)
val layout = lm.compute_layout(3)
expect(layout.width).to_equal(260)
expect(layout.height).to_equal(160)
expect(layout.x).to_equal(1640)
```

</details>

#### tracks pip_id

1. var lm =  make lm
2. lm set pip
   - Expected: lm.pip_id equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_pip(9)
expect(lm.pip_id).to_equal(9)
```

</details>

### LayoutManager compute_layout StageManager

#### returns default cascade position

1. var lm =  make lm
2. lm set mode
   - Expected: layout.x equals `100`
   - Expected: layout.y equals `70`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_mode(1, WindowMode.StageManager)
val layout = lm.compute_layout(1)
# offset = (1 % 5) * 40 = 40
expect(layout.x).to_equal(100)
expect(layout.y).to_equal(70)
```

</details>

#### uses stored position when available

1. var lm =  make lm
2. lm set stage position
   - Expected: layout.x equals `200`
   - Expected: layout.y equals `100`
   - Expected: layout.width equals `800`
   - Expected: layout.height equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
val custom = WindowLayout(x: 200, y: 100, width: 800, height: 600)
lm.set_stage_position(1, custom)
val layout = lm.compute_layout(1)
expect(layout.x).to_equal(200)
expect(layout.y).to_equal(100)
expect(layout.width).to_equal(800)
expect(layout.height).to_equal(600)
```

</details>

### LayoutManager Minimized

#### hides window below screen

1. var lm =  make lm
2. lm set mode
   - Expected: layout.y equals `1080`
   - Expected: layout.width equals `0`
   - Expected: layout.height equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lm = _make_lm(1920, 1080, 48)
lm.set_mode(1, WindowMode.Minimized)
val layout = lm.compute_layout(1)
expect(layout.y).to_equal(1080)
expect(layout.width).to_equal(0)
expect(layout.height).to_equal(0)
```

</details>

### SnapZone detection

#### detects left edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(5, 400, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.LeftHalf)
```

</details>

#### detects right edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(1910, 400, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.RightHalf)
```

</details>

#### detects top edge as FullScreen

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(960, 5, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.FullScreen)
```

</details>

#### detects bottom edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(960, 1075, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.BottomHalf)
```

</details>

#### detects top-left corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(5, 5, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.TopLeftQuarter)
```

</details>

#### detects top-right corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(1915, 5, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.TopRightQuarter)
```

</details>

#### detects bottom-left corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(5, 1075, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.BottomLeftQuarter)
```

</details>

#### detects bottom-right corner

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(1915, 1075, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.BottomRightQuarter)
```

</details>

#### returns None_ when not near any edge

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zone = detect_snap_zone(960, 540, 1920, 1080, 20)
expect(zone).to_equal(SnapZone.None_)
```

</details>

### compute_snap_layout

#### computes LeftHalf layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = compute_snap_layout(SnapZone.LeftHalf, 1920, 1080, 48)
expect(layout.x).to_equal(0)
expect(layout.y).to_equal(0)
expect(layout.width).to_equal(960)
expect(layout.height).to_equal(1032)
```

</details>

#### computes RightHalf layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = compute_snap_layout(SnapZone.RightHalf, 1920, 1080, 48)
expect(layout.x).to_equal(960)
expect(layout.width).to_equal(960)
```

</details>

#### computes FullScreen layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = compute_snap_layout(SnapZone.FullScreen, 1920, 1080, 48)
expect(layout.x).to_equal(0)
expect(layout.y).to_equal(0)
expect(layout.width).to_equal(1920)
expect(layout.height).to_equal(1032)
```

</details>

#### computes TopLeftQuarter layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = compute_snap_layout(SnapZone.TopLeftQuarter, 1920, 1080, 48)
expect(layout.x).to_equal(0)
expect(layout.y).to_equal(0)
expect(layout.width).to_equal(960)
expect(layout.height).to_equal(516)
```

</details>

#### computes BottomRightQuarter layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = compute_snap_layout(SnapZone.BottomRightQuarter, 1920, 1080, 48)
expect(layout.x).to_equal(960)
expect(layout.y).to_equal(516)
expect(layout.width).to_equal(960)
expect(layout.height).to_equal(516)
```

</details>

### SpringConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_default_spring()
expect(cfg.stiffness).to_equal(200.0)
expect(cfg.damping).to_equal(20.0)
expect(cfg.mass).to_equal(1.0)
```

</details>

#### creates bouncy config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_bouncy_spring()
expect(cfg.stiffness).to_equal(300.0)
expect(cfg.damping).to_equal(10.0)
```

</details>

#### creates smooth config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_smooth_spring()
expect(cfg.stiffness).to_equal(100.0)
expect(cfg.damping).to_equal(20.0)
```

</details>

#### creates stiff config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = _make_stiff_spring()
expect(cfg.stiffness).to_equal(500.0)
expect(cfg.damping).to_equal(30.0)
```

</details>

### SpringAnimation

#### creates with initial values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anim = _make_spring_anim(0.0, 100.0)
expect(anim.current).to_equal(0.0)
expect(anim.from_value).to_equal(0.0)
expect(anim.to_value).to_equal(100.0)
expect(anim.velocity).to_equal(0.0)
expect(anim.is_complete).to_equal(false)
```

</details>

#### moves toward target after step

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anim = _make_spring_anim(0.0, 100.0)
val stepped = spring_step(anim, 0.016)
# Should have moved toward 100.0
expect(stepped.current).to_be_greater_than(0.0)
expect(stepped.is_complete).to_equal(false)
```

</details>

#### converges to target after many steps

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_spring_to_rest(_make_spring_anim(0.0, 100.0))
expect(result.is_complete).to_equal(true)
expect(result.current).to_equal(100.0)
```

</details>

#### snaps to target when at rest

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _run_spring_to_rest(_make_stiff_anim(0.0, 50.0))
# When complete, current should be exactly to_value
expect(result.current).to_equal(50.0)
expect(result.velocity).to_equal(0.0)
```

</details>

#### does not advance when already complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val settled = _run_spring_to_rest(_make_stiff_anim(0.0, 10.0))
# Step again - should not change
val again = spring_step(settled, 0.016)
expect(again.current).to_equal(10.0)
expect(again.is_complete).to_equal(true)
```

</details>

#### tracks elapsed time

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anim = _make_spring_anim(0.0, 100.0)
val s1 = spring_step(anim, 0.016)
val s2 = spring_step(s1, 0.016)
expect(s2.elapsed).to_be_greater_than(0.03)
```

</details>

#### is_at_rest returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anim = _make_spring_anim(0.0, 100.0)
expect(spring_is_at_rest(anim)).to_equal(false)
```

</details>

#### bouncy config overshoots target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_val = _run_spring_max(_make_bouncy_anim(0.0, 100.0))
# Bouncy spring should overshoot past 100.0
expect(max_val).to_be_greater_than(100.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/layout_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LayoutManager
- LayoutManager compute_layout FullScreen
- LayoutManager compute_layout Split
- LayoutManager compute_layout SlideOver
- LayoutManager compute_layout PiP
- LayoutManager compute_layout StageManager
- LayoutManager Minimized
- SnapZone detection
- compute_snap_layout
- SpringConfig
- SpringAnimation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

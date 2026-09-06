# Reftest Specification

> <details>

<!-- sdn-diagram:id=reftest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reftest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reftest_spec -> std
reftest_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reftest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reftest Specification

## Scenarios

### Drawing parity reftest suite

#### harness starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = reftest_harness_new()
expect(h.result_count()).to_equal(0)
```

</details>

#### runs one scene and records result

1. var h = reftest harness new
   - Expected: r.op_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = reftest_harness_new()
val pic = winding_scene()
val m = _manifest("path_winding", "winding fill rule")
val r = h.run(m, pic)
expect(r.op_count >= 0).to_equal(true)
```

</details>

#### result_count increases after each scene

1. var h = reftest harness new
2. h run
3. h run
   - Expected: h.result_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = reftest_harness_new()
val m1 = _manifest("path_winding", "winding fill")
val m2 = _manifest("path_evenodd", "even-odd fill")
h.run(m1, winding_scene())
h.run(m2, evenodd_scene())
expect(h.result_count()).to_equal(2)
```

</details>

#### find returns Some for registered scene

1. var h = reftest harness new
2. h run
   - Expected: found.is_some() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var h = reftest_harness_new()
val m = _manifest("dashed_strokes", "dashed path effect")
h.run(m, dashed_scene())
val found = h.find("dashed_strokes")
expect(found.is_some()).to_equal(true)
```

</details>

#### find returns None for unknown scene

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = reftest_harness_new()
val found = h.find("nonexistent")
expect(found.is_none()).to_equal(true)
```

</details>

### 10 scenes produce distinct signatures

#### all 10 scene signatures are unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s0 = scene_signature(winding_scene())
val s1 = scene_signature(evenodd_scene())
val s2 = scene_signature(dashed_scene())
val s3 = scene_signature(gradient_scene())
val s4 = scene_signature(arabic_scene())
val s5 = scene_signature(porterduff_scene())
val s6 = scene_signature(mixblend_scene())
val s7 = scene_signature(backdrop_scene())
val s8 = scene_signature(scroll_scene())
val s9 = scene_signature(transform_scene())
val s10 = scene_signature(opacity_scene())
# Each cull_rect differs, so coord_sum differs, so signature differs.
expect(s0 == s1).to_equal(false)
expect(s1 == s2).to_equal(false)
expect(s2 == s3).to_equal(false)
expect(s3 == s4).to_equal(false)
expect(s4 == s5).to_equal(false)
expect(s5 == s6).to_equal(false)
expect(s6 == s7).to_equal(false)
expect(s7 == s8).to_equal(false)
expect(s8 == s9).to_equal(false)
expect(s9 == s10).to_equal(false)
```

</details>

#### same scene produces same signature when called twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = scene_signature(winding_scene())
val b = scene_signature(winding_scene())
expect(a).to_equal(b)
```

</details>

### compare_pictures stub

#### identical signatures return ratio 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = winding_scene()
val sig = scene_signature(pic)
val diff = compare_pictures(sig, sig)
expect(diff.ratio).to_equal(0.0)
```

</details>

#### identical signatures return max_channel_delta 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = evenodd_scene()
val sig = scene_signature(pic)
val diff = compare_pictures(sig, sig)
expect(diff.max_channel_delta).to_equal(0)
```

</details>

#### different signatures return ratio 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig_a = scene_signature(winding_scene())
val sig_b = scene_signature(evenodd_scene())
val diff = compare_pictures(sig_a, sig_b)
expect(diff.ratio).to_equal(1.0)
```

</details>

#### different signatures return max_channel_delta 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig_a = scene_signature(porterduff_scene())
val sig_b = scene_signature(mixblend_scene())
val diff = compare_pictures(sig_a, sig_b)
expect(diff.max_channel_delta).to_equal(255)
```

</details>

### Scene cull rects match Chromium spec

#### path_winding cull is 200x200

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = winding_scene()
val r = pic.cull_rect
expect(r.right).to_equal(200.0)
expect(r.bottom).to_equal(200.0)
```

</details>

#### porter_duff cull is 300x300

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = porterduff_scene()
val r = pic.cull_rect
expect(r.right).to_equal(300.0)
expect(r.bottom).to_equal(300.0)
```

</details>

#### scroll_damage cull is 400x400

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = scroll_scene()
val r = pic.cull_rect
expect(r.right).to_equal(400.0)
expect(r.bottom).to_equal(400.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/reftest/parity/reftest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Drawing parity reftest suite
- 10 scenes produce distinct signatures
- compare_pictures stub
- Scene cull rects match Chromium spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

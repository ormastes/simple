# skeletal_spec

> Engine Animation — Skeletal animation system tests

<!-- sdn-diagram:id=skeletal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=skeletal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

skeletal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=skeletal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# skeletal_spec

Engine Animation — Skeletal animation system tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/skeletal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Animation — Skeletal animation system tests

Tests skeleton bone hierarchy, animation clip sampling,
animation blender layer management, and skinning data.

## Scenarios

### Skeleton

#### creates empty skeleton

1. var skel = Skeleton new
   - Expected: skel.bone_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("test")
expect(skel.bone_count()).to_equal(0)
```

</details>

#### adds bones and returns indices

1. var skel = Skeleton new
   - Expected: root_idx equals `0`
   - Expected: spine_idx equals `1`
   - Expected: skel.bone_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("humanoid")
val root_idx = skel.add_bone("root", -1, BoneTransform.identity())
val spine_idx = skel.add_bone("spine", 0, BoneTransform.identity())
expect(root_idx).to_equal(0)
expect(spine_idx).to_equal(1)
expect(skel.bone_count()).to_equal(2)
```

</details>

#### finds bone by name

1. var skel = Skeleton new
2. skel add bone
3. skel add bone
   - Expected: skel.find_bone("knee") equals `1`
   - Expected: skel.find_bone("missing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("test")
skel.add_bone("hip", -1, BoneTransform.identity())
skel.add_bone("knee", 0, BoneTransform.identity())
expect(skel.find_bone("knee")).to_equal(1)
expect(skel.find_bone("missing")).to_equal(-1)
```

</details>

#### gets bone by index

1. var skel = Skeleton new
2. skel add bone
   - Expected: b.name equals `root`
   - Expected: b.parent_index equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("test")
skel.add_bone("root", -1, BoneTransform.identity())
if val Some(b) = skel.get_bone(0):
    expect(b.name).to_equal("root")
    expect(b.parent_index).to_equal(-1)
```

</details>

#### gets children of a bone

1. var skel = Skeleton new
2. skel add bone
3. skel add bone
4. skel add bone
5. skel add bone
   - Expected: children.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("test")
skel.add_bone("root", -1, BoneTransform.identity())
skel.add_bone("left_arm", 0, BoneTransform.identity())
skel.add_bone("right_arm", 0, BoneTransform.identity())
skel.add_bone("left_hand", 1, BoneTransform.identity())
val children = skel.get_children(0)
expect(children.len()).to_equal(2)
```

</details>

#### sets local transform

1. var skel = Skeleton new
2. skel add bone
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skel = Skeleton.new("test")
skel.add_bone("root", -1, BoneTransform.identity())
val moved = BoneTransform(
    tx: 1.0, ty: 2.0, tz: 3.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
val ok = skel.set_local_transform(0, moved)
expect(ok).to_equal(true)
if val Some(b) = skel.get_bone(0):
    val tx_i = b.local_transform.tx * 100.0
    expect(tx_i).to_be_greater_than(99.0)
    expect(tx_i).to_be_less_than(101.0)
```

</details>

### BoneTransform

#### identity has correct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = BoneTransform.identity()
val rw_i = id.rw * 1000.0
expect(rw_i).to_be_greater_than(999.0)
expect(rw_i).to_be_less_than(1001.0)
val sx_i = id.sx * 1000.0
expect(sx_i).to_be_greater_than(999.0)
expect(sx_i).to_be_less_than(1001.0)
val tx_i = id.tx * 1000.0
expect(tx_i).to_be_greater_than(-1.0)
expect(tx_i).to_be_less_than(1.0)
```

</details>

#### lerp_to interpolates halfway

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = BoneTransform(
    tx: 0.0, ty: 0.0, tz: 0.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
val b = BoneTransform(
    tx: 10.0, ty: 20.0, tz: 30.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 2.0, sy: 2.0, sz: 2.0
)
val mid = a.lerp_to(b, 0.5)
val mid_tx = mid.tx * 100.0
expect(mid_tx).to_be_greater_than(499.0)
expect(mid_tx).to_be_less_than(501.0)
val mid_sy = mid.sy * 100.0
expect(mid_sy).to_be_greater_than(149.0)
expect(mid_sy).to_be_less_than(151.0)
```

</details>

### BoneTrack

#### samples between keyframes

1. var track = BoneTrack new
2. track add keyframe
3. track add keyframe


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = BoneTrack.new(0)
val kf_a = BoneTransform(
    tx: 0.0, ty: 0.0, tz: 0.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
val kf_b = BoneTransform(
    tx: 10.0, ty: 0.0, tz: 0.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
track.add_keyframe(0.0, kf_a)
track.add_keyframe(1.0, kf_b)
val sampled = track.sample(0.5)
val s_tx = sampled.tx * 100.0
expect(s_tx).to_be_greater_than(499.0)
expect(s_tx).to_be_less_than(501.0)
```

</details>

#### clamps before first keyframe

1. var track = BoneTrack new
2. track add keyframe


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = BoneTrack.new(0)
val kf = BoneTransform(
    tx: 5.0, ty: 0.0, tz: 0.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
track.add_keyframe(1.0, kf)
val sampled = track.sample(0.0)
val s_tx = sampled.tx * 100.0
expect(s_tx).to_be_greater_than(499.0)
expect(s_tx).to_be_less_than(501.0)
```

</details>

#### clamps after last keyframe

1. var track = BoneTrack new
2. track add keyframe


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = BoneTrack.new(0)
val kf = BoneTransform(
    tx: 7.0, ty: 0.0, tz: 0.0,
    rx: 0.0, ry: 0.0, rz: 0.0, rw: 1.0,
    sx: 1.0, sy: 1.0, sz: 1.0
)
track.add_keyframe(0.0, kf)
val sampled = track.sample(10.0)
val s_tx = sampled.tx * 100.0
expect(s_tx).to_be_greater_than(699.0)
expect(s_tx).to_be_less_than(701.0)
```

</details>

### AnimationClipData

#### creates clip and adds tracks

1. var clip = AnimationClipData new
2. var track = BoneTrack new
3. track add keyframe
4. clip add track
   - Expected: clip.track_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clip = AnimationClipData.new("walk", 2.0, true)
var track = BoneTrack.new(0)
track.add_keyframe(0.0, BoneTransform.identity())
clip.add_track(track)
expect(clip.track_count()).to_equal(1)
```

</details>

#### finds track by bone index

1. var clip = AnimationClipData new
2. var t0 = BoneTrack new
3. var t1 = BoneTrack new
4. t0 add keyframe
5. t1 add keyframe
6. clip add track
7. clip add track
   - Expected: found.bone_index equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var clip = AnimationClipData.new("run", 1.0, false)
var t0 = BoneTrack.new(0)
var t1 = BoneTrack.new(3)
t0.add_keyframe(0.0, BoneTransform.identity())
t1.add_keyframe(0.0, BoneTransform.identity())
clip.add_track(t0)
clip.add_track(t1)
if val Some(found) = clip.get_track(3):
    expect(found.bone_index).to_equal(3)
```

</details>

### AnimationBlender

#### adds and retrieves layers

1. var blender = AnimationBlender new
   - Expected: idx equals `0`
   - Expected: blender.layer_count() equals `1`
   - Expected: layer.clip_name equals `walk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blender = AnimationBlender.new(10)
val idx = blender.add_layer("walk", 1.0)
expect(idx).to_equal(0)
expect(blender.layer_count()).to_equal(1)
if val Some(layer) = blender.get_layer(0):
    expect(layer.clip_name).to_equal("walk")
    val w_i = layer.weight * 1000.0
    expect(w_i).to_be_greater_than(999.0)
    expect(w_i).to_be_less_than(1001.0)
```

</details>

#### sets layer weight

1. var blender = AnimationBlender new
2. blender add layer
3. blender set layer weight


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blender = AnimationBlender.new(10)
blender.add_layer("idle", 1.0)
blender.set_layer_weight(0, 0.5)
if val Some(layer) = blender.get_layer(0):
    val w_i = layer.weight * 1000.0
    expect(w_i).to_be_greater_than(499.0)
    expect(w_i).to_be_less_than(501.0)
```

</details>

#### sets layer time

1. var blender = AnimationBlender new
2. blender add layer
3. blender set layer time


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blender = AnimationBlender.new(10)
blender.add_layer("run", 1.0)
blender.set_layer_time(0, 0.75)
if val Some(layer) = blender.get_layer(0):
    val t_i = layer.time * 1000.0
    expect(t_i).to_be_greater_than(749.0)
    expect(t_i).to_be_less_than(751.0)
```

</details>

#### removes layer

1. var blender = AnimationBlender new
2. blender add layer
3. blender add layer
   - Expected: removed is true
   - Expected: blender.layer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blender = AnimationBlender.new(10)
blender.add_layer("a", 1.0)
blender.add_layer("b", 0.5)
val removed = blender.remove_layer(0)
expect(removed).to_equal(true)
expect(blender.layer_count()).to_equal(1)
```

</details>

#### clears all layers

1. var blender = AnimationBlender new
2. blender add layer
3. blender add layer
4. blender clear
   - Expected: blender.layer_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var blender = AnimationBlender.new(10)
blender.add_layer("a", 1.0)
blender.add_layer("b", 0.5)
blender.clear()
expect(blender.layer_count()).to_equal(0)
```

</details>

### SkinData

#### adds vertex weights

1. var skin = SkinData new
2. var sw = SkinWeight new
3. sw add influence
4. sw add influence
5. skin add vertex weight
   - Expected: skin.vertex_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var skin = SkinData.new()
var sw = SkinWeight.new()
sw.add_influence(0, 0.7)
sw.add_influence(1, 0.3)
skin.add_vertex_weight(sw)
expect(skin.vertex_count()).to_equal(1)
```

</details>

#### limits influences to 4

1. var sw = SkinWeight new
2. sw add influence
3. sw add influence
4. sw add influence
5. sw add influence
6. sw add influence
   - Expected: sw.influence_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sw = SkinWeight.new()
sw.add_influence(0, 0.4)
sw.add_influence(1, 0.3)
sw.add_influence(2, 0.2)
sw.add_influence(3, 0.1)
sw.add_influence(4, 0.05)
expect(sw.influence_count()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

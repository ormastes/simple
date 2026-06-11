# Engine Animation Facade Specification

> <details>

<!-- sdn-diagram:id=engine_animation_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_animation_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_animation_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_animation_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Animation Facade Specification

## Scenarios

### gc_async_mut engine animation facade

#### re-exports skeleton, clip, blender, and skinning surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity = BoneTransform.identity()
expect(identity.rw).to_equal(1.0)
val bone = Bone(name: "root", index: 0, parent_index: -1, bind_pose: identity, local_transform: identity)
expect(bone.name).to_equal("root")
val skeleton = Skeleton.new("rig")
expect(skeleton.bone_count()).to_equal(0)

val keyframe = Keyframe(time: 0.0, transform: identity)
expect(keyframe.time).to_equal(0.0)
val track = BoneTrack.new(0)
expect(track.keyframe_count()).to_equal(0)
val clip = AnimationClipData.new("idle", 1.0, true)
expect(clip.track_count()).to_equal(0)

val layer = BlendLayer(clip_name: "idle", weight: 1.0, time: 0.0)
expect(layer.clip_name).to_equal("idle")
val blender = AnimationBlender.new(1)
expect(blender.layer_count()).to_equal(0)

val skin_weight = SkinWeight.new()
expect(skin_weight.influence_count()).to_equal(0)
val skin = SkinData.new()
expect(skin.vertex_count()).to_equal(0)
```

</details>

#### re-exports IK and timeline surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ik_sqrt(4.0)).to_be_greater_than(1.9)
val joint = IKJoint(x: 0.0, y: 0.0, bone_length: 1.0)
expect(joint.bone_length).to_equal(1.0)
val target = IKTarget(x: 1.0, y: 1.0)
expect(target.y).to_equal(1.0)
val chain = IKChain.new(0.01, 4)
expect(chain.joint_count()).to_equal(0)

val key = TimelineKey(time: 0.0, value: 1.0, easing: "linear")
expect(key.value).to_equal(1.0)
val timeline_track = TimelineTrack.new("x", "position.x")
expect(timeline_track.key_count()).to_equal(0)
expect(apply_easing(0.5, "linear")).to_equal(0.5)
val timeline = Timeline.new("cutscene", 2.0)
expect(timeline.track_count()).to_equal(0)
expect(timeline.is_playing()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/animation/engine_animation_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut engine animation facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

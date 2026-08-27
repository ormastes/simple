# Engine Animation Facade Specification

> Tests covering nogc_async_mut engine animation facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Animation Facade Specification

## Scenarios

### nogc_async_mut engine animation facade

#### re-exports skeleton, clip, blender, and skinning surfaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports skeleton, clip, blender, and skinning surfaces
   - Expected: identity.rw equals `1.0`
   - Expected: bone.name equals `root`
   - Expected: skeleton.bone_count() equals `0`
   - Expected: keyframe.time equals `0.0`
   - Expected: track.keyframe_count() equals `0`
   - Expected: clip.track_count() equals `0`
   - Expected: layer.clip_name equals `idle`
   - Expected: blender.layer_count() equals `0`
   - Expected: skin_weight.influence_count() equals `0`
   - Expected: skin.vertex_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports skeleton, clip, blender, and skinning surfaces")
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

- re-exports IK and timeline surfaces
   - Expected: joint.bone_length equals `1.0`
   - Expected: target.y equals `1.0`
   - Expected: chain.joint_count() equals `0`
   - Expected: key.value equals `1.0`
   - Expected: timeline_track.key_count() equals `0`
   - Expected: apply_easing(0.5, "linear") equals `0.5`
   - Expected: timeline.track_count() equals `0`
   - Expected: timeline.is_playing() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports IK and timeline surfaces")
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
| Source | `test/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut engine animation facade.
- nogc_async_mut engine animation facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `b0df18f641d7f668612619c000bd554deee0bf2c381850e54b1a08b545af7df7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b0df18f641d7f668612619c000bd554deee0bf2c381850e54b1a08b545af7df7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b0df18f641d7f668612619c000bd554deee0bf2c381850e54b1a08b545af7df7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports skeleton, clip, blender, and skinning surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/engine/animation/engine_animation_facade_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports IK and timeline surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

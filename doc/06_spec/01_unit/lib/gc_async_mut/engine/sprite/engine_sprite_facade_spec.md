# Engine Sprite Facade Specification

> Tests covering gc_async_mut engine sprite facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Sprite Facade Specification

## Scenarios

### gc_async_mut engine sprite facade

#### re-exports texture, atlas, sprite, and builder behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports texture, atlas, sprite, and builder behavior
   - Expected: tex.width equals `2`
   - Expected: tex.pixels.len() equals `4`
   - Expected: region.width equals `2`
   - Expected: region.height equals `2`
   - Expected: sheet.frame_count() equals `4`
   - Expected: animator.current_frame() equals `0`
   - Expected: layout.sprite_count() equals `1`
   - Expected: packed_sprite.name equals `hero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports texture, atlas, sprite, and builder behavior")
val color = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val packed = pack_color(color)
expect(packed).to_be_greater_than(0)
expect(unpack_color(packed).r).to_be_greater_than(0.99)
val tex = Texture.create_solid(2, 2, color)
expect(tex.width).to_equal(2)
expect(tex.pixels.len()).to_equal(4)
var atlas = TextureAtlas.create(8, 8)
val region = atlas.pack(2, 2, tex.pixels)
expect(region.width).to_equal(2)
expect(region.height).to_equal(2)
val tid = TextureId(raw: RawHandle.new(0, 1))
val sheet = SpriteSheet.create(tid, 16, 16, 2, 2)
expect(sheet.frame_count()).to_equal(4)
val animator = SpriteAnimator.create(sheet)
expect(animator.current_frame()).to_equal(0)
var builder = AtlasBuilder.new(1)
builder.add_sprite("hero", 16, 16)
val layout = builder.pack()
expect(layout.sprite_count()).to_equal(1)
val packed_sprite = layout.sprites[0]
expect(packed_sprite.name).to_equal("hero")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine sprite facade.
- gc_async_mut engine sprite facade

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

- Canonical SPipe generation for source `4fcb56dcad0569cb4a32cb454cb93056e90e9f70fed68c85cf0c35e9d135d20a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fcb56dcad0569cb4a32cb454cb93056e90e9f70fed68c85cf0c35e9d135d20a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fcb56dcad0569cb4a32cb454cb93056e90e9f70fed68c85cf0c35e9d135d20a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/sprite/engine_sprite_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports texture, atlas, sprite, and builder behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

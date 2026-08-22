# Shared Font Material Across 2D Surfaces

> Verifies the shared font surfaces behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Font Material Across 2D Surfaces

Verifies the shared font surfaces behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the shared font surfaces behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### shared font surfaces

#### should prepare stable glyph quads and no warm dirty upload

- Verify: should prepare stable glyph quads and no warm dirty upload
- Prepare one shared font batch for 2D
   - Expected: cold.dirty_rects.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: warm.dirty_rects.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: warm.atlas_generation equals `cold.atlas_generation`
   - Expected: warm.atlas_owner_identity() equals `cold.atlas_owner_identity()`
   - Expected: warm.atlas_cache_identity() equals `cold.atlas_cache_identity()`
   - Expected: warm.quads[0].atlas_x equals `cold.quads[0].atlas_x`
   - Expected: warm.quads[0].byte_offset equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: warm.quads[1].byte_offset equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: dirty.atlas_owner_identity() equals `warm.atlas_owner_identity()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-009 REQ-011
step("Verify: should prepare stable glyph quads and no warm dirty upload")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare one shared font batch for 2D")
var renderer = setup_shared_font_fixture()
val cold = renderer.prepare_text("AB", 0xFF336699u32, 16)
val warm = renderer.prepare_text("AB", 0xFFCC8844u32, 16)
expect_shared_font_batch(cold, 2)
expect_shared_font_batch(warm, 2)
expect(cold.dirty_rects.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(warm.dirty_rects.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(warm.atlas_generation).to_equal(cold.atlas_generation)
expect(warm.atlas_owner_identity()).to_equal(cold.atlas_owner_identity())
expect(warm.atlas_cache_identity()).to_equal(cold.atlas_cache_identity())
expect(warm.quads[0].atlas_x).to_equal(cold.quads[0].atlas_x)
expect(warm.quads[0].byte_offset).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(warm.quads[1].byte_offset).to_equal(1)  # oracle: pinned constant asserted by this scenario
val dirty = renderer.prepare_text("ABC", 0xFFCC8844u32, 16)
expect(dirty.dirty_rects.len()).to_be_greater_than(0)
expect(dirty.atlas_owner_identity()).to_equal(warm.atlas_owner_identity())
assert_not_equal(dirty.atlas_cache_identity(), warm.atlas_cache_identity())
```

</details>

#### should carry one validated runtime configuration through every material path

- Verify: should carry one validated runtime configuration through every material path
- Prepare one shared font batch for 2D
   - Expected: text_batch.render_config_identity equals `config.identity()`
   - Expected: text_batch.execution_target equals `cpu`
   - Expected: text_batch.execution_policy equals `FontExecutionPolicy.Required`
   - Expected: renderer.prepare_glyph_run_configured(run, 0xFFFFFFFFu32, config).render_config_identity equals `config.identity()`
   - Expected: selected_config_identity equals `config.identity()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-009 REQ-015 REQ-011
step("Verify: should carry one validated runtime configuration through every material path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare one shared font batch for 2D")
var renderer = setup_shared_font_fixture()
val config = FontRenderConfig(
    family: "Noto Sans Mono", category: "mono", language: "en", script: "latn", size: 16,
    weight: "normal", style: "normal", hinting: "none", antialiasing: "grayscale",
    atlas_policy: "shared-alpha-1024", execution_target: "cpu",
    execution_policy: FontExecutionPolicy.Required
)
val text_batch = renderer.prepare_text_configured("A", 0xFFFFFFFFu32, config)
val advanced_batch = renderer.prepare_text_with_advances_configured(
    "A", [12], 0xFFFFFFFFu32, config
)
expect_shared_font_batch(text_batch, 1)
expect_shared_font_batch(advanced_batch, 1)
expect(text_batch.render_config_identity).to_equal(config.identity())
expect(text_batch.execution_target).to_equal("cpu")
expect(text_batch.execution_policy).to_equal(FontExecutionPolicy.Required)
val run = FontGlyphRun(valid: false, face_id: 0, face_generation: 0,
    glyph_ids: [], xs: [], ys: [], clusters: [])
expect(renderer.prepare_glyph_run_configured(run, 0xFFFFFFFFu32, config).render_config_identity).to_equal(config.identity())
val selected_config_identity = renderer.prepare_selected_glyph_run_configured(
    draw_ir_empty_glyph_run_payload(), 0xFFFFFFFFu32, config
).render_config_identity
expect(selected_config_identity).to_equal(config.identity())
```

</details>

#### should preserve selected font identity across cold and warm batches

- Verify: should preserve selected font identity across cold and warm batches
   - Expected: warm.font_identity equals `cold.font_identity`
   - Expected: warm.face_generation equals `cold.face_generation`
   - Expected: stale.0 equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: stale.1 equals ``
   - Expected: empty.font_identity equals ``
   - Expected: empty.face_generation equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: invalid.font_identity equals ``
   - Expected: invalid.face_generation equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-009 REQ-015
step("Verify: should preserve selected font identity across cold and warm batches")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var renderer = FontRenderer.browser_serif_default()
val cold = renderer.prepare_text("A", 0xFFFFFFFFu32, 16)
val warm = renderer.prepare_text("A", 0xFFFFFFFFu32, 16)

expect(warm.font_identity).to_equal(cold.font_identity)
expect(warm.face_generation).to_equal(cold.face_generation)
if cold.font_identity != "":
    expect(cold.face_generation).to_be_greater_than(0)
    val selected_rasterizer = renderer.ttf_rasterizer
    renderer.clear_ttf()
    if selected_rasterizer != nil:
        val stale = selected_rasterizer.cache_identity_snapshot()
        expect(stale.0).to_equal(0)  # oracle: pinned constant asserted by this scenario
        expect(stale.1).to_equal("")
    val empty = renderer.prepare_text("", 0xFFFFFFFFu32, 16)
    val invalid = renderer.prepare_text("A", 0xFFFFFFFFu32, 0)
    expect(empty.font_identity).to_equal("")
    expect(empty.face_generation).to_equal(0)  # oracle: pinned constant asserted by this scenario
    expect(invalid.font_identity).to_equal("")
    expect(invalid.face_generation).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should feed the 2D blend surface from the shared white-alpha atlas

- Verify: should feed the 2D blend surface from the shared white-alpha atlas
   - Expected: pixels.len() equals `(quad.width * quad.height).to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-009 REQ-015 REQ-011
step("Verify: should feed the 2D blend surface from the shared white-alpha atlas")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var renderer = setup_shared_font_fixture()
val batch = renderer.prepare_text("A", 0x80402010u32, 16)
expect_shared_font_batch(batch, 1)
val quad = batch.quads[0]
val pixels = engine2d_font_atlas_subrect_pixels(
    batch.atlas_pixels, batch.atlas_width, batch.atlas_height,
    quad.atlas_x, quad.atlas_y, quad.width, quad.height, quad.color
)
expect(pixels.len()).to_equal((quad.width * quad.height).to_i64())
expect(_nonzero_pixels(pixels)).to_be_greater_than(0)
```

</details>

#### should fail closed for invalid sizes and empty content

- Verify: should fail closed for invalid sizes and empty content
   - Expected: invalid.font_identity equals ``
   - Expected: invalid.face_generation equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: empty.font_identity equals ``
   - Expected: empty.face_generation equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-009 REQ-015 REQ-011
step("Verify: should fail closed for invalid sizes and empty content")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var renderer = setup_shared_font_fixture()
val invalid = renderer.prepare_text("A", 0xFFFFFFFFu32, 0)
expect(invalid.valid).to_be(false)
expect(invalid.font_identity).to_equal("")
expect(invalid.face_generation).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(renderer.prepare_text("A", 0xFFFFFFFFu32, 513).valid).to_be(false)
val empty = renderer.prepare_text("", 0xFFFFFFFFu32, 16)
expect(empty.valid).to_be(true)
expect(empty.is_empty()).to_be(true)
expect(empty.font_identity).to_equal("")
expect(empty.face_generation).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should snapshot supplied glyph-run generation without claiming an identity

- Verify: should snapshot supplied glyph-run generation without claiming an identity
   - Expected: batch.font_identity equals ``
   - Expected: batch.face_generation equals `37)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-006 REQ-009 REQ-015 REQ-011
step("Verify: should snapshot supplied glyph-run generation without claiming an identity")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var renderer = setup_shared_font_fixture()
val run = FontGlyphRun(valid: false, face_id: 0, face_generation: 37,
    glyph_ids: [], xs: [], ys: [], clusters: [])
val batch = renderer.prepare_glyph_run(run, 0xFFFFFFFFu32, 16)

expect(batch.valid).to_be(false)
expect(batch.font_identity).to_equal("")
expect(batch.face_generation).to_equal(37)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37c519feda9e8e87d1c579846b7fabfe64b75d1a41a4a7ef45c718a90c69793e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37c519feda9e8e87d1c579846b7fabfe64b75d1a41a4a7ef45c718a90c69793e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37c519feda9e8e87d1c579846b7fabfe64b75d1a41a4a7ef45c718a90c69793e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prepare stable glyph quads and no warm dirty upload' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry one validated runtime configuration through every material path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve selected font identity across cold and warm batches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:138:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should feed the 2D blend surface from the shared white-alpha atlas' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:153:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for invalid sizes and empty content' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl:169:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should snapshot supplied glyph-run generation without claiming an identity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->

# Shared Font Material Across 2D Surfaces

> Checks one persistent 2D glyph batch, warm atlas reuse, atlas-subrect blending, and fail-closed material behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Font Material Across 2D Surfaces

Checks one persistent 2D glyph batch, warm atlas reuse, atlas-subrect blending, and fail-closed material behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Checks one persistent 2D glyph batch, warm atlas reuse, atlas-subrect blending, and fail-closed material behavior.

CPU output is an oracle and compatibility path, not native GPU proof. This lane
does not claim native texture upload, submission, fence, device readback, or presentation.
Engine3D CPU HUD/world compatibility remains in
`test/01_unit/lib/gpu/engine3d/font_compat_spec.spl` so this 2D system spec does
not statically close over optional Vulkan symbols. Font configuration remains
transient material input and is not serialized into Draw IR; captured identity
does not claim atomic process-global font replacement or a global lock.

## Scenarios

### shared font surfaces

#### should prepare stable glyph quads and no warm dirty upload

- Prepare one shared font batch for 2D
- var renderer = setup shared font fixture
- expect shared font batch
- expect shared font batch
   - Expected: cold.dirty_rects.len() equals `2`
   - Expected: warm.dirty_rects.len() equals `0`
   - Expected: warm.atlas_generation equals `cold.atlas_generation`
   - Expected: warm.atlas_owner_identity() equals `cold.atlas_owner_identity()`
   - Expected: warm.atlas_cache_identity() equals `cold.atlas_cache_identity()`
   - Expected: warm.quads[0].atlas_x equals `cold.quads[0].atlas_x`
   - Expected: warm.quads[0].byte_offset equals `0`
   - Expected: warm.quads[1].byte_offset equals `1`
   - Expected: dirty.atlas_owner_identity() equals `warm.atlas_owner_identity()`
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepare one shared font batch for 2D")
var renderer = setup_shared_font_fixture()
val cold = renderer.prepare_text("AB", 0xFF336699u32, 16)
val warm = renderer.prepare_text("AB", 0xFFCC8844u32, 16)
expect_shared_font_batch(cold, 2)
expect_shared_font_batch(warm, 2)
expect(cold.dirty_rects.len()).to_equal(2)
expect(warm.dirty_rects.len()).to_equal(0)
expect(warm.atlas_generation).to_equal(cold.atlas_generation)
expect(warm.atlas_owner_identity()).to_equal(cold.atlas_owner_identity())
expect(warm.atlas_cache_identity()).to_equal(cold.atlas_cache_identity())
expect(warm.quads[0].atlas_x).to_equal(cold.quads[0].atlas_x)
expect(warm.quads[0].byte_offset).to_equal(0)
expect(warm.quads[1].byte_offset).to_equal(1)
val dirty = renderer.prepare_text("ABC", 0xFFCC8844u32, 16)
expect(dirty.dirty_rects.len()).to_be_greater_than(0)
expect(dirty.atlas_owner_identity()).to_equal(warm.atlas_owner_identity())
assert_not_equal(dirty.atlas_cache_identity(), warm.atlas_cache_identity())
```

</details>

#### should carry one validated runtime configuration through every material path

- Prepare one shared font batch for 2D
- var renderer = setup shared font fixture
- expect shared font batch
- expect shared font batch
   - Expected: text_batch.render_config_identity equals `config.identity()`
   - Expected: text_batch.execution_target equals `cpu`
   - Expected: text_batch.execution_policy equals `FontExecutionPolicy.Required`
   - Expected: renderer.prepare_glyph_run_configured(run, 0xFFFFFFFFu32, config).render_config_identity equals `config.identity()`
- draw ir empty glyph run payload
   - Expected: selected_config_identity equals `config.identity()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var renderer = FontRenderer browser serif default
   - Expected: warm.font_identity equals `cold.font_identity`
   - Expected: warm.face_generation equals `cold.face_generation`
- renderer clear ttf
   - Expected: stale.0 equals `0`
   - Expected: stale.1 equals ``
   - Expected: empty.font_identity equals ``
   - Expected: empty.face_generation equals `0`
   - Expected: invalid.font_identity equals ``
   - Expected: invalid.face_generation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        expect(stale.0).to_equal(0)
        expect(stale.1).to_equal("")
    val empty = renderer.prepare_text("", 0xFFFFFFFFu32, 16)
    val invalid = renderer.prepare_text("A", 0xFFFFFFFFu32, 0)
    expect(empty.font_identity).to_equal("")
    expect(empty.face_generation).to_equal(0)
    expect(invalid.font_identity).to_equal("")
    expect(invalid.face_generation).to_equal(0)
```

</details>

#### should feed the 2D blend surface from the shared white-alpha atlas

- var renderer = setup shared font fixture
- expect shared font batch
   - Expected: pixels.len() equals `(quad.width * quad.height).to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var renderer = setup shared font fixture
   - Expected: invalid.font_identity equals ``
   - Expected: invalid.face_generation equals `0`
   - Expected: empty.font_identity equals ``
   - Expected: empty.face_generation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = setup_shared_font_fixture()
val invalid = renderer.prepare_text("A", 0xFFFFFFFFu32, 0)
expect(invalid.valid).to_be(false)
expect(invalid.font_identity).to_equal("")
expect(invalid.face_generation).to_equal(0)
expect(renderer.prepare_text("A", 0xFFFFFFFFu32, 513).valid).to_be(false)
val empty = renderer.prepare_text("", 0xFFFFFFFFu32, 16)
expect(empty.valid).to_be(true)
expect(empty.is_empty()).to_be(true)
expect(empty.font_identity).to_equal("")
expect(empty.face_generation).to_equal(0)
```

</details>

#### should snapshot supplied glyph-run generation without claiming an identity

- var renderer = setup shared font fixture
   - Expected: batch.font_identity equals ``
   - Expected: batch.face_generation equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = setup_shared_font_fixture()
val run = FontGlyphRun(valid: false, face_id: 0, face_generation: 37,
    glyph_ids: [], xs: [], ys: [], clusters: [])
val batch = renderer.prepare_glyph_run(run, 0xFFFFFFFFu32, 16)

expect(batch.valid).to_be(false)
expect(batch.font_identity).to_equal("")
expect(batch.face_generation).to_equal(37)
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

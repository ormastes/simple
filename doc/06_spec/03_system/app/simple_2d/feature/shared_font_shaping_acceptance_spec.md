# Exact-face Shared Font Shaping Acceptance

> Exercises the selected bundled face through loading, Pure Simple shaping, and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exact-face Shared Font Shaping Acceptance

Exercises the selected bundled face through loading, Pure Simple shaping, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/shared_font_shaping_acceptance_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the selected bundled face through loading, Pure Simple shaping, and
the canonical FontRenderer material path. Complex-script completion stays an
explicit release blocker until GSUB/GPOS is complete.

## Scenarios

### shared font shaping acceptance

#### should accept 54 identity native cells and the Chinese mono identity fallback

- Accept exact-face-bound simple-script shaping
   - Expected: rows.len() equals `55`
- keys push
   - Expected: native_count equals `54`
   - Expected: fallback_count equals `1`
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- setup selected shaping face
- expect simple row material
- assert not equal
   - Expected: cmap_glyph_id(mono.parsed, codepoint) equals `0u32`
   - Expected: glyph_index(mono.handle, codepoint as i64) equals `0`
- assert not equal
   - Expected: fallback_row.proposed_status equals `fallback`
   - Expected: fallback_row.family equals `Noto Sans SC`
- expect simple row material


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept exact-face-bound simple-script shaping")
val rows = simple_shaping_acceptance_rows()
expect(rows.len()).to_equal(55)
var native_count: i64 = 0
var fallback_count: i64 = 0
var keys: [text] = []
for row in rows:
    val key = row.language + "/" + row.category
    expect(keys.contains(key)).to_be(false)
    keys.push(key)
    if row.proposed_status == "native": native_count = native_count + 1
    elif row.proposed_status == "fallback": fallback_count = fallback_count + 1
    else: fail("unsupported proposed shaping status: " + row.proposed_status)
expect(native_count).to_equal(54)
expect(fallback_count).to_equal(1)
val fixtures = [
    setup_selected_shaping_face("Noto Sans SC"),
    setup_selected_shaping_face("Noto Serif SC"),
    setup_selected_shaping_face("Noto Sans Mono"),
    setup_selected_shaping_face("Bungee"),
    setup_selected_shaping_face("Nunito"),
    setup_selected_shaping_face("Caveat"),
    setup_selected_shaping_face("Roboto Slab"),
    setup_selected_shaping_face("UnifrakturCook"),
    setup_selected_shaping_face("Pixelify Sans")
]
for fixture in fixtures:
    expect(font_face_is_live(fixture.handle.handle, fixture.handle.generation)).to_be(true)
for row in rows:
    if row.proposed_status == "native":
        expect_simple_row_material(_fixture_for_family(fixtures, row.family), row)

val mono = _fixture_for_family(fixtures, "Noto Sans Mono")
val sc = _fixture_for_family(fixtures, "Noto Sans SC")
assert_not_equal(mono.handle.handle, sc.handle.handle)
expect(font_face_is_live(mono.handle.handle, mono.handle.generation)).to_be(true)
expect(font_face_is_live(sc.handle.handle, sc.handle.generation)).to_be(true)
for codepoint in _codepoints("中文"):
    expect(cmap_glyph_id(mono.parsed, codepoint)).to_equal(0u32)
    expect(glyph_index(mono.handle, codepoint as i64)).to_equal(0)
    assert_not_equal(cmap_glyph_id(sc.parsed, codepoint), 0u32)
    expect(glyph_index(sc.handle, codepoint as i64) > 0).to_be(true)
val fallback_fixture = _zh_mono_fallback_fixture(mono, sc)
val fallback_row = _simple_row_for_cell(rows, "zh", "mono")
expect(fallback_row.proposed_status).to_equal("fallback")
expect(fallback_row.family).to_equal("Noto Sans SC")
expect_simple_row_material(fallback_fixture, fallback_row)
expect(font_face_is_live(mono.handle.handle, mono.handle.generation)).to_be(true)

for fixture in fixtures: free_font(fixture.handle)
```

</details>

#### should reject a selected-face missing glyph

- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = setup_selected_shaping_face("Bungee")
val codepoint = 1114111u32
expect(cmap_glyph_id(fixture.parsed, codepoint)).to_equal(0u32)
expect(glyph_index(fixture.handle, codepoint as i64)).to_equal(0)
val runs = shaper_shape_with_language(fixture.shaper, [codepoint], fixture.font,
    0.0, 0.0, "und")
expect(runs.len()).to_equal(1)
expect(runs[0].glyph_indices_valid).to_be(false)
expect(runs[0].substitution_complete).to_be(false)
expect(runs[0].positioning_complete).to_be(false)
expect(shaped_run_to_font_glyph_run(runs[0]).valid).to_be(false)
free_font(fixture.handle)
```

</details>

#### should reject shaped material after the selected face becomes stale

- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = setup_selected_shaping_face("Bungee")
val run = expect_simple_identity_run(fixture, "B", "en", Script.Latin)
val glyph_run = shaped_run_to_font_glyph_run(run)
free_font(fixture.handle)
expect(fixture.renderer.prepare_glyph_run(glyph_run, 0xFFFFFFFFu32, 32).valid).to_be(false)
```

</details>

#### should retain unique live face identities across A to B to A and evict stale dependencies

- "|" + second identity len
- var renderer = FontRenderer new
   - Expected: first_batch.font_identity equals `first_identity`
   - Expected: second_batch.font_identity equals `combined_identity`
   - Expected: warm_first.font_identity equals `second_batch.font_identity`
   - Expected: warm_first.atlas_generation equals `second_batch.atlas_generation`
   - Expected: warm_first.atlas_owner_identity() equals `second_batch.atlas_owner_identity()`
   - Expected: warm_first.atlas_cache_identity() equals `second_batch.atlas_cache_identity()`
- free font
   - Expected: font_face_identity(first.handle.handle, first.handle.generation) equals ``
   - Expected: after_stale.font_identity equals `second_identity`
- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = setup_selected_shaping_face("Bungee")
val second = setup_selected_shaping_face("Nunito")
val first_run = shaped_run_to_font_glyph_run(expect_simple_identity_run(first, "A", "en", Script.Latin))
val second_run = shaped_run_to_font_glyph_run(expect_simple_identity_run(second, "B", "en", Script.Latin))
val first_identity = selected_font_asset_identity(first.asset)
val second_identity = selected_font_asset_identity(second.asset)
val combined_identity = "font-faces-v1|" + first_identity.len().to_string() + ":" + first_identity +
    "|" + second_identity.len().to_string() + ":" + second_identity
var renderer = FontRenderer.new()

val first_batch = renderer.prepare_glyph_run(first_run, 0xFFFFFFFFu32, 32)
expect(first_batch.font_identity).to_equal(first_identity)
val second_batch = renderer.prepare_glyph_run(second_run, 0xFFFFFFFFu32, 32)
expect(second_batch.font_identity).to_equal(combined_identity)
val warm_first = renderer.prepare_glyph_run(first_run, 0xFFFFFFFFu32, 32)
expect(warm_first.font_identity).to_equal(second_batch.font_identity)
expect(warm_first.atlas_generation).to_equal(second_batch.atlas_generation)
expect(warm_first.atlas_owner_identity()).to_equal(second_batch.atlas_owner_identity())
expect(warm_first.atlas_cache_identity()).to_equal(second_batch.atlas_cache_identity())

free_font(first.handle)
expect(font_face_identity(first.handle.handle, first.handle.generation)).to_equal("")
val after_stale = renderer.prepare_glyph_run(second_run, 0xFFFFFFFFu32, 32)
expect(after_stale.valid).to_be(true)
expect(after_stale.font_identity).to_equal(second_identity)
expect(after_stale.atlas_generation).to_be_greater_than(warm_first.atlas_generation)
free_font(second.handle)
```

</details>

#### should accept the exact Arabic and Urdu witnesses and reject unselected sequences

- Shape selected Unicode scripts with the pinned face
   - Expected: selected_font_coverage_cell("ar", "sans").?.status equals `native`
   - Expected: selected_font_coverage_cell("ur", "sans").?.status equals `native`
   - Expected: selected_font_coverage_cell("ar", "serif").?.status equals `unavailable`
   - Expected: selected_font_coverage_cell("ur", "serif").?.status equals `unavailable`
   - Expected: selected_font_coverage_cell("ar", "mono").?.status equals `fallback`
   - Expected: selected_font_coverage_cell("ar", "mono").?.witness_family equals `Noto Sans Arabic`
   - Expected: selected_font_coverage_cell("ur", "mono").?.status equals `fallback`
   - Expected: selected_font_coverage_cell("ur", "mono").?.witness_family equals `Noto Sans Arabic`
- expect selected unicode shaping
- expect selected unicode shaping
- expect complex run rejected
- free font
- expect selected unicode shaping
- expect selected unicode shaping
- expect complex run rejected
- expect complex run rejected
- expect complex run rejected
- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Shape selected Unicode scripts with the pinned face")
expect(selected_font_simple_tuple_accepted("Noto Sans Arabic", "ar")).to_be(true)
expect(selected_font_simple_tuple_accepted("Noto Sans Arabic", "ur")).to_be(true)
expect(selected_font_simple_tuple_accepted("Noto Naskh Arabic", "ar")).to_be(false)
expect(selected_font_simple_tuple_accepted("Noto Naskh Arabic", "ur")).to_be(false)
expect(selected_font_coverage_cell("ar", "sans").?.status).to_equal("native")
expect(selected_font_coverage_cell("ur", "sans").?.status).to_equal("native")
expect(selected_font_coverage_cell("ar", "serif").?.status).to_equal("unavailable")
expect(selected_font_coverage_cell("ur", "serif").?.status).to_equal("unavailable")
expect(selected_font_asset_for_language_category("ar", "serif")).to_be_nil()
expect(selected_font_asset_for_language_category("ur", "serif")).to_be_nil()
expect(selected_font_coverage_cell("ar", "mono").?.status).to_equal("fallback")
expect(selected_font_coverage_cell("ar", "mono").?.witness_family).to_equal("Noto Sans Arabic")
expect(selected_font_coverage_cell("ur", "mono").?.status).to_equal("fallback")
expect(selected_font_coverage_cell("ur", "mono").?.witness_family).to_equal("Noto Sans Arabic")
val arabic = setup_selected_shaping_face("Noto Sans Arabic")
expect_selected_unicode_shaping(arabic, "العربية", "ar", Script.Arabic)
expect_selected_unicode_shaping(arabic, "اردو", "ur", Script.Arabic)
expect_complex_run_rejected(arabic, "بَ", "ar")
free_font(arabic.handle)
val naskh = setup_selected_shaping_face("Noto Naskh Arabic")
expect_selected_unicode_shaping(naskh, "العربية", "ar", Script.Arabic)
expect_selected_unicode_shaping(naskh, "اردو", "ur", Script.Arabic)
expect_complex_run_rejected(naskh, "العربية", "ur")
expect_complex_run_rejected(naskh, "اردو", "ar")
expect_complex_run_rejected(naskh, "بَ", "ar")
free_font(naskh.handle)
```

</details>

#### should accept the exact Hindi dev2 witness and reject other complex sequences

- expect selected unicode shaping
- expect complex run rejected
- free font
- expect selected unicode shaping
- expect complex run rejected
- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(selected_font_simple_tuple_accepted("Noto Sans Devanagari", "hi")).to_be(true)
expect(selected_font_simple_tuple_accepted("Noto Serif Devanagari", "hi")).to_be(false)
expect(selected_font_coverage_cell("hi", "sans").?.status).to_equal("native")
expect(selected_font_coverage_cell("hi", "serif").?.status).to_equal("unavailable")
expect(selected_font_asset_for_language_category("hi", "serif")).to_be_nil()
expect(selected_font_coverage_cell("hi", "mono").?.status).to_equal("fallback")
expect(selected_font_coverage_cell("hi", "mono").?.witness_family).to_equal("Noto Sans Devanagari")
val devanagari = setup_selected_shaping_face("Noto Sans Devanagari")
expect_selected_unicode_shaping(devanagari, "हिन्दी", "hi", Script.Devanagari)
expect_complex_run_rejected(devanagari, "र्क", "hi")
free_font(devanagari.handle)
val serif_devanagari = setup_selected_shaping_face("Noto Serif Devanagari")
expect_selected_unicode_shaping(serif_devanagari, "हिन्दी", "hi", Script.Devanagari)
expect_complex_run_rejected(serif_devanagari, "र्क", "hi")
free_font(serif_devanagari.handle)
```

</details>

#### should accept exact single-codepoint emoji material and reject sequences

- expect complex run rejected
- expect complex run rejected
- expect complex run rejected
- expect complex run rejected
- free font


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = setup_selected_shaping_face("Noto Emoji")
for language in ["en", "zh", "es", "hi", "ar", "fr", "pt", "ru", "ur", "id"]:
    val run = expect_simple_identity_run(fixture, "😀", language, Script.Emoji)
    val glyph_run = shaped_run_to_font_glyph_run(run)
    expect(glyph_run.valid).to_be(true)
    val batch = fixture.renderer.prepare_glyph_run(glyph_run, 0xFFFFFFFFu32, 32)
    expect(batch.valid).to_be(true)
    expect(batch.face_generation).to_equal(fixture.handle.generation)
    expect(batch.quads.len()).to_equal(1)
    val quad = batch.quads[0]
    val pixels = font_atlas_subrect_pixels(batch.atlas_pixels, batch.atlas_width, batch.atlas_height,
        quad.atlas_x, quad.atlas_y, quad.width, quad.height, quad.color)
    var nonzero: i64 = 0
    for pixel in pixels:
        if pixel != 0u32: nonzero = nonzero + 1
    expect(nonzero).to_be_greater_than(0)
    expect(selected_font_simple_tuple_accepted("Noto Emoji", language)).to_be(true)
    expect(selected_font_coverage_cell(language, "emoji").?.status).to_equal("native")
    expect(selected_font_asset_for_language_category(language, "emoji").?.family).to_equal("Noto Emoji")
expect_complex_run_rejected(fixture, "😀😀", "und")
expect_complex_run_rejected(fixture, "😀️", "und")
expect_complex_run_rejected(fixture, "😀🏻", "und")
expect_complex_run_rejected(fixture, "😀‍😀", "und")
free_font(fixture.handle)
```

</details>

#### should shape and materialize exact registered-only SimpleOS witnesses

- Accept exact-face-bound simple-script shaping
   - Expected: registered equals `2`
- font renderer use registered selected bytes only
   - Expected: arabic.reason equals `resolved`
   - Expected: hindi.reason equals `resolved`
- var renderer = FontRenderer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept exact-face-bound simple-script shaping")
var registered = 0
for asset in selected_font_asset_candidates():
    if asset.family == "Noto Sans Arabic" or asset.family == "Noto Sans Devanagari":
        expect(font_renderer_register_selected_bytes(asset.local_path, file_read_bytes(asset.local_path))).to_be(true)
        registered = registered + 1
expect(registered).to_equal(2)
font_renderer_use_registered_selected_bytes_only()
val arabic = resolve_font_metrics_with_language("sans-serif", "العربية", 32, "ar")
val hindi = resolve_font_metrics_with_language("sans-serif", "हिन्दी", 32, "hi")
expect(arabic.reason).to_equal("resolved")
expect(arabic.glyph_run.valid).to_be(true)
expect(hindi.reason).to_equal("resolved")
expect(hindi.glyph_run.valid).to_be(true)
var renderer = FontRenderer.new()
expect(renderer.try_load_registered_identity(arabic.identity)).to_be(true)
val arabic_batch = renderer.prepare_selected_glyph_run(arabic.glyph_run, 0xFFFFFFFFu32, 32)
expect(arabic_batch.valid).to_be(true)
expect(arabic_batch.quads.len()).to_be_greater_than(0)
expect(renderer.try_load_registered_identity(hindi.identity)).to_be(true)
val hindi_batch = renderer.prepare_selected_glyph_run(hindi.glyph_run, 0xFFFFFFFFu32, 32)
expect(hindi_batch.valid).to_be(true)
expect(hindi_batch.quads.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

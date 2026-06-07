# Font Renderer Specification

> <details>

<!-- sdn-diagram:id=font_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=font_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

font_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=font_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Renderer Specification

## Scenarios

### shared font renderer fallbacks

#### renders vector glyph coverage with antialiasing evidence

- var renderer = FontRenderer new
   - Expected: glyph.height equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = FontRenderer.new()
renderer.use_bitmap = false

val glyph = renderer.get_glyph(65, 24)

expect(glyph.width).to_be_greater_than(0)
expect(glyph.height).to_equal(24)
expect(_count_nonzero_alpha(glyph.pixels)).to_be_greater_than(0)
expect(_count_partial_alpha(glyph.pixels)).to_be_greater_than(0)
```

</details>

#### renders Simple Vector Outline glyphs into an ARGB buffer

- var renderer = FontRenderer new


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = FontRenderer.new()
renderer.use_bitmap = false
val bg = 0xFFFFFFFFu32
val fg = 0xFF000000u32
val buffer = [bg; 40 * 32]

val rendered = renderer.render_text(buffer, 40, 32, 2, 3, "A", fg, 24)

expect(_count_painted_pixels(rendered, bg)).to_be_greater_than(0)
expect(_count_antialiased_argb_pixels(rendered, bg, fg)).to_be_greater_than(0)
```

</details>

#### renders bitmap glyph fallback with exact mask evidence

- reset bitmap font raster stats
- var renderer = FontRenderer new
   - Expected: glyph.width equals `8`
   - Expected: glyph.height equals `16`
   - Expected: stats.attempts equals `1`
   - Expected: stats.cpu_fallback_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_bitmap_font_raster_stats()
var renderer = FontRenderer.new()
renderer.use_vector = false

val glyph = renderer.get_glyph(65, 16)
val stats = bitmap_font_accelerator_stats()

expect(glyph.width).to_equal(8)
expect(glyph.height).to_equal(16)
expect(_count_nonzero_alpha(glyph.pixels)).to_be_greater_than(0)
expect(_count_full_alpha(glyph.pixels)).to_be_greater_than(0)
expect(stats.attempts).to_equal(1)
expect(stats.cpu_fallback_hits).to_equal(1)
```

</details>

#### accepts bitmap glyph pixels returned by a backend rasterizer

- reset bitmap font raster stats
-  set cuda bitmap font probe glyph
- var renderer = FontRenderer new
   - Expected: glyph.width equals `1`
   - Expected: glyph.height equals `1`
   - Expected: glyph.advance equals `2`
   - Expected: glyph.pixels[0].to_i32() equals `255`
   - Expected: stats.attempts equals `1`
   - Expected: stats.cuda_hits equals `1`
   - Expected: stats.gpu_returned_glyphs equals `1`
   - Expected: stats.gpu_returned_glyph_pixels equals `1`
   - Expected: stats.unavailable_reason equals `cuda-bitmap-font-glyph-pixels-returned`
-  clear cuda bitmap font probe glyph


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_bitmap_font_raster_stats()
_set_cuda_bitmap_font_probe_glyph()
var renderer = FontRenderer.new()
renderer.use_vector = false

val glyph = renderer.get_glyph(65, 16)
val stats = bitmap_font_accelerator_stats()

expect(glyph.width).to_equal(1)
expect(glyph.height).to_equal(1)
expect(glyph.advance).to_equal(2)
expect(glyph.pixels[0].to_i32()).to_equal(255)
expect(stats.attempts).to_equal(1)
expect(stats.cuda_hits).to_equal(1)
expect(stats.gpu_returned_glyphs).to_equal(1)
expect(stats.gpu_returned_glyph_pixels).to_equal(1)
expect(stats.unavailable_reason).to_equal("cuda-bitmap-font-glyph-pixels-returned")
_clear_cuda_bitmap_font_probe_glyph()
```

</details>

#### keeps Chrome-compatible serif font candidates ahead of fallback fonts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = browser_serif_font_candidates()
expect(candidates[0]).to_equal(browser_chrome_compatible_normal_font_path())
expect(candidates[1]).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
expect(candidates[2]).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerifSC-Regular.otf")
```

</details>

#### keeps provided browser sans and mono candidates ahead of host fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sans = browser_sans_font_candidates()
val mono = browser_mono_font_candidates()
expect(sans[0]).to_equal("examples/09_embedded/simple_os/fonts/sans/NotoSans-Regular.ttf")
expect(sans[1]).to_equal("/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf")
expect(mono[0]).to_equal("examples/09_embedded/simple_os/fonts/mono/FiraCodeNerdFontMono-Regular.ttf")
expect(mono[1]).to_equal("/usr/share/fonts/truetype/liberation/LiberationMono-Regular.ttf")
```

</details>

#### maps browser CSS font-family names to provided font lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(browser_font_candidates_for_family("monospace")[0]).to_equal("examples/09_embedded/simple_os/fonts/mono/FiraCodeNerdFontMono-Regular.ttf")
expect(browser_font_candidates_for_family("'Fira Code', monospace")[0]).to_equal("examples/09_embedded/simple_os/fonts/mono/FiraCodeNerdFontMono-Regular.ttf")
expect(browser_font_candidates_for_family("Arial, sans-serif")[0]).to_equal("examples/09_embedded/simple_os/fonts/sans/NotoSans-Regular.ttf")
expect(browser_font_candidates_for_family("system")[0]).to_equal(browser_chrome_compatible_normal_font_path())
expect(browser_font_candidates_for_family("Times New Roman, serif")[0]).to_equal(browser_chrome_compatible_normal_font_path())
```

</details>

#### selects one Chrome-compatible normal font and one vector fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(browser_chrome_compatible_normal_font_name()).to_equal("Liberation Serif Regular")
expect(browser_chrome_compatible_normal_font_path()).to_equal("/usr/share/fonts/truetype/liberation/LiberationSerif-Regular.ttf")
expect(browser_chrome_compatible_vector_font_name()).to_equal("Simple Vector Outline")
```

</details>

#### builds browser default renderers from selected font lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = FontRenderer.browser_serif_default()
expect(renderer.use_vector).to_equal(true)
expect(renderer.use_bitmap).to_equal(true)
val mono_renderer = FontRenderer.browser_default_for_family("monospace")
expect(mono_renderer.use_vector).to_equal(true)
expect(mono_renderer.use_bitmap).to_equal(true)
```

</details>

#### exposes an opt-in browser default font materialization surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val provided = browser_provided_font_paths()
expect(provided).to_contain("examples/09_embedded/simple_os/fonts/sans/NotoSans-Regular.ttf")
expect(provided).to_contain("examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
expect(provided).to_contain("examples/09_embedded/simple_os/fonts/mono/FiraCodeNerdFontMono-Regular.ttf")
expect(browser_font_download_script_path()).to_equal("examples/09_embedded/simple_os/fonts/download_fonts.shs")

val result = ensure_browser_provided_fonts(false, 1)
expect(result.attempted_download).to_equal(false)
expect(result.status == "available" or result.status == "missing").to_equal(true)
```

</details>

#### extracts font-face source URLs for browser font materialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = "@font-face { font-family: Demo; src: url('/fonts/demo.woff2') format('woff2'), url(\"https://cdn.example/demo.ttf\") format('truetype'); } body { color: red }"
val urls = browser_font_face_source_urls(css)
expect(urls.len()).to_equal(2)
expect(urls[0]).to_equal("/fonts/demo.woff2")
expect(urls[1]).to_equal("https://cdn.example/demo.ttf")
```

</details>

#### puts resolved local font-face sources ahead of generic fallback candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val family = browser_font_face_family_value("Demo Serif, serif", "examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
val candidates = browser_font_candidates_for_family(family)
expect(browser_font_face_source_from_family_value(family)).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
expect(candidates[0]).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
expect(candidates[1]).to_equal(browser_chrome_compatible_normal_font_path())
```

</details>

#### keeps remote font-face sources out of renderer file candidates until fetched

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val family = browser_font_face_family_value("Remote Serif, serif", "https://cdn.example/font.ttf")
expect(family).to_equal("Remote Serif, serif")
expect(browser_font_candidates_for_family(family)[0]).to_equal(browser_chrome_compatible_normal_font_path())
```

</details>

#### maps remote font-face sources to deterministic cache paths without implicit download

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = "https://cdn.example/fonts/demo.woff2"
expect(browser_font_cache_dir()).to_equal("build/browser-font-cache")
expect(browser_font_face_cached_source_path(url)).to_equal("build/browser-font-cache/https___cdn_example_fonts_demo_woff2.woff2")

val css = "@font-face { font-family: Remote; src: url('https://cdn.example/fonts/demo.woff2') format('woff2'); }"
val result = ensure_browser_font_face_sources(css, false)
expect(result.attempted_download).to_equal(false)
expect(result.status).to_equal("remote_sources_missing")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- shared font renderer fallbacks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

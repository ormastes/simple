# Html Compat Specification

> <details>

<!-- sdn-diagram:id=html_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=html_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

html_compat_spec -> std
html_compat_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=html_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Compat Specification

## Scenarios

### wm_compare HTML Chromium compatibility manifest

#### baseline widget scene manifest

#### lists the fixed 320x240 widget and flex scenes

<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = build_catalog()
expect(catalog.len()).to_equal(60)
expect(_catalog_has("00_text_only")).to_equal(true)
expect(_catalog_has("01_inline_text")).to_equal(true)
expect(_catalog_has("02_block_boxes")).to_equal(true)
expect(_catalog_has("03_list")).to_equal(true)
expect(_catalog_has("04_button")).to_equal(true)
expect(_catalog_has("05_text_input")).to_equal(true)
expect(_catalog_has("06_card_panel")).to_equal(true)
expect(_catalog_has("07_scrollable_list")).to_equal(true)
expect(_catalog_has("10_colors")).to_equal(true)
expect(_catalog_has("11_font_size")).to_equal(true)
expect(_catalog_has("12_padding")).to_equal(true)
expect(_catalog_has("13_margin")).to_equal(true)
expect(_catalog_has("14_border")).to_equal(true)
expect(_catalog_has("15_background")).to_equal(true)
expect(_catalog_has("16_flex_row")).to_equal(true)
expect(_catalog_has("17_flex_col")).to_equal(true)
expect(_catalog_has("18_flex_grow_weights")).to_equal(true)
expect(_catalog_has("19_flex_shrink_weights")).to_equal(true)
expect(_catalog_has("20_flex_basis_override")).to_equal(true)
expect(_catalog_has("21_flex_wrap_basic")).to_equal(true)
expect(_catalog_has("22_flex_align_items_baseline")).to_equal(true)
expect(_catalog_has("23_flex_wrap_align_content_center")).to_equal(true)
expect(_catalog_has("24_flex_wrap_reverse_basic")).to_equal(true)
expect(_catalog_has("25_flex_justify_space_between")).to_equal(true)
expect(_catalog_has("26_flex_gap_basic")).to_equal(true)
expect(_catalog_has("27_absolute_position_basic")).to_equal(true)
expect(_catalog_has("28_display_contents_basic")).to_equal(true)
expect(_catalog_has("29_box_sizing_border_box")).to_equal(true)
expect(_catalog_has("30_min_max_width_basic")).to_equal(true)
expect(_catalog_has("31_flex_align_items_center")).to_equal(true)
expect(_catalog_has("32_flex_align_items_flex_end")).to_equal(true)
expect(_catalog_has("33_flex_justify_flex_end")).to_equal(true)
expect(_catalog_has("34_flex_justify_center")).to_equal(true)
expect(_catalog_has("35_flex_align_items_stretch")).to_equal(true)
expect(_catalog_has("36_flex_align_self_flex_end")).to_equal(true)
expect(_catalog_has("37_flex_gap_justify_center")).to_equal(true)
expect(_catalog_has("38_flex_gap_space_between")).to_equal(true)
expect(_catalog_has("39_flex_gap_flex_end")).to_equal(true)
expect(_catalog_has("40_flex_column_gap_justify_center")).to_equal(true)
expect(_catalog_has("41_flex_column_gap_space_between")).to_equal(true)
expect(_catalog_has("42_flex_column_gap_flex_end")).to_equal(true)
expect(_catalog_has("43_flex_column_align_items_center")).to_equal(true)
expect(_catalog_has("44_flex_column_align_items_flex_end")).to_equal(true)
expect(_catalog_has("45_flex_column_align_self_flex_end")).to_equal(true)
expect(_catalog_has("46_flex_column_align_items_stretch")).to_equal(true)
expect(_catalog_has("47_flex_column_align_self_center")).to_equal(true)
expect(_catalog_has("48_flex_column_align_self_stretch")).to_equal(true)
expect(_catalog_has("49_flex_column_justify_space_around")).to_equal(true)
expect(_catalog_has("50_flex_row_justify_space_around")).to_equal(true)
expect(_catalog_has("51_flex_row_justify_space_evenly")).to_equal(true)
expect(_catalog_has("52_flex_column_justify_space_evenly")).to_equal(true)
expect(_catalog_has("53_flex_wrap_align_content_flex_end")).to_equal(true)
expect(_catalog_has("54_flex_wrap_align_content_space_between")).to_equal(true)
expect(_catalog_has("55_flex_wrap_align_content_space_around")).to_equal(true)
expect(_catalog_has("56_flex_wrap_align_content_space_evenly")).to_equal(true)
expect(_catalog_has("57_flex_wrap_gap_basic")).to_equal(true)
expect(_catalog_has("58_flex_wrap_axis_gap_basic")).to_equal(true)
expect(_catalog_has("59_flex_column_axis_gap_basic")).to_equal(true)
expect(_catalog_has("60_flex_align_self_mixed_overrides")).to_equal(true)
expect(_catalog_has("61_flex_gap_space_around")).to_equal(true)
```

</details>

#### uses text-tolerant matching for antialiased text scenes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = build_catalog()
var strict = true
for fixture in catalog:
    if fixture.id == "00_text_only":
        strict = fixture.strict
expect(strict).to_equal(false)
```

</details>

#### marks Chrome edge-antialiased block boxes as diagnostic tolerant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = build_catalog()
var strict = true
for fixture in catalog:
    if fixture.id == "02_block_boxes":
        strict = fixture.strict
expect(strict).to_equal(false)
```

</details>

#### marks Chrome edge-antialiased list rows as diagnostic tolerant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = build_catalog()
var strict = true
for fixture in catalog:
    if fixture.id == "03_list":
        strict = fixture.strict
expect(strict).to_equal(false)
```

</details>

#### resolves scene HTML from the fixture tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "04_button",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val html = load_combined_html(fixture)
expect(html).to_contain("<button")
```

</details>

#### Chromium golden loading

#### loads checked-in Chromium PPMs at the canonical viewport

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "04_button",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val golden = load_chrome_golden(fixture, 320, 240)
expect(golden.success).to_equal(true)
expect(golden.pixels.len()).to_equal(320 * 240)
```

</details>

#### fails clearly when the viewport does not match the golden

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "04_button",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val golden = load_chrome_golden(fixture, 160, 120)
expect(golden.success).to_equal(false)
expect(golden.error).to_contain("viewport mismatch")
```

</details>

#### Simple child-process timeout options

#### defaults Simple source-B timeout to 20 seconds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_opts([])
expect(opts.simple_timeout_ms).to_equal(20000)
```

</details>

#### parses explicit Simple source-B timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_opts(["--simple-timeout-ms=3210"])
expect(opts.simple_timeout_ms).to_equal(3210)
```

</details>

#### bitwise pixel comparison

#### reports exact match for identical pixel buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_exact(
    [0xFF000000u32, 0xFFFFFFFFu32],
    [0xFF000000u32, 0xFFFFFFFFu32],
    2, 1
)
expect(result.different_pixels).to_equal(0)
expect(result.match_percentage).to_equal(10000)
expect(result.max_channel_diff).to_equal(0)
```

</details>

#### reports changed pixels and maximum channel drift

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_exact(
    [0xFF000000u32, 0xFFFFFFFFu32],
    [0xFF000000u32, 0xFF00FFFFu32],
    2, 1
)
expect(result.different_pixels).to_equal(1)
expect(result.match_percentage).to_equal(5000)
expect(result.max_channel_diff).to_equal(255)
```

</details>

#### does not report invalid dimensions as exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_exact([], [], 0, 1)
expect(result.different_pixels).to_be_greater_than(0)
expect(result.match_percentage).to_equal(0)
expect(result.max_channel_diff).to_equal(255)
```

</details>

#### does not report truncated equal buffers as exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_exact(
    [0xFF000000u32],
    [0xFF000000u32],
    2, 1
)
expect(result.different_pixels).to_equal(2)
expect(result.match_percentage).to_equal(0)
expect(result.max_channel_diff).to_equal(255)
```

</details>

#### does not report truncated equal buffers as perceptually complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compare_perceptual(
    [0xFF000000u32],
    [0xFF000000u32],
    2, 1, 16, true
)
expect(result.match_percentage).to_equal(0)
```

</details>

#### does not accept perceptual-only pixel matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "99_policy_probe",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val chrome = CaptureResult(
    pixels: [0xFF000000u32, 0xFFFFFFFFu32],
    width: 2, height: 1,
    backend_name: "chrome", success: true, error: ""
)
val simple = CaptureResult(
    pixels: [0xFF000000u32, 0xFFFEFFFFu32],
    width: 2, height: 1,
    backend_name: "simple", success: true, error: ""
)
val pair = compare_pair(fixture, chrome, simple, 2, 1)
expect(pair.exact).to_equal(false)
expect(pair.accepted).to_equal(false)
expect(pair.perceptual_pct_10000).to_be_greater_than(0)
```

</details>

#### does not accept captures with mismatched viewport metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "99_policy_probe",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val chrome = CaptureResult(
    pixels: [0xFF000000u32, 0xFFFFFFFFu32],
    width: 1, height: 2,
    backend_name: "chrome", success: true, error: ""
)
val simple = CaptureResult(
    pixels: [0xFF000000u32, 0xFFFFFFFFu32],
    width: 2, height: 1,
    backend_name: "simple", success: true, error: ""
)
val pair = compare_pair(fixture, chrome, simple, 2, 1)
expect(pair.exact).to_equal(false)
expect(pair.accepted).to_equal(false)
expect(pair.chrome_ok).to_equal(false)
expect(pair.chrome_error).to_contain("viewport metadata mismatch")
```

</details>

#### writes exact-only diagnostic policy into reports

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture = Fixture(
    id: "99_policy_probe",
    html_path: "test/fixtures/html_compat/04_button.html",
    css_path: "",
    strict: false
)
val capture = CaptureResult(
    pixels: [0xFF000000u32],
    width: 1, height: 1,
    backend_name: "probe", success: true, error: ""
)
val opts = HtmlCompatOpts(
    width: 1,
    height: 1,
    only: "",
    update_baseline: false,
    skip_simple: false,
    simple_timeout_ms: 1000,
    help: false
)
val pair = compare_pair(fixture, capture, capture, 1, 1)
expect(write_report(fixture, capture, capture, pair, opts)).to_equal(true)
val report = rt_file_read_text(report_sdn_path(fixture.id))
expect(report).to_contain("acceptance_policy: \"exact_pixels_required_perceptual_diagnostic_only\"")
expect(report).to_contain("acceptance_policy: (exact_required: true perceptual_diagnostic_only: true tolerance_acceptance_allowed: false)")
```

</details>

#### Chromium flex geometry evidence reports

#### records flex subpixel diagnostics without pixel tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/chrome_html_compat_geometry_flex_fraction_evidence_2026-06-11.md")
expect(report).to_contain("- status: pass")
expect(report).to_contain("- blur/tolerance used: false")
expect(report).to_contain("## Subpixel Diagnostics")
expect(report).to_contain("| `18_flex_grow_weights` | 2 | 0.328 | `grow_one,grow_two` |")
expect(report).to_contain("| `22_flex_align_items_baseline` | 2 | 0.328 | `baseline_big,baseline_small` |")
expect(report).to_contain("| `24_flex_wrap_reverse_basic` | pass | 0 |")
```

</details>

#### keeps Chrome geometry manifest evidence on exact structural comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrapper = rt_file_read_text("scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs")
val capture = rt_file_read_text("tools/chrome-live-bitmap/capture_html_argb.js")
val report = rt_file_read_text("doc/09_report/chrome_html_compat_geometry_manifest_evidence_2026-06-11.md")
expect(wrapper).to_contain("25_flex_justify_space_between")
expect(wrapper).to_contain("26_flex_gap_basic")
expect(wrapper).to_contain("27_absolute_position_basic")
expect(wrapper).to_contain("28_display_contents_basic")
expect(wrapper).to_contain("29_box_sizing_border_box")
expect(wrapper).to_contain("30_min_max_width_basic")
expect(wrapper).to_contain("31_flex_align_items_center")
expect(wrapper).to_contain("32_flex_align_items_flex_end")
expect(wrapper).to_contain("33_flex_justify_flex_end")
expect(wrapper).to_contain("34_flex_justify_center")
expect(wrapper).to_contain("35_flex_align_items_stretch")
expect(wrapper).to_contain("36_flex_align_self_flex_end")
expect(wrapper).to_contain("37_flex_gap_justify_center")
expect(wrapper).to_contain("38_flex_gap_space_between")
expect(wrapper).to_contain("39_flex_gap_flex_end")
expect(wrapper).to_contain("40_flex_column_gap_justify_center")
expect(wrapper).to_contain("41_flex_column_gap_space_between")
expect(wrapper).to_contain("42_flex_column_gap_flex_end")
expect(wrapper).to_contain("43_flex_column_align_items_center")
expect(wrapper).to_contain("44_flex_column_align_items_flex_end")
expect(wrapper).to_contain("45_flex_column_align_self_flex_end")
expect(wrapper).to_contain("46_flex_column_align_items_stretch")
expect(wrapper).to_contain("47_flex_column_align_self_center")
expect(wrapper).to_contain("48_flex_column_align_self_stretch")
expect(wrapper).to_contain("49_flex_column_justify_space_around")
expect(wrapper).to_contain("50_flex_row_justify_space_around")
expect(wrapper).to_contain("51_flex_row_justify_space_evenly")
expect(wrapper).to_contain("52_flex_column_justify_space_evenly")
expect(wrapper).to_contain("53_flex_wrap_align_content_flex_end")
expect(wrapper).to_contain("54_flex_wrap_align_content_space_between")
expect(wrapper).to_contain("55_flex_wrap_align_content_space_around")
expect(wrapper).to_contain("56_flex_wrap_align_content_space_evenly")
expect(wrapper).to_contain("57_flex_wrap_gap_basic")
expect(wrapper).to_contain("58_flex_wrap_axis_gap_basic")
expect(wrapper).to_contain("59_flex_column_axis_gap_basic")
expect(wrapper).to_contain("60_flex_align_self_mixed_overrides")
expect(wrapper).to_contain("61_flex_gap_space_around")
expect(wrapper).to_contain("CHROME_CAPTURE_GEOMETRY_OUTPUT")
expect(wrapper).to_contain("HTML_COMPAT_GEOMETRY_JSON=\"$geometry_json\"")
expect(wrapper).to_contain("src/app/wm_compare/html_compat_geometry_probe_cli.spl")
expect(wrapper).to_contain("\"$fixture\" \"$geometry_json\" \"$structural_sdn\" \"$WIDTH\" \"$HEIGHT\"")
expect(wrapper).to_contain("blur_or_tolerance_used=false")
expect(report).to_contain("- fixtures: 58")
expect(report).to_contain("- pass count: 58")
expect(report).to_contain("- fail count: 0")
expect(report).to_contain("- blur/tolerance used: false")
expect(report).to_contain("It does not use blur, downscaling, pixel tolerance, copied Chromium")
expect(capture).to_contain("--force-device-scale-factor=1")
expect(capture).to_contain("deviceScaleFactor: 1")
expect(capture).to_contain("blur_or_tolerance_used: false")
expect(_index_or_missing(wrapper, "HTML_COMPAT_GEOMETRY_JSON=\"$argb_json\"")).to_equal(-1)
expect(_index_or_missing(wrapper, "\"$fixture\" \"$argb_json\"")).to_equal(-1)
expect(_index_or_missing(wrapper, "mismatch_count -le")).to_equal(-1)
expect(_index_or_missing(wrapper, "mismatch_count <=")).to_equal(-1)
expect(_index_or_missing(wrapper, "pixelmatch")).to_equal(-1)
expect(_index_or_missing(wrapper, "perceptual")).to_equal(-1)
expect(_index_or_missing(wrapper, " -resize ")).to_equal(-1)
expect(_index_or_missing(wrapper, " -scale ")).to_equal(-1)
expect(_index_or_missing(wrapper, " -blur ")).to_equal(-1)
expect(_index_or_missing(wrapper, " -filter ")).to_equal(-1)
expect(_index_or_missing(capture, "require(\"sharp\")")).to_equal(-1)
expect(_index_or_missing(capture, "require(\"canvas\")")).to_equal(-1)
expect(_index_or_missing(capture, "OffscreenCanvas")).to_equal(-1)
expect(_index_or_missing(capture, "createElement(\"canvas\")")).to_equal(-1)
expect(_index_or_missing(capture, "pixelmatch")).to_equal(-1)
expect(_index_or_missing(capture, "threshold")).to_equal(-1)
expect(_index_or_missing(capture, "imageSmoothingEnabled")).to_equal(-1)
expect(_index_or_missing(capture, "drawImage(")).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/html_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare HTML Chromium compatibility manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

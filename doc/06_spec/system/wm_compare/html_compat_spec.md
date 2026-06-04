# Html Compat Specification

## Scenarios

### wm_compare HTML Chromium compatibility manifest

#### baseline widget scene manifest

#### lists the fixed 320x240 widget scenes

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val catalog = build_catalog()
expect(catalog.len()).to_equal(16)
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
```

</details>

#### uses text-tolerant matching for antialiased text scenes

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_opts([])
expect(opts.simple_timeout_ms).to_equal(20000)
```

</details>

#### parses explicit Simple source-B timeout

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/wm_compare/html_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_compare HTML Chromium compatibility manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


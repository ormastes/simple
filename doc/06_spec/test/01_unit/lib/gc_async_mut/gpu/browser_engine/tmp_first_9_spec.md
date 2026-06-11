# Tmp First 9 Specification

> <details>

<!-- sdn-diagram:id=tmp_first_9_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_first_9_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_first_9_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_first_9_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp First 9 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### renders inline background blocks without producing a blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 120px; height: 60px; background-color: #ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders style block CSS without hanging

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; } .card { width: 100px; height: 50px; background-color: #0000ff; }</style></head><body><div class='card'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders arbitrary non-fixture CSS through layout and paint instead of fill-only fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0; background-color:#ffffff'><div style='width:12px; height:4px; background-color:#2563eb'></div><div style='width:8px; height:4px; background-color:#16a34a'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

#### renders arbitrary non-fixture CSS text through the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { width: 32px; height: 18px; background-color: #e0f2fe; color: #dc2626; font-size: 16px; }</style></head><body><div class='label'>Hi</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFE0F2FEu32)).to_be_greater_than(0)
expect(_count_non_background(result.pixel_data, 0xFFE0F2FEu32)).to_be_greater_than(0)
```

</details>

#### applies later class rules over earlier ones in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies tag rules in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies class rules over tag rules in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### does not match class selector prefixes in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card-title { width: 12px; height: 8px; background-color: #2563eb; } .card { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies exact selectors from comma selector lists in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } section, .card { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_first_9_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

# Browser Renderer Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 123 | 123 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Specification

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

#### renders CSS linear-gradient background images as vertical pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-image: linear-gradient(#dc2626, #2563eb); }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[0]).to_equal(0xFFDC2626u32)
expect(result.pixel_data[9 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### uses ordered fractional quantization for small no-repeat gradient tiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 20px; height: 20px; background-color: #e5e7eb; background-image: linear-gradient(#e5e7eb, #cbd5e1); background-size: 20px 20px; background-repeat: no-repeat; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[0]).to_equal(0xFFE5E7EBu32)
expect(result.pixel_data[19 * TEST_WIDTH]).to_equal(0xFFCBD5E1u32)
expect(result.pixel_data[8 * TEST_WIDTH]).to_equal(0xFFDADFE7u32)
expect(result.pixel_data[1 + 8 * TEST_WIDTH]).to_equal(0xFFDADFE7u32)
expect(result.pixel_data[2 + 8 * TEST_WIDTH]).to_equal(0xFFDAE0E7u32)
expect(result.pixel_data[3 + 9 * TEST_WIDTH]).to_equal(0xFFD9DFE7u32)
expect(result.pixel_data[4 + 10 * TEST_WIDTH]).to_equal(0xFFD8DEE6u32)
```

</details>

#### clips gradient background images to background-size when repeat is disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; background-color: #16a34a; background-image: linear-gradient(#dc2626, #2563eb); background-size: 6px 6px; background-repeat: no-repeat; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[0]).to_equal(0xFFDC2626u32)
expect(result.pixel_data[5 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(result.pixel_data[6 * TEST_WIDTH]).to_equal(0xFF16A34Au32)
expect(result.pixel_data[6]).to_equal(0xFF16A34Au32)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 6, 6, 0xFF16A34Au32)).to_equal(36)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 6, 6, 6, 6, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### clips background-color to content-box when background-clip requests it

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val border_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; padding: 4px; border: 2px solid #dc2626; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val content_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; padding: 4px; border: 2px solid #dc2626; background-color: #2563eb; background-clip: content-box; }</style></head><body><div class='card'></div></body></html>"
val border_box = render_html_to_pixels_with_viewport(border_html, 40, 32).pixel_data
val content_box = render_html_to_pixels_with_viewport(content_html, 40, 32).pixel_data

expect(border_box[3 + 3 * 40]).to_equal(0xFF2563EBu32)
expect(content_box[3 + 3 * 40]).to_equal(WHITE_BG)
expect(content_box[7 + 7 * 40]).to_equal(0xFF2563EBu32)
expect(_count_color(content_box, 0xFF2563EBu32)).to_be_less_than(_count_color(border_box, 0xFF2563EBu32))
```

</details>

#### positions background images from content-box when background-origin requests it

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val padding_origin_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; padding: 4px; border: 2px solid #dc2626; background-color: #16a34a; background-image: linear-gradient(#2563eb, #f59e0b); background-size: 4px 4px; background-repeat: no-repeat; }</style></head><body><div class='card'></div></body></html>"
val content_origin_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; padding: 4px; border: 2px solid #dc2626; background-color: #16a34a; background-image: linear-gradient(#2563eb, #f59e0b); background-size: 4px 4px; background-repeat: no-repeat; background-origin: content-box; }</style></head><body><div class='card'></div></body></html>"
val padding_origin = render_html_to_pixels_with_viewport(padding_origin_html, 40, 32).pixel_data
val content_origin = render_html_to_pixels_with_viewport(content_origin_html, 40, 32).pixel_data

expect(padding_origin[2 + 2 * 40]).to_equal(0xFF2563EBu32)
expect(content_origin[2 + 2 * 40]).to_equal(0xFF16A34Au32)
expect(content_origin[6 + 6 * 40]).to_equal(0xFF2563EBu32)
expect(_pixels_equal(padding_origin, content_origin)).to_equal(false)
```

</details>

#### positions no-repeat gradient background images within the background color layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 12px; background-color: #16a34a; background-image: linear-gradient(#dc2626, #2563eb); background-size: 6px 6px; background-repeat: no-repeat; background-position: 3px 4px; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[0]).to_equal(0xFF16A34Au32)
expect(result.pixel_data[3 + 4 * TEST_WIDTH]).to_equal(0xFFDC2626u32)
expect(result.pixel_data[3 + 9 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(result.pixel_data[2 + 4 * TEST_WIDTH]).to_equal(0xFF16A34Au32)
expect(result.pixel_data[3 + 10 * TEST_WIDTH]).to_equal(0xFF16A34Au32)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 3, 4, 6, 6, 0xFF16A34Au32)).to_equal(36)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 3, 4, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### renders static CSS translate transforms as shifted painted pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 6px; height: 4px; background-color: #2563eb; transform: translate(10px, 6px); }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 0, 6, 4, WHITE_BG)).to_equal(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 10, 6, 6, 4, WHITE_BG)).to_equal(24)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(24)
```

</details>

#### renders absolute bottom offsets as bottom anchored painted pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .shell { position: relative; width: 20px; height: 20px; background-color: #ffffff; } .card { position: absolute; left: 2px; bottom: 3px; width: 6px; height: 4px; background-color: #16a34a; }</style></head><body><div class='shell'><div class='card'></div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 2, 0, 6, 4, WHITE_BG)).to_equal(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 2, 13, 6, 4, WHITE_BG)).to_equal(24)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(24)
```

</details>

#### renders side-specific border style none without painting disabled sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-color: #ffffff; border: 2px solid #dc2626; }</style></head><body><div class='card'></div></body></html>"
val left_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-color: #ffffff; border: 2px solid #dc2626; border-left-style: none; }</style></head><body><div class='card'></div></body></html>"
val top_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-color: #ffffff; border: 2px solid #dc2626; border-top-style: none; }</style></head><body><div class='card'></div></body></html>"
val right_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-color: #ffffff; border: 2px solid #dc2626; border-right-style: none; }</style></head><body><div class='card'></div></body></html>"
val bottom_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 10px; height: 10px; background-color: #ffffff; border: 2px solid #dc2626; border-bottom-style: none; }</style></head><body><div class='card'></div></body></html>"
val base_red = _count_color(render_html_to_pixels_with_viewport(base_html, TEST_WIDTH, TEST_HEIGHT).pixel_data, 0xFFDC2626u32)
val left_red = _count_color(render_html_to_pixels_with_viewport(left_html, TEST_WIDTH, TEST_HEIGHT).pixel_data, 0xFFDC2626u32)
val top_red = _count_color(render_html_to_pixels_with_viewport(top_html, TEST_WIDTH, TEST_HEIGHT).pixel_data, 0xFFDC2626u32)
val right_red = _count_color(render_html_to_pixels_with_viewport(right_html, TEST_WIDTH, TEST_HEIGHT).pixel_data, 0xFFDC2626u32)
val bottom_red = _count_color(render_html_to_pixels_with_viewport(bottom_html, TEST_WIDTH, TEST_HEIGHT).pixel_data, 0xFFDC2626u32)

expect(base_red).to_be_greater_than(left_red)
expect(base_red).to_be_greater_than(top_red)
expect(base_red).to_be_greater_than(right_red)
expect(base_red).to_be_greater_than(bottom_red)
```

</details>

#### renders CSS outline outside border box without affecting flow layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 8px; height: 6px; background-color: #ffffff; outline-width: 2px; outline-style: solid; outline-color: #7c3aed; } .next { width: 6px; height: 4px; background-color: #16a34a; }</style></head><body><div class='card'></div><div class='next'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
expect(_count_region_changed(result.pixel_data, TEST_WIDTH, 0, 14, 6, 4, WHITE_BG)).to_equal(24)
```

</details>

#### renders CSS outline-offset as an expanded outline gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 6px; width: 8px; height: 6px; background-color: #ffffff; outline-width: 1px; outline-style: solid; outline-color: #7c3aed; outline-offset: 3px; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(result.pixel_data[2 + 2 * TEST_WIDTH]).to_equal(0xFF7C3AEDu32)
expect(result.pixel_data[5 + 5 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(result.pixel_data[6 + 6 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### renders box-shadow behind the element background box

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 10px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val shadow_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 10px; background-color: #2563eb; box-shadow: 5px 4px #dc2626; }</style></head><body><div class='card'></div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val shadow = render_html_to_pixels_with_viewport(shadow_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_count_color(shadow, 0xFF2563EBu32)).to_equal(_count_color(plain, 0xFF2563EBu32))
expect(_count_color(shadow, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_pixels_equal(plain, shadow)).to_equal(false)
```

</details>

#### renders border-radius by clipping background corner pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val square_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 12px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val round_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 12px; background-color: #2563eb; border-radius: 6px; }</style></head><body><div class='card'></div></body></html>"
val square = render_html_to_pixels_with_viewport(square_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val rounded = render_html_to_pixels_with_viewport(round_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_count_color(rounded, 0xFF2563EBu32)).to_be_less_than(_count_color(square, 0xFF2563EBu32))
expect(rounded[4 + 4 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(rounded[10 + 8 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(_pixels_equal(square, rounded)).to_equal(false)
```

</details>

#### renders border corner radius longhands independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val square_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 12px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val corner_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 18px; height: 12px; background-color: #2563eb; border-top-left-radius: 6px; }</style></head><body><div class='card'></div></body></html>"
val square = render_html_to_pixels_with_viewport(square_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val corner = render_html_to_pixels_with_viewport(corner_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(corner[4 + 4 * TEST_WIDTH]).to_equal(WHITE_BG)
expect(corner[21 + 4 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(corner[4 + 15 * TEST_WIDTH]).to_equal(0xFF2563EBu32)
expect(_count_color(corner, 0xFF2563EBu32)).to_be_less_than(_count_color(square, 0xFF2563EBu32))
expect(_pixels_equal(square, corner)).to_equal(false)
```

</details>

#### does not render CSS outline when outline-style disables paint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { margin: 4px; width: 8px; height: 6px; background-color: #ffffff; outline: 2px solid #7c3aed; outline-style: none; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### renders text-transform uppercase with uppercase glyph pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lower_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>chrome baseline</div></body></html>"
val upper_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>CHROME BASELINE</div></body></html>"
val transform_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; text-transform: uppercase; }</style></head><body><div class='label'>chrome baseline</div></body></html>"
val lower = render_html_to_pixels_with_viewport(lower_html, 96, 32).pixel_data
val upper = render_html_to_pixels_with_viewport(upper_html, 96, 32).pixel_data
val transformed = render_html_to_pixels_with_viewport(transform_html, 96, 32).pixel_data

expect(_count_color(transformed, 0xFF111827u32)).to_be_greater_than(0)
expect(_pixels_equal(lower, transformed)).to_equal(false)
expect(_pixels_equal(upper, transformed)).to_equal(true)
```

</details>

#### renders text-decoration underline below text glyphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val underline_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; text-decoration: underline; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 96, 32).pixel_data
val underline = render_html_to_pixels_with_viewport(underline_html, 96, 32).pixel_data

expect(_count_color(underline, 0xFF111827u32)).to_be_greater_than(_count_color(plain, 0xFF111827u32))
expect(_pixels_equal(plain, underline)).to_equal(false)
```

</details>

#### renders text-decoration-color independently from text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #2563eb; font-size: 8px; text-decoration-line: underline; text-decoration-color: #dc2626; }</style></head><body><div class='label'>UNDERLINE</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, 96, 32).pixel_data

expect(_count_color(result, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### renders text-indent by shifting the first text line right

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>INDENT</div></body></html>"
val indent_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; text-indent: 12px; }</style></head><body><div class='label'>INDENT</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 96, 32).pixel_data
val indented = render_html_to_pixels_with_viewport(indent_html, 96, 32).pixel_data

expect(_count_color(indented, 0xFF111827u32)).to_equal(_count_color(plain, 0xFF111827u32))
expect(_count_region_changed(plain, 96, 0, 0, 12, 12, WHITE_BG)).to_be_greater_than(_count_region_changed(indented, 96, 0, 0, 12, 12, WHITE_BG))
expect(_pixels_equal(plain, indented)).to_equal(false)
```

</details>

#### renders letter-spacing by spreading glyph advances

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>SPACING</div></body></html>"
val spaced_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; letter-spacing: 2px; }</style></head><body><div class='label'>SPACING</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 128, 32).pixel_data
val spaced = render_html_to_pixels_with_viewport(spaced_html, 128, 32).pixel_data

expect(_count_color(spaced, 0xFF111827u32)).to_equal(_count_color(plain, 0xFF111827u32))
expect(_count_region_changed(spaced, 128, 32, 0, 48, 12, WHITE_BG)).to_be_greater_than(_count_region_changed(plain, 128, 32, 0, 48, 12, WHITE_BG))
expect(_pixels_equal(plain, spaced)).to_equal(false)
```

</details>

#### renders word-spacing by widening space advances

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>WORD GAP TEST</div></body></html>"
val spaced_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; word-spacing: 6px; }</style></head><body><div class='label'>WORD GAP TEST</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 160, 32).pixel_data
val spaced = render_html_to_pixels_with_viewport(spaced_html, 160, 32).pixel_data

expect(_count_color(spaced, 0xFF111827u32)).to_equal(_count_color(plain, 0xFF111827u32))
expect(_count_region_changed(spaced, 160, 45, 0, 60, 12, WHITE_BG)).to_be_greater_than(_count_region_changed(plain, 160, 45, 0, 60, 12, WHITE_BG))
expect(_pixels_equal(plain, spaced)).to_equal(false)
```

</details>

#### renders font-style italic with skewed glyph pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>ITALIC</div></body></html>"
val italic_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; font-style: italic; }</style></head><body><div class='label'>ITALIC</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 96, 32).pixel_data
val italic = render_html_to_pixels_with_viewport(italic_html, 96, 32).pixel_data

expect(_count_color(italic, 0xFF111827u32)).to_equal(_count_color(plain, 0xFF111827u32))
expect(_count_region_changed(italic, 96, 1, 0, 40, 8, WHITE_BG)).to_be_greater_than(0)
expect(_pixels_equal(plain, italic)).to_equal(false)
```

</details>

#### renders direction rtl by reversing simple text glyph order

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ltr_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>ABC</div></body></html>"
val reversed_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>CBA</div></body></html>"
val rtl_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; direction: rtl; }</style></head><body><div class='label'>ABC</div></body></html>"
val ltr = render_html_to_pixels_with_viewport(ltr_html, 96, 32).pixel_data
val reversed = render_html_to_pixels_with_viewport(reversed_html, 96, 32).pixel_data
val rtl = render_html_to_pixels_with_viewport(rtl_html, 96, 32).pixel_data

expect(_count_color(rtl, 0xFF111827u32)).to_equal(_count_color(reversed, 0xFF111827u32))
expect(_pixels_equal(ltr, rtl)).to_equal(false)
expect(_pixels_equal(reversed, rtl)).to_equal(true)
```

</details>

#### renders text-shadow behind foreground text glyphs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; }</style></head><body><div class='label'>SHADOW</div></body></html>"
val shadow_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; text-shadow: 4px 3px #dc2626; }</style></head><body><div class='label'>SHADOW</div></body></html>"
val plain = render_html_to_pixels_with_viewport(plain_html, 96, 32).pixel_data
val shadow = render_html_to_pixels_with_viewport(shadow_html, 96, 32).pixel_data

expect(_count_color(shadow, 0xFF111827u32)).to_equal(_count_color(plain, 0xFF111827u32))
expect(_count_color(shadow, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_pixels_equal(plain, shadow)).to_equal(false)
```

</details>

#### renders text-overflow ellipsis for clipped nowrap text

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clipped_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; width: 42px; overflow: hidden; white-space: nowrap; }</style></head><body><div class='label'>OVERFLOWINGTEXT</div></body></html>"
val ellipsis_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .label { color: #111827; font-size: 8px; width: 42px; overflow: hidden; white-space: nowrap; text-overflow: ellipsis; }</style></head><body><div class='label'>OVERFLOWINGTEXT</div></body></html>"
val clipped = render_html_to_pixels_with_viewport(clipped_html, 96, 32).pixel_data
val ellipsis = render_html_to_pixels_with_viewport(ellipsis_html, 96, 32).pixel_data

expect(_count_color(ellipsis, 0xFF111827u32)).to_be_greater_than(0)
expect(_count_color(ellipsis, 0xFF111827u32)).to_be_less_than(_count_color(clipped, 0xFF111827u32))
expect(_pixels_equal(clipped, ellipsis)).to_equal(false)
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

#### applies :is selector lists in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } :is(section, .card) { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies :where selector lists in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } :where(section, .card) { width: 12px; height: 8px; background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_be_greater_than(0)
```

</details>

#### applies tag qualified :is selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:is(.card, .panel) { width: 12px; height: 8px; background-color: #dc2626; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### applies :not selector lists in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_be_greater_than(0)
```

</details>

#### rejects :not selectors when an option matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.card, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_equal(0)
```

</details>

#### applies :has descendant selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### applies :has direct child selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### rejects :has direct child selectors for nested descendants

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><section><span class='badge'></span></section></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### rejects :has selectors when no descendant option matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge, strong) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='label'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_equal(0)
```

</details>

#### applies :empty selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### rejects :empty selectors when the fallback div has content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div>content</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_equal(0)
```

</details>

#### applies :first-child selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### rejects :first-child selectors for later fallback divs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### applies :last-child selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### rejects :last-child selectors for earlier fallback divs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_equal(0)
```

</details>

#### applies :only-child selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_be_greater_than(0)
```

</details>

#### rejects :only-child selectors when a sibling exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_equal(0)
```

</details>

#### applies :nth-child odd and even selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### rejects :nth-child odd selectors for even fallback nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### applies :nth-child an plus b selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(2n+1) { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div></div><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_be_greater_than(0)
```

</details>

#### rejects :nth-child an plus b selectors for non matching fallback nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(2n+1) { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div></div><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_equal(0)
```

</details>

#### applies simple rules nested inside CSS layer blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { .card { width: 12px; height: 8px; background-color: #0f766e; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### applies functional selectors nested inside CSS layer blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } @layer components { div:not(.disabled) { width: 12px; height: 8px; background-color: #be123c; } }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### normalizes simple CSS nesting before fallback selector scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = browser_renderer_normalize_style_rules(".card { width: 12px; height: 8px; &.primary { background-color: #7e22ce; } & span { color: #0f766e; } }")
val normalized_document_style = browser_renderer_normalize_style_rules("body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
val normalized_html = browser_renderer_normalize_style_blocks("<html><head><style>body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }</style></head><body><div class='card primary'></div></body></html>")

expect(normalized).to_contain(".card { width: 12px; height: 8px; }")
expect(normalized).to_contain(".card.primary { background-color: #7e22ce; }")
expect(normalized).to_contain(".card span { color: #0f766e; }")
expect(normalized_document_style).to_contain(".card.primary { width: 12px; height: 8px; background-color: #7e22ce; }")
expect(normalized_html).to_contain(".card.primary { width: 12px; height: 8px; background-color: #7e22ce; }")
expect(normalized_document_style.contains("&.primary")).to_equal(false)
expect(normalized_html.contains("&.primary")).to_equal(false)
```

</details>

#### applies simple CSS nesting with parent selector references

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }</style></head><body><div class='card primary'></div></body></html>"
val flat_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #7e22ce; }</style></head><body><div class='card primary'></div></body></html>"
val normalized_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { &.primary { width: 12px; height: 8px; background-color: #7e22ce; } }")
val normalized_rule_html = "<html><head><style>" + normalized_css + "</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(normalized_rule_html, TEST_WIDTH, TEST_HEIGHT)
val flat_result = render_html_to_pixels_with_viewport(flat_html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(flat_result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF7E22CEu32)).to_be_greater_than(0)
```

</details>

#### applies simple descendant rules from CSS nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#dc2626; } }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#16a34a; } }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#dc2626; } }")
val green_css = "body { margin: 0; background-color: #ffffff; } " + browser_renderer_normalize_style_rules(".card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; & span { color:#16a34a; } }")
val red_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + red_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport("<html><head><style>" + green_css + "</style></head><body><div class='card'><span>Hi</span></div></body></html>", TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### applies attribute presence selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### applies exact attribute value selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='active'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_be_greater_than(0)
```

</details>

#### applies exact quoted attribute value selectors containing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-label='primary action'] { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div data-label='primary action'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### rejects exact attribute value selectors with different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### applies attribute prefix selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF0F5E9Cu32)).to_be_greater_than(0)
```

</details>

#### applies attribute suffix selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF065F46u32)).to_be_greater_than(0)
```

</details>

#### rejects attribute suffix selectors without a matching suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF065F46u32)).to_equal(0)
```

</details>

#### applies attribute substring selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-tags*='beta'] { width: 12px; height: 8px; background-color: #9d174d; }</style></head><body><div data-tags='alpha-beta-release'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF9D174Du32)).to_be_greater_than(0)
```

</details>

#### applies attribute whitespace token selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-flags~='selected'] { width: 12px; height: 8px; background-color: #7c2d12; }</style></head><body><div data-flags='primary selected visible'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF7C2D12u32)).to_be_greater_than(0)
```

</details>

#### applies attribute dash match selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }</style></head><body><div lang='en-US'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF155E75u32)).to_be_greater_than(0)
```

</details>

#### rejects attribute dash match selectors without a boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[lang|='en'] { width: 12px; height: 8px; background-color: #155e75; }</style></head><body><div lang='english'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF155E75u32)).to_equal(0)
```

</details>

#### applies case insensitive attribute selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog' i] { width: 12px; height: 8px; background-color: #4338ca; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4338CAu32)).to_be_greater_than(0)
```

</details>

#### keeps attribute selectors case sensitive without the i flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog'] { width: 12px; height: 8px; background-color: #4338ca; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF4338CAu32)).to_equal(0)
```

</details>

#### applies explicit case sensitive attribute selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='Dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### rejects explicit case sensitive attribute selectors with different case

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-mode='dialog' s] { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div data-mode='Dialog'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### applies tag class compound selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div.card { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies tag class compound selectors over bare class selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div.card { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### applies multi class selectors in fallback pixels regardless of class order

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='primary card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### applies multi class selectors over bare class selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card.primary { width: 12px; height: 8px; background-color: #2563eb; } .card { background-color: #16a34a; }</style></head><body><div class='card primary'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF16A34Au32)).to_equal(0)
```

</details>

#### applies id rules over class rules in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 12px; height: 8px; background-color: #2563eb; } #hero { background-color: #dc2626; }</style></head><body><div id='hero' class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### applies tag id compound selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div#hero { width: 12px; height: 8px; background-color: #dc2626; }</style></head><body><div id='hero'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

#### applies tag id compound selectors over bare id selectors in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div#hero { width: 12px; height: 8px; background-color: #dc2626; } #hero { background-color: #2563eb; }</style></head><body><div id='hero'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
expect(_count_color(result.pixel_data, 0xFF2563EBu32)).to_equal(0)
```

</details>

#### renders simple nested span text in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #fef3c7; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)

expect(_count_color(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
expect(_count_non_background(result.pixel_data, 0xFFFEF3C7u32)).to_be_greater_than(0)
```

</details>

#### uses nested span style when rendering fallback text pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#dc2626'>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; }</style></head><body><div class='card'><span style='color:#16a34a'>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor descendant span style when rendering fallback text pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor id descendant span style when rendering fallback text pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#dc2626; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } #hero { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } #hero span { color:#16a34a; }</style></head><body><div id='hero'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### uses ancestor child span style when rendering fallback text pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#dc2626; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val green_html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .card { width: 32px; height: 18px; background-color: #ffffff; color: #111827; font-size: 16px; } .card > span { color:#16a34a; }</style></head><body><div class='card'><span>Hi</span></div></body></html>"
val red_pixels = render_html_to_pixels_with_viewport(red_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green_pixels = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data

expect(_sum_red(red_pixels)).to_be_greater_than(_sum_red(green_pixels))
expect(_sum_green(green_pixels)).to_be_greater_than(_sum_green(red_pixels))
```

</details>

#### paints inline background shorthand fallback colors after url tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### paints style block background shorthand fallback colors after url tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### resolves background-color currentColor from the computed text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; color: #123456; background-color: currentColor'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF123456u32)).to_equal(true)
```

</details>

#### resolves background shorthand currentColor from the computed text color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; color: #345678; background: currentColor no-repeat'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF345678u32)).to_equal(true)
```

</details>

#### resolves inline currentColor backgrounds even when color is declared later

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: currentColor; color: #456789'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF456789u32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds from rule color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; color: #56789a; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF56789Au32)).to_equal(true)
```

</details>

#### resolves style block currentColor backgrounds after later matched color rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background-color: currentColor; } .card { color: #6789ab; }</style></head><body><div class='card'></div></body></html>"
expect(_scene_has_fill_color(html, 0xFF6789ABu32)).to_equal(true)
```

</details>

#### resolves CSS custom properties from style blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blue_html = "<html><head><style>:root { --theme-panel: #0000ff; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val green_html = "<html><head><style>:root { --theme-panel: #00ff00; } body { margin: 0; background-color: #ffffff; } .card { width: 100px; height: 50px; background-color: var(--theme-panel); }</style></head><body><div class='card'></div></body></html>"
val blue = render_html_to_pixels_with_viewport(blue_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val green = render_html_to_pixels_with_viewport(green_html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_pixel_signature(blue) != _pixel_signature(green)).to_equal(true)
```

</details>

#### renders the glass style body fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #101820; color: #f3f4f6; } .panel { width: 120px; height: 70px; background-color: #1f2937; }</style></head><body><div class='panel'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(pixels.len()).to_equal(TEST_WIDTH * TEST_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### is deterministic for repeated renders of the same HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #22aa44'></div></body></html>"
val first = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val second = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
expect(_pixel_signature(first)).to_equal(_pixel_signature(second))
```

</details>

#### uses the same pixels as an explicit Engine2D software renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #2050a0'></div><span style='color:#ffffff'>Hi</span></body></html>"
val default_renderer = BrowserRenderer.create(TEST_WIDTH, TEST_HEIGHT)
val software_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val default_pixels = default_renderer.render_html_to_pixels(html).pixel_data
val software_pixels = software_renderer.render_html_to_pixels(html).pixel_data
expect(default_renderer.engine.?).to_equal(false)
expect(software_renderer.engine.?).to_equal(true)
expect(default_renderer.backend_name()).to_equal("software")
expect(software_renderer.backend_name()).to_equal("software")
expect(_pixels_equal(default_pixels, software_pixels)).to_equal(true)
```

</details>

#### reports deterministic software for unknown backend fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "not-a-backend")
expect(renderer.engine.?).to_equal(false)
expect(renderer.backend_name()).to_equal("software")
```

</details>

#### module pixel helper matches explicit Engine2D software rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 110px; height: 30px; background-color: #aa2244'></div></body></html>"
val helper_pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val renderer_pixels = renderer.render_html_to_pixels(html).pixel_data
expect(_pixels_equal(helper_pixels, renderer_pixels)).to_equal(true)
```

</details>

#### renders famous-site corpus block at Chrome default body margin

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 120px; height: 40px; background-color: #2563eb'>Google search deterministic compatibility fixture</div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 160, 120).pixel_data
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(_count_region_changed(pixels, 160, 20, 19, 92, 18, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 8, 48, 120, 36, 0xFFFFFFFFu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 128, 8, 32, 40, 0xFFFFFFFFu32)).to_equal(0)
```

</details>

#### Engine2D bridge keeps explicit backend rendering available

- bridge renderer render html to pixels
- explicit renderer render html to pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 70px; height: 24px; background-color: #4488cc'></div></body></html>"
val bridge_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
expect(bridge_renderer.engine.?).to_equal(true)
expect(explicit_renderer.engine.?).to_equal(true)
expect(_pixels_equal(
    bridge_renderer.render_html_to_pixels(html).pixel_data,
    explicit_renderer.render_html_to_pixels(html).pixel_data
)).to_equal(true)
```

</details>

#### Engine2D GPU bridge requests Metal while preserving CPU parity fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val gpu_renderer = create_gpu_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val cpu_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "cpu")
val gpu_pixels = gpu_renderer.render_html_to_pixels(html).pixel_data
val cpu_pixels = cpu_renderer.render_html_to_pixels(html).pixel_data
expect(gpu_renderer.backend_name()).to_equal("metal")
expect(cpu_renderer.backend_name()).to_equal("cpu")
expect(_count_color(gpu_pixels, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(gpu_pixels, cpu_pixels)).to_equal(true)
```

</details>

#### renders CSS background fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS color fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("10_colors"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[8 + 8 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[8 + 28 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[8 + 48 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS padding fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("12_padding"), 40, 90).pixel_data
expect(pixels.len()).to_equal(40 * 90)
expect(pixels[16 + 16 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 50 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 78 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS margin fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("13_margin"), 40, 95).pixel_data
expect(pixels.len()).to_equal(40 * 95)
expect(pixels[14 + 14 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 52 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 82 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS border fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("14_border"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[4 + 4 * 40]).to_equal(0xFF000000u32)
expect(pixels[15 + 18 * 40]).to_equal(0xFF003366u32)
expect(pixels[24 + 61 * 40]).to_equal(0xFF006600u32)
```

</details>

#### renders CSS flex row fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("16_flex_row"), 125, 70).pixel_data
expect(pixels.len()).to_equal(125 * 70)
expect(pixels[121 + 61 * 125]).to_equal(0xFF93C5FDu32)
expect(pixels[27 + 61 * 125]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS flex column fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("17_flex_col"), 40, 100).pixel_data
expect(pixels.len()).to_equal(40 * 100)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[27 + 95 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### parses rgb() background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(37, 99, 235)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF2563EBu32)
```

</details>

#### parses modern space-separated rgb() background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(5 150 105)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### composites rgba() background-color over the white page in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF808080u32)
```

</details>

#### parses shorthand hex background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### composites shorthand hex alpha background-color over the white page in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0008'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF777777u32)
```

</details>

#### parses named CSS background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### composites transparent background-color to the white page in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: transparent'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses hsl() background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF008000u32)
```

</details>

#### parses color-first background shorthand in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rebeccapurple no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### parses function color background shorthand before trailing tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### parses fallback color after url() in background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background shorthand override earlier background-color in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background-color override earlier background shorthand in fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 123 |
| Active scenarios | 123 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
